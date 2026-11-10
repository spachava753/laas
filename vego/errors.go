package vego

import (
	"go/ast"
	"go/token"
	"go/types"
	"maps"
	"math/big"
	"slices"

	"github.com/spachava753/laas/vego/internal/logic"
	"github.com/spachava753/laas/vego/internal/solver"
	"golang.org/x/tools/go/types/typeutil"
)

// findSentinels records the package-level error variables that are known to
// be non-nil: those initialised with errors.New or fmt.Errorf and never
// assigned or addressed anywhere in the package. For an exported variable
// this relies on other packages not assigning to it.
func (pv *pkgVerifier) findSentinels() {
	pv.sentinels = map[*types.Var]bool{}
	for _, file := range pv.pass.Files {
		for _, decl := range file.Decls {
			gen, ok := decl.(*ast.GenDecl)
			if !ok || gen.Tok != token.VAR {
				continue
			}
			for _, spec := range gen.Specs {
				spec := spec.(*ast.ValueSpec)
				for i, name := range spec.Names {
					if len(spec.Values) != len(spec.Names) {
						break
					}
					call, isCall := ast.Unparen(spec.Values[i]).(*ast.CallExpr)
					variable, _ := pv.info.Defs[name].(*types.Var)
					if isCall && variable != nil && errorConstructor(typeutil.StaticCallee(pv.info, call)) {
						pv.sentinels[variable] = true
					}
				}
			}
		}
	}
	changed := func(e ast.Expr) {
		if id, ok := ast.Unparen(e).(*ast.Ident); ok {
			if variable, ok := pv.info.Uses[id].(*types.Var); ok {
				delete(pv.sentinels, variable)
			}
		}
	}
	for _, file := range pv.pass.Files {
		ast.Inspect(file, func(n ast.Node) bool {
			switch n := n.(type) {
			case *ast.AssignStmt:
				for _, lhs := range n.Lhs {
					changed(lhs)
				}
			case *ast.UnaryExpr:
				if n.Op == token.AND {
					changed(n.X)
				}
			case *ast.RangeStmt:
				if n.Key != nil {
					changed(n.Key)
				}
				if n.Value != nil {
					changed(n.Value)
				}
			}
			return true
		})
	}
}

// outcome is what verifying a function established about its failure,
// beyond the diagnostics it produced.
type outcome struct {
	// complete is set when verification ran to the end; the rest is only
	// meaningful then, and only for functions that return an error.
	complete bool
	// forces is set when the contract makes the function succeed for some
	// input.
	forces bool
	// outside is set when execution reached a call without a contract that
	// returns an error; reached holds the verified callees returning an
	// error that it reached.
	outside bool
	reached map[*funcInfo]bool
}

// verified verifies a function once and records the outcome.
func (pv *pkgVerifier) verified(fn *funcInfo) {
	if _, done := pv.outcomes[fn]; done {
		return
	}
	result := &outcome{}
	pv.outcomes[fn] = result
	pv.current = fn
	defer func() { pv.current = nil }()
	pv.run(fn, func(v *fnVerifier) {
		v.verify()
		if len(errorResults(fn)) > 0 {
			result.forces = v.forcesSuccess()
		}
		result.outside, result.reached, result.complete = v.outside, v.reached, true
	})
}

// reportAlwaysFailing rejects every contract that its function could meet
// by failing on every call. A postcondition of the form "err = nil -> ..."
// alone says what success looks like but never that success happens.
//
// A function is excused when it cannot promise success: its contract forces
// none, and it reaches a call whose failure no contract predicts, either
// directly or through a verified callee that is itself excused. The excused
// functions are the least fixed point of that rule, so a cycle of functions
// that only call each other excuses nobody, and the order of declarations
// does not matter.
func (pv *pkgVerifier) reportAlwaysFailing() map[*funcInfo]bool {
	excused := map[*funcInfo]bool{}
	candidate := func(fn *funcInfo) bool {
		result := pv.outcomes[fn]
		return result != nil && result.complete && len(errorResults(fn)) > 0 && !result.forces
	}
	for changed := true; changed; {
		changed = false
		for _, fn := range pv.order {
			if !candidate(fn) || excused[fn] {
				continue
			}
			through := slices.ContainsFunc(slices.Collect(maps.Keys(pv.outcomes[fn].reached)), func(callee *funcInfo) bool {
				return pv.outcomes[fn].reached[callee] && excused[callee]
			})
			if pv.outcomes[fn].outside || through {
				excused[fn], changed = true, true
			}
		}
	}
	for _, fn := range pv.order {
		if candidate(fn) && !excused[fn] {
			fn.failed = true
			pv.report(fn.decl.Name.Pos(), "the contract of %s would also be met by a function that always returns an error; "+
				"state when it succeeds with a clause such as \"condition -> err = nil\", "+
				"where the condition is about the inputs and some input satisfies it", fn.obj.Name())
		}
	}
	return excused
}

// trustForces reports whether a trusted contract forces success for some
// input. One that does not is a source of unpredictable failure: nothing
// says when the function succeeds.
func (pv *pkgVerifier) trustForces(fn *funcInfo) bool {
	if fn.forces != nil {
		return *fn.forces
	}
	forces := false
	fn.forces = &forces
	supported := func(t types.Type) bool {
		_, ok := sortOf(t)
		return ok
	}
	if slices.ContainsFunc(fn.params, func(p *types.Var) bool { return !supported(p.Type()) }) ||
		slices.ContainsFunc(fn.results, func(r *types.Var) bool { return !supported(r.Type()) }) {
		return false
	}
	pv.run(fn, func(v *fnVerifier) { forces = v.forcesSuccess() })
	if use := pv.usage.Entries[fn.trust.key]; use != nil {
		use.Unpredictable = !forces
	}
	return forces
}

// errorResults returns the indices of the results of type error.
func errorResults(fn *funcInfo) []int {
	var indices []int
	for i, result := range fn.results {
		if sort, ok := sortOf(result.Type()); ok && sort == logic.Err {
			indices = append(indices, i)
		}
	}
	return indices
}

// successConditions collects the conditions under which a postcondition
// forces the given error to be nil. It understands the shapes such clauses
// take: "err = nil" itself, a conjunction containing it, "C -> ...",
// "... <-> C", and a disjunction containing it.
func successConditions(post, forced *logic.Term) []*logic.Term {
	if post.Op == logic.OpIsNil && post.Args[0] == forced {
		return []*logic.Term{logic.True()}
	}
	var conditions []*logic.Term
	under := func(premise, rest *logic.Term) {
		for _, condition := range successConditions(rest, forced) {
			conditions = append(conditions, logic.And(premise, condition))
		}
	}
	switch post.Op {
	case logic.OpAnd:
		for _, arg := range post.Args {
			conditions = append(conditions, successConditions(arg, forced)...)
		}
	case logic.OpImplies:
		under(post.Args[0], post.Args[1])
	case logic.OpIff:
		under(post.Args[1], post.Args[0])
		under(post.Args[0], post.Args[1])
	case logic.OpOr:
		for i, arg := range post.Args {
			var others []*logic.Term
			for j, other := range post.Args {
				if i != j {
					others = append(others, logic.Not(other))
				}
			}
			under(logic.And(others...), arg)
		}
	}
	return conditions
}

// mentions reports whether a term contains one of the given constants.
func mentions(t *logic.Term, constants map[*logic.Term]bool) bool {
	if constants[t] {
		return true
	}
	for _, arg := range t.Args {
		if mentions(arg, constants) {
			return true
		}
	}
	return false
}

// successClauses resolves the contract for the given argument values. It
// returns the facts the precondition and the parameter types give about
// them and, for each error result, the conditions over the inputs alone
// under which the postcondition forces that error to be nil.
func (v *fnVerifier) successClauses(args map[*types.Var]*logic.Term) (pre []*logic.Term, conditions [][]*logic.Term) {
	fn := v.fn
	outputs := map[*logic.Term]bool{}
	results := make([]*logic.Term, len(fn.results))
	for i, result := range fn.results {
		sort, _ := sortOf(result.Type())
		results[i] = v.fresh("out", sort)
		outputs[results[i]] = true
	}
	post := map[*types.Var]*logic.Term{}
	for _, param := range fn.params {
		pre = append(pre, v.typeFact(args[param], param.Type()))
		post[param] = args[param]
		if isSlice(param.Type()) {
			post[param] = v.fresh("out", post[param].Sort)
			outputs[post[param]] = true
		}
	}
	for _, c := range fn.requires {
		pre = append(pre, v.formula(c, c.node, &contractEnv{pv: v.pkgVerifier, fn: fn, args: args}))
	}
	env := &contractEnv{pv: v.pkgVerifier, fn: fn, args: args, post: post, results: results}
	conditions = make([][]*logic.Term, len(errorResults(fn)))
	for _, c := range fn.ensures {
		clause := v.formula(c, c.node, env)
		for n, index := range errorResults(fn) {
			for _, condition := range successConditions(clause, results[index]) {
				if !mentions(condition, outputs) {
					conditions[n] = append(conditions[n], condition)
				}
			}
		}
	}
	return pre, conditions
}

// maxWitnesses bounds the inputs tried when looking for one on which a
// contract forces success.
const maxWitnesses = 3000

// forcesSuccess reports whether the contract makes the function succeed for
// some input: for every error result there is a clause "C -> err = nil"
// whose condition C speaks only about the inputs, and a concrete input that
// provably satisfies the precondition and C. Without such a clause and
// witness, an implementation that fails on every call may well satisfy the
// contract, whatever else the contract demands.
//
// The witness is searched among small inputs built from 0, 1, -1 and the
// numbers the contract mentions. Finding none is reported, even though a
// witness outside that search may exist: the contract must then be stated so
// that its success condition is plainly satisfiable.
func (v *fnVerifier) forcesSuccess() bool {
	v.enter()
	pre, conditions := v.successClauses(v.entry)
	for _, group := range conditions {
		if len(group) == 0 {
			return false
		}
	}
	opts := solver.Options{Preds: v.res.Preds, MaxSteps: v.maxSteps}
	forced := make([]bool, len(conditions))
	v.someInput(slices.Concat(append(conditions, pre)...), func(args map[*types.Var]*logic.Term) bool {
		facts, candidates := v.successClauses(args)
		for result, group := range candidates {
			forced[result] = forced[result] || slices.ContainsFunc(group, func(condition *logic.Term) bool {
				return solver.Prove(nil, logic.And(append(facts, condition)...), opts) == solver.Proved
			})
		}
		return !slices.Contains(forced, false)
	})
	return !slices.Contains(forced, false)
}

// canReach reports whether there is evidence that execution can arrive at
// the current point, given the facts that hold on the path to it. A path
// that is provably impossible cannot. Beyond that, the facts that speak
// about the inputs alone must be satisfied together by some concrete input;
// failing to refute them is not enough. Facts that depend on values the
// verifier treats as unknown, such as the result of an earlier call or the
// state after a loop, have no such witness and are taken as possible unless
// refuted, so this is an over-approximation for such paths.
func (v *fnVerifier) canReach(path []*logic.Term) bool {
	opts := solver.Options{Preds: v.res.Preds, MaxSteps: v.maxSteps}
	if solver.Prove(path, logic.False(), opts) == solver.Proved {
		return false
	}
	inputs := map[*logic.Term]bool{logic.NilErr(): true}
	for _, entry := range v.entry {
		inputs[entry] = true
	}
	var inputsOnly func(t *logic.Term) bool
	inputsOnly = func(t *logic.Term) bool {
		if t.Op == logic.OpConst && !inputs[t] {
			return false
		}
		return !slices.ContainsFunc(t.Args, func(arg *logic.Term) bool { return !inputsOnly(arg) })
	}
	// What must hold on the path is split into its necessary parts, so that
	// a condition on the inputs is found even inside a conjunction with
	// something unknown. Those parts must be proved for a concrete input,
	// and under the same input the path as a whole must not be refutable.
	var required []*logic.Term
	for _, fact := range path {
		for _, part := range necessary(fact) {
			if inputsOnly(part) {
				required = append(required, part)
			}
		}
	}
	return v.someInput(path, func(args map[*types.Var]*logic.Term) bool {
		var chosen []*logic.Term
		for param, value := range args {
			switch entry := v.entry[param]; {
			case value == entry:
			case entry.Sort.IsSeq():
				chosen = append(chosen, logic.SeqEq(entry, value, logic.Bound(v.fresh("k#", logic.Int).Name, logic.Int)))
			default:
				chosen = append(chosen, logic.Eq(entry, value))
			}
		}
		return solver.Prove(chosen, logic.And(required...), opts) == solver.Proved &&
			solver.Prove(append(chosen, path...), logic.False(), opts) != solver.Proved
	})
}

// necessary splits a formula into formulas that must each hold whenever it
// does: the conjuncts of a conjunction, and what the negation of a
// disjunction or of an implication entails.
func necessary(t *logic.Term) []*logic.Term {
	var parts []*logic.Term
	switch {
	case t.Op == logic.OpAnd:
		for _, arg := range t.Args {
			parts = append(parts, necessary(arg)...)
		}
	case t.Op == logic.OpNot && t.Args[0].Op == logic.OpOr:
		for _, arg := range t.Args[0].Args {
			parts = append(parts, necessary(logic.Not(arg))...)
		}
	case t.Op == logic.OpNot && t.Args[0].Op == logic.OpImplies:
		parts = append(necessary(t.Args[0].Args[0]), necessary(logic.Not(t.Args[0].Args[1]))...)
	default:
		parts = []*logic.Term{t}
	}
	return parts
}

// someInput tries small concrete inputs until one is accepted, and reports
// whether one was. The inputs are built from 0, 1, -1, 2, 3 and the numbers
// that occur in the given terms, which is where a witness for a condition
// over those terms is most likely to be found.
func (v *fnVerifier) someInput(terms []*logic.Term, accept func(args map[*types.Var]*logic.Term) bool) bool {
	numbers := []*big.Int{big.NewInt(0), big.NewInt(1), big.NewInt(-1), big.NewInt(2), big.NewInt(3)}
	var harvest func(t *logic.Term)
	harvest = func(t *logic.Term) {
		if t.Op == logic.OpIntLit && t.Value().IsInt64() && len(numbers) < 12 {
			for _, delta := range []int64{0, 1, -1} {
				numbers = append(numbers, new(big.Int).Add(t.Value(), big.NewInt(delta)))
			}
		}
		for _, arg := range t.Args {
			harvest(arg)
		}
	}
	for _, t := range terms {
		harvest(t)
	}
	params := v.fn.params
	choices := make([][]*logic.Term, len(params))
	total := 1
	for i, param := range params {
		choices[i] = v.sampleValues(param, numbers)
		total = min(total*len(choices[i]), maxWitnesses)
	}
	for n := range total {
		args := map[*types.Var]*logic.Term{}
		rest := n
		for i, param := range params {
			args[param] = choices[i][rest%len(choices[i])]
			rest /= len(choices[i])
		}
		if accept(args) {
			return true
		}
	}
	return false
}

// sampleValues lists concrete values of a parameter's type to try as part of
// a witness: the given numbers that fit an integer type, both booleans, and
// short sequences holding one repeated value. A float or an error has no
// concrete values in the logic and stays symbolic.
func (v *fnVerifier) sampleValues(param *types.Var, numbers []*big.Int) []*logic.Term {
	fitting := func(t types.Type) []*logic.Term {
		var values []*logic.Term
		lo, hi, _ := v.intRange(t)
		for _, number := range numbers {
			if lo != nil && number.Cmp(lo) >= 0 && number.Cmp(hi) <= 0 {
				values = append(values, logic.BigLit(number))
			}
		}
		return values
	}
	entry := v.entry[param]
	switch {
	case entry.Sort == logic.Int:
		return fitting(param.Type())
	case entry.Sort == logic.Bool:
		return []*logic.Term{logic.False(), logic.True()}
	case !entry.Sort.IsSeq():
		return []*logic.Term{entry}
	}
	elements := []*logic.Term{zero(entry.Sort.Elem())}
	switch {
	case entry.Sort == logic.BoolSeq:
		elements = append(elements, logic.True())
	case isString(param.Type()):
		elements = fitting(types.Typ[types.Uint8])
	case entry.Sort == logic.IntSeq:
		elements = fitting(param.Type().Underlying().(*types.Slice).Elem())
	}
	var values []*logic.Term
	for _, length := range fitting(types.Typ[types.Int]) {
		if length.Value().Sign() < 0 || length.Value().Cmp(big.NewInt(64)) > 0 {
			continue
		}
		for _, element := range elements[:min(len(elements), 3)] {
			values = append(values, logic.Fill(length, element))
		}
	}
	return values
}
