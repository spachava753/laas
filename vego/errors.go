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
	// The contract is examined on its own; parts of the signature of types
	// vego does not model take no part in it.
	pv.run(fn, func(v *fnVerifier) {
		v.lenient = true
		forces = v.forcesSuccess()
	})
	if fn.use != nil && len(errorResults(fn)) > 0 {
		fn.use.Unpredictable = !forces
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

// contractInstance resolves the contract for the given argument values. It
// returns the facts that the precondition and the parameter types give
// about them; everything that then holds of the outputs of any function
// meeting the contract, namely what their types and the call guarantee and
// the postcondition; and the terms standing for the error results.
func (v *fnVerifier) contractInstance(args map[*types.Var]*logic.Term) (pre, post, failures []*logic.Term) {
	fn := v.fn
	results := make([]*logic.Term, len(fn.results))
	final := map[*types.Var]*logic.Term{}
	for _, param := range fn.params {
		if args[param] == nil {
			continue
		}
		pre = append(pre, v.typeFact(args[param], param.Type()))
		final[param] = args[param]
		// Only a slice the function may write has contents of its own
		// afterwards, and even then its length is the caller's.
		if isSlice(param.Type()) && v.mutates(fn, param) {
			final[param] = v.fresh("out", final[param].Sort)
			post = append(post, v.valueFacts(final[param], param.Type()),
				logic.Eq(logic.Len(final[param]), logic.Len(args[param])))
		}
	}
	for i, result := range fn.results {
		if sort, ok := sortOf(result.Type()); ok {
			results[i] = v.fresh("out", sort)
			post = append(post, v.valueFacts(results[i], result.Type()))
		}
	}
	for _, c := range fn.requires {
		pre = append(pre, v.formula(c, c.node, &contractEnv{pv: v.pkgVerifier, fn: fn, args: args}))
	}
	env := &contractEnv{pv: v.pkgVerifier, fn: fn, args: args, post: final, results: results}
	for _, c := range fn.ensures {
		// A clause about a result that has no value in the logic says
		// nothing here.
		post = append(post, v.calleeFormula(c, env))
	}
	for _, index := range errorResults(fn) {
		failures = append(failures, results[index])
	}
	return pre, slices.Concat(pre, post), failures
}

// maxWitnesses bounds the inputs tried when looking for one on which a
// contract forces success.
const maxWitnesses = 3000

// forcesSuccess reports whether the contract makes the function succeed for
// some input: there is a concrete input that provably satisfies the
// precondition and for which every well-typed outcome that meets the
// postcondition has a nil error. Without such an input, an implementation
// that fails on every call may well satisfy the contract, whatever else the
// contract demands.
//
// The witness is searched among small inputs built from 0, 1, -1 and the
// numbers and strings the contract mentions. Finding none is reported, even
// though a witness outside that search may exist: the contract must then be
// stated so that its success condition is plainly satisfiable.
func (v *fnVerifier) forcesSuccess() bool {
	v.enter()
	_, mentioned, failures := v.contractInstance(v.entry)
	opts := solver.Options{Preds: v.res.Preds, MaxSteps: v.maxSteps}
	forced := make([]bool, len(failures))
	v.someInput(mentioned, func(args map[*types.Var]*logic.Term) bool {
		// The sample error is the one sample that is not a literal; all
		// that is known of it is that it is not nil.
		known := []*logic.Term{logic.Not(logic.IsNil(someError))}
		pre, post, failures := v.contractInstance(args)
		if solver.Prove(known, logic.And(pre...), opts) != solver.Proved {
			return false
		}
		for i, failure := range failures {
			forced[i] = forced[i] || solver.Prove(append(known, post...), logic.IsNil(failure), opts) == solver.Proved
		}
		return !slices.Contains(forced, false)
	})
	return !slices.Contains(forced, false)
}

// someError is the sample value for an error that is not nil.
var someError = logic.Const("some error", logic.Err)

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
			case value == entry || entry == nil:
			case entry.Sort.IsSeq():
				chosen = append(chosen, logic.SeqEq(entry, value, logic.Bound(v.fresh("k#", logic.Int).Name, logic.Int)))
			case entry.Sort == logic.Err:
				// All that is known of an error is whether it is nil.
				nilness := logic.IsNil(entry)
				if value == someError {
					nilness = logic.Not(nilness)
				}
				chosen = append(chosen, nilness)
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
	// A string or slice literal is a chain of appended elements.
	var literals []*logic.Term
	var collect func(t *logic.Term)
	collect = func(t *logic.Term) {
		if t.Op == logic.OpPush && len(literals) < 8 {
			literals = append(literals, t)
			return
		}
		for _, arg := range t.Args {
			collect(arg)
		}
	}
	for _, t := range terms {
		harvest(t)
		collect(t)
	}
	params := v.fn.params
	choices := make([][]*logic.Term, len(params))
	total := 1
	for i, param := range params {
		choices[i] = v.sampleValues(param, numbers)
		for _, literal := range literals {
			if entry := v.entry[param]; entry != nil && entry.Sort == literal.Sort {
				choices[i] = append(choices[i], literal)
			}
		}
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
// a witness: the given numbers that fit an integer type, both booleans, a
// nil and a non-nil error, and short sequences holding one repeated value.
// A float has no concrete values in the logic and stays symbolic.
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
	case entry == nil:
		return []*logic.Term{nil}
	case entry.Sort == logic.Int:
		return fitting(param.Type())
	case entry.Sort == logic.Bool:
		return []*logic.Term{logic.False(), logic.True()}
	case entry.Sort == logic.Err:
		return []*logic.Term{logic.NilErr(), someError}
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
