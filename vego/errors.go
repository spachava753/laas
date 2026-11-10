package vego

import (
	"go/ast"
	"go/token"
	"go/types"
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

// outcome is what verifying a function established about it, beyond the
// diagnostics it produced.
type outcome struct {
	// excused is set when the function may legitimately fail on every call:
	// it reaches a call whose failure no contract predicts, and its own
	// contract never says that it succeeds.
	excused bool
}

// verified verifies a function once and returns the outcome. A function that
// is still being verified, which happens on recursion, is not excused.
func (pv *pkgVerifier) verified(fn *funcInfo) *outcome {
	if result, ok := pv.outcomes[fn]; ok {
		return result
	}
	result := &outcome{}
	pv.outcomes[fn] = result
	pv.run(fn, func(v *fnVerifier) {
		v.verify()
		v.checkAlwaysFails(result)
	})
	return result
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

// forcesSuccess reports whether the contract makes the function succeed for
// some input: for every error result it has a clause "C -> err = nil" whose
// condition C speaks only about the inputs and is not provably impossible.
// Without such a clause an implementation that fails on every call may well
// satisfy the contract, whatever else the contract demands.
func (v *fnVerifier) forcesSuccess() bool {
	fn, st := v.fn, v.enter()
	opts := solver.Options{Preds: v.res.Preds, MaxSteps: v.maxSteps}
	outputs := map[*logic.Term]bool{}
	results := make([]*logic.Term, len(fn.results))
	for i, result := range fn.results {
		sort, _ := sortOf(result.Type())
		results[i] = v.fresh("out", sort)
		outputs[results[i]] = true
	}
	post := map[*types.Var]*logic.Term{}
	for _, param := range fn.params {
		post[param] = v.entry[param]
		if isSlice(param.Type()) {
			post[param] = v.fresh("out", post[param].Sort)
			outputs[post[param]] = true
		}
	}
	env := &contractEnv{pv: v.pkgVerifier, fn: fn, args: v.entry, post: post, results: results}
	var conditions [][]*logic.Term
	for range errorResults(fn) {
		conditions = append(conditions, nil)
	}
	for _, c := range fn.ensures {
		clause := v.formula(c, c.node, env)
		for n, index := range errorResults(fn) {
			conditions[n] = append(conditions[n], successConditions(clause, results[index])...)
		}
	}
	for _, candidates := range conditions {
		usable := slices.ContainsFunc(candidates, func(condition *logic.Term) bool {
			return !mentions(condition, outputs) && solver.Prove(st.hyps, logic.Not(condition), opts) != solver.Proved
		})
		if !usable {
			return false
		}
	}
	return true
}

// checkAlwaysFails rejects a contract that a function could meet by failing
// on every call. A postcondition of the form "err = nil -> ..." alone says
// what success looks like but never that success happens. A function that
// reached a call whose failure no contract predicts cannot promise success;
// it is excused, and its callers inherit the excuse.
func (v *fnVerifier) checkAlwaysFails(result *outcome) {
	if len(errorResults(v.fn)) == 0 || v.forcesSuccess() {
		return
	}
	if v.outside {
		result.excused = true
		return
	}
	v.report(v.fn.decl.Name.Pos(), "the contract of %s would also be met by a function that always returns an error; "+
		"state when it succeeds, for example with \"condition -> err = nil\"", v.fn.obj.Name())
}
