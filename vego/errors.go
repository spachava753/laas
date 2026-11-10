package vego

import (
	"go/ast"
	"go/token"
	"go/types"

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

// returnsError reports whether a function has a result of type error.
func returnsError(fn *funcInfo) bool {
	for _, result := range fn.results {
		if sort, ok := sortOf(result.Type()); ok && sort == logic.Err {
			return true
		}
	}
	return false
}

// admitsAlwaysFailing reports whether the contract of the function would also
// be satisfied by an implementation that returns a non-nil error, zero values
// for everything else, and changes nothing.
func (v *fnVerifier) admitsAlwaysFailing() bool {
	fn, st := v.fn, v.enter()
	opts := solver.Options{Preds: v.res.Preds, MaxSteps: v.maxSteps}
	if solver.Prove(st.hyps, logic.False(), opts) == solver.Proved {
		return false
	}
	results := make([]*logic.Term, len(fn.results))
	for i, result := range fn.results {
		sort, _ := sortOf(result.Type())
		results[i] = zero(sort)
		if sort == logic.Err {
			results[i] = v.fresh("failure", logic.Err)
			st.assume(logic.Not(logic.IsNil(results[i])))
		}
	}
	env := &contractEnv{pv: v.pkgVerifier, fn: fn, args: v.entry, post: v.entry, results: results}
	for _, c := range fn.ensures {
		if solver.Prove(st.hyps, v.formula(c, c.node, env), opts) != solver.Proved {
			return false
		}
	}
	return true
}

// failsFromOutside reports whether a function can fail for reasons no
// contract can predict: it calls something whose own failure is not tied to
// its inputs. Such a function cannot promise success, so its contract may
// leave "always fails" open. A callee without a contract counts, since
// nothing says when it succeeds; so does a verified callee that is itself
// excused. Error constructors do not: they fail by design, not by chance.
func (pv *pkgVerifier) failsFromOutside(fn *funcInfo, visiting map[*funcInfo]bool) bool {
	if visiting[fn] || fn.decl.Body == nil {
		return false
	}
	visiting[fn] = true
	found := false
	ast.Inspect(fn.decl.Body, func(n ast.Node) bool {
		call, ok := n.(*ast.CallExpr)
		if !ok || found {
			return !found
		}
		callee, _ := typeutil.Callee(pv.info, call).(*types.Func)
		if callee == nil || errorConstructor(callee) {
			return true
		}
		results := callee.Type().(*types.Signature).Results()
		for i := range results.Len() {
			if sort, ok := sortOf(results.At(i).Type()); !ok || sort != logic.Err {
				continue
			}
			target := pv.funcs[callee]
			if target == nil || !target.annotated() {
				found = true
			} else {
				excused := false
				pv.run(target, func(v *fnVerifier) { excused = v.admitsAlwaysFailing() })
				found = excused && pv.failsFromOutside(target, visiting)
			}
		}
		return true
	})
	return found
}

// checkAlwaysFails rejects a contract that a function could meet by failing
// on every call. A postcondition of the form "err = nil -> ..." alone says
// what success looks like but never that success happens.
func (v *fnVerifier) checkAlwaysFails() {
	if !returnsError(v.fn) || !v.admitsAlwaysFailing() || v.failsFromOutside(v.fn, map[*funcInfo]bool{}) {
		return
	}
	v.report(v.fn.decl.Name.Pos(), "the contract of %s would also be met by a function that always returns an error; "+
		"state when it succeeds, for example with \"condition -> err = nil\"", v.fn.obj.Name())
}
