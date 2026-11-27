package vego

import (
	"go/ast"
	"slices"
)

// The runs of the functions a call hands to parameters with a contract
// under calls, or under Calls in source, are a loop the caller does not
// write: the callee runs them any number of times, never included, in any
// order, with its own writes between them. Their invariant is written
// above the statement that makes the call, as a loop's is above the loop:
//
//	// @Invariant 0 <= n <= |xs|
//	each(xs, func(x int) {
//		if n < len(xs) {
//			n++
//		}
//	})
//
// It is proved where the call is made, after what the callee may write
// between two runs from any state where it holds, and at the end of every
// run, whose head assumes it; after the call it is known (runHanded). So
// it holds in every state in which the callee calls a handed function or
// returns. One group belongs to one call, and every run of every function
// that call hands proves all of it.

// handInvariantCall returns the call that an invariant written above a
// statement belongs to, or why there is none. The calls of the statement
// are those of its own expressions: not those inside a function literal it
// holds, nor inside its blocks, nor of an else branch, and not of a
// deferred call or a goroutine, which run when nothing of the statement is
// known.
func (v *fnVerifier) handInvariantCall(s ast.Stmt) (*ast.CallExpr, string) {
	var handing []*ast.CallExpr
	var own func(n ast.Node)
	own = func(n ast.Node) {
		ast.Inspect(n, func(n ast.Node) bool {
			switch n := n.(type) {
			case *ast.FuncLit, *ast.BlockStmt, *ast.DeferStmt, *ast.GoStmt:
				return false
			case *ast.IfStmt:
				if n.Init != nil {
					own(n.Init)
				}
				own(n.Cond)
				return false
			case *ast.CallExpr:
				if len(v.pkgVerifier.handedArgs(n)) > 0 {
					handing = append(handing, n)
				}
			}
			return true
		})
	}
	own(s)
	const where = "an Invariant annotation must be directly above a for loop, or above a statement that makes one call handing a function literal " +
		"to a parameter with a contract under calls or Calls, whose runs it describes"
	switch {
	case len(handing) == 0:
		return nil, where
	case len(handing) > 1:
		return nil, "an Invariant annotation above a statement describes the runs of what one call hands over, and this statement makes " +
			"several calls that hand functions over; make each call in a statement of its own"
	}
	call := handing[0]
	if !slices.ContainsFunc(v.pkgVerifier.handedArgs(call), func(arg ast.Expr) bool { return asLit(ast.Unparen(arg)) != nil }) {
		return nil, "an Invariant annotation above a call describes the runs of the function literals it hands over, and this call hands none: " +
			"a function or a method value writes the caller's variables only by its contract"
	}
	return call, ""
}

// invariantHolds proves the invariant of the runs of a call in a state.
func (v *fnVerifier) invariantHolds(invariants []*clause, st *state, what string) {
	for _, c := range invariants {
		v.checkClause(c, v.bodyEnv(st, c.pos), st, nil, c.pos, what)
	}
}

// assumeInvariant assumes the invariant of the runs of a call in a state.
func (v *fnVerifier) assumeInvariant(invariants []*clause, st *state) {
	for _, c := range invariants {
		st.assume(v.formula(c, c.node, v.bodyEnv(st, c.pos)))
	}
}

// keptBetweenRuns proves that the invariant of the runs of a call holds
// after what the callee may write between two runs, from any state in
// which it holds: a state made from the one at the call by forgetting what
// the runs and the callee may write, where the invariant is assumed, and
// in which what the callee may write is forgotten once more.
func (v *fnVerifier) keptBetweenRuns(invariants []*clause, atCall *state, written []target, eff *effects, name string) {
	if len(written) == 0 {
		return
	}
	between := atCall.clone()
	for _, t := range written {
		v.havoc(between, t, nil)
	}
	between = v.forget(between, eff)
	v.assumeInvariant(invariants, between)
	for _, t := range written {
		v.havoc(between, t, nil)
	}
	v.invariantHolds(invariants, between, "invariant may not hold after "+name+" writes what it may write between two runs")
}
