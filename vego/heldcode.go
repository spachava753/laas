package vego

import (
	"go/ast"
	"go/types"
)

// Verified code of another package may run code of this package that it
// holds but was not handed at the call that leads to it: a hook kept in a
// package-level variable, or a value it wraps that code which is not
// verified put together. "What a proof assumes" covers what code that is
// not verified keeps and runs later; it says nothing of verified code, so
// the call graph follows it (F43, step 0). Where it may happen is part of a
// function's summary (runs.go): ambient, when what it runs reads a
// package-level variable that code other than its package's initialisers
// may set to code, and the summaries of the implementations that a call
// through a value may reach in the packages this one imports.
//
// Only what this package can see is counted: the packages it imports, at any
// depth. An implementation in a package that it cannot see is the limit
// "What a proof assumes" states.

// readsHeldLocally reports whether a node's own body reads a package-level
// variable that code other than its package's initialisers may set to code.
func (pv *pkgVerifier) readsHeldLocally(body ast.Node) bool {
	found := false
	ast.Inspect(body, func(n ast.Node) bool {
		if id, ok := n.(*ast.Ident); ok {
			v, isVar := pv.info.Uses[id].(*types.Var)
			found = found || isVar && pv.holdsSetCode(v)
		}
		return !found
	})
	return found
}

// holdsSetCode reports whether a variable is a package-level variable whose
// type can hold code and that code other than its package's initialisers
// may set. A variable that nothing assigns after it is initialised, and
// whose contents are only read, or a sentinel error, holds only what its
// package's initialisers made, which cannot name a package that imports
// it.
func (pv *pkgVerifier) holdsSetCode(v *types.Var) bool {
	if v.Pkg() == nil || v.Parent() != v.Pkg().Scope() || !holdsCode(v.Type(), map[types.Type]bool{}) {
		return false
	}
	if v.Pkg() == pv.pass.Pkg {
		_, fixed := pv.fixed[v]
		return !pv.sentinels[v] && !(fixed && pv.readOnly[v])
	}
	if isError(v.Type()) {
		_, stable := pv.foreignSentinel(v)
		return !stable
	}
	fact := pv.publishedFixed(v)
	if fact == nil {
		return true
	}
	_, fixed := fact.Vars[v.Name()]
	return !(fixed && fact.ReadOnly[v.Name()])
}

func mapKeysOf(m map[string]bool) func(func(string) bool) {
	return func(yield func(string) bool) {
		for k := range m {
			if !yield(k) {
				return
			}
		}
	}
}
