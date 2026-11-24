package vego

import (
	"fmt"
	"go/ast"
	"go/types"
	"slices"
	"strings"

	"github.com/spachava753/laas/vego/internal/logic"
)

// Struct variables whose address is taken (kind 3, part 4 of package-level
// variables, F32).
//
// A package-level variable of a struct type whose address the build takes,
// with &v, &v.f, or a method with a pointer receiver selected on v or one of
// its fields, lies in an allocation of its own: the constant reference
// boxRef, at position 0, in the struct's ordinary regions, as a boxed local
// lies at the allocation its declaration made. The allocation existed on
// entry of every function, is not nil, and is apart from every other kind-3
// variable's. A pointer parameter of its type may point to it, and the
// proof weighs both cases.
//
// It is not a boxed local: v.boxed means "made by this function" to the
// readers of origins, of loops, and of literals, and none of that holds of
// a package-level variable. Its reads and writes have a path of their own,
// and which variables are kind 3 is decided for the package by findChanges
// before any function is walked.

// boxName begins the name of the reference of a kind-3 variable.
const boxName = "varbox "

// boxRef is the reference of the allocation of a kind-3 variable.
func boxRef(variable *types.Var) *logic.Term {
	return logic.Const(boxName+errorKey(variable), logic.Ref)
}

// isBoxedGlobal reports whether a package-level variable is a struct
// variable whose address is taken (kind 3): of this package, by what the
// build changes; of another package, by what its package published, as long
// as no directive of this build names it.
func (pv *pkgVerifier) isBoxedGlobal(variable *types.Var) bool {
	if variable == nil || variable.Pkg() == nil || variable.Parent() != variable.Pkg().Scope() {
		return false
	}
	if variable.Pkg() == pv.pass.Pkg {
		return pv.boxedWhy(variable) == "" && pv.changeKinds[variable]&changeAddress != 0
	}
	fact := pv.publishedFixed(variable)
	return fact != nil && fact.Boxed[variable.Name()] && pv.changeKinds[variable]&changeLinked == 0
}

// boxedWhy reports why a variable of this package whose address the build
// takes cannot be a kind-3 variable, or "".
func (pv *pkgVerifier) boxedWhy(variable *types.Var) string {
	kinds := pv.changeKinds[variable]
	spelled := pv.spelling(variable)
	t := variable.Type()
	switch {
	case kinds&changeAddress == 0:
		return fmt.Sprintf("%s does not have its address taken", spelled)
	case kinds&changeLinked != 0:
		return fmt.Sprintf("%s %s; a variable that a directive or assembly names is another symbol's storage, which code writes under the other name, "+
			"so it cannot be verified", spelled, pv.changeOf[variable])
	case isError(t):
		return fmt.Sprintf("%s %s; package-level error variables that are changed are not supported yet", spelled, pv.ownChanges[variable])
	case !isStructType(t):
		return fmt.Sprintf("%s %s; only a package-level variable of a struct type may have its address taken, since pointers to anything "+
			"but a struct are not supported yet", spelled, pv.addressAt(variable))
	}
	if _, ok := layoutOf(t); !ok {
		return fmt.Sprintf("%s has type %s, which is not supported%s", spelled, t, unsupportedHint(t))
	}
	if !pv.dataType(t, map[types.Type]bool{}) {
		return fmt.Sprintf("%s has type %s, which can hold a function value, an interface value, an error, a channel, or an unsafe.Pointer; "+
			"package-level variables of such types whose address is taken are not supported yet", spelled, t)
	}
	return ""
}

// addressAt says where the build first takes the address of a variable of
// this package, as findChanges recorded it.
func (pv *pkgVerifier) addressAt(variable *types.Var) string {
	if at := pv.addressSite[variable]; at != "" {
		return at
	}
	return pv.ownChanges[variable]
}

// noteBoxed states, once on a path, what is known of the allocation of a
// kind-3 variable: it is not nil, it existed on entry, and it is apart from
// that of every other kind-3 variable the function met.
func (v *fnVerifier) noteBoxed(st *state, variable *types.Var) {
	if st == nil {
		return
	}
	if v.boxedMet == nil {
		v.boxedMet = map[string]*types.Var{}
	}
	key := errorKey(variable)
	v.boxedMet[key] = variable
	note := boxName + key
	if st.noted[note] {
		return
	}
	st.noted[note] = true
	ref := boxRef(variable)
	st.assume(logic.And(logic.Not(logic.Eq(ref, logic.RefLit(0))), logic.Lt(ref, v.entryBrk)))
	for _, other := range slices.Sorted(func(yield func(string) bool) {
		for k := range v.boxedMet {
			if !yield(k) {
				return
			}
		}
	}) {
		if other != key && st.noted[boxName+other] {
			st.assume(logic.Not(logic.Eq(ref, boxRef(v.boxedMet[other]))))
		}
	}
}

// boxedPointer is the pointer to a kind-3 variable, noted on the path.
func (v *fnVerifier) boxedPointer(st *state, variable *types.Var) value {
	v.noteBoxed(st, variable)
	return value{boxRef(variable), logic.IntLit(0)}
}

// locateBoxed follows a path of an annotation that starts at a kind-3
// variable, as locateAssigned does for an assigned one: in a contract its
// value when the function is called, primed its value on return, and inside
// a body its current value, or with old its value when the function was
// entered.
func (e *specEnv) locateBoxed(variable *types.Var, steps []logic.Step, when logic.When) (reached, error) {
	spelled := e.v.spelling(variable)
	hops, final, err := plan(variable.Type(), steps, e.writtenIn())
	if err != nil {
		return reached{}, fmt.Errorf("%s%v", spelled, err)
	}
	mem := e.now
	switch when {
	case logic.Old:
		if e.fn != nil {
			return reached{}, fmt.Errorf("old(%s) is only allowed inside a body; in a contract %s already denotes the value on entry", spelled, spelled)
		}
		mem = memory{}
	case logic.Primed:
		switch {
		case e.fn == nil:
			return reached{}, fmt.Errorf("%s' is only allowed in Ensures; inside a body %s already denotes the current value", spelled, spelled)
		case e.post == nil:
			return reached{}, fmt.Errorf("%s' describes the state on return and is only allowed in Ensures", spelled)
		}
		mem = e.post
	}
	pointer := e.v.boxedPointer(e.sink, variable)
	val := e.v.fetchIn(e.sink, mem, e.v.cellsOf(variable.Type()), pointer[0], pointer[1], variable.Type())
	e.v.noteTyped(e.sink, val, variable.Type())
	cur, ground := e.v.follow(e.sink, mem, val, hops)
	found := reached{val: cur, typ: final, mem: mem, hops: len(hops)}
	if ground {
		found.sink = e.sink
	}
	return found, nil
}

// boxedTarget locates a Modifies entry whose path starts at a kind-3
// variable: the struct at its allocation, with its states and what it owns,
// or the part a path names, as for the struct a pointer parameter points to.
func (v *fnVerifier) boxedTarget(fn *funcInfo, m *modTarget, variable *types.Var, args map[*types.Var]value, sink *state, mem memory) (shape, target, error) {
	t := variable.Type()
	root := located{typ: t, cells: v.cellsOf(t)}
	if mem != nil {
		pointer := v.boxedPointer(sink, variable)
		root.ref, root.at = pointer[0], pointer[1]
		root.val = v.fetchIn(sink, mem, root.cells, pointer[0], pointer[1], t)
		v.noteTyped(sink, root.val, t)
	}
	return v.walkTarget(fn, m, nil, root, t, mem == nil, args, sink, mem)
}

// addressRoot returns the package-level variable whose address &e takes,
// through struct fields, or nil.
func (v *fnVerifier) addressRoot(e ast.Expr) *types.Var {
	for {
		switch x := ast.Unparen(e).(type) {
		case *ast.Ident:
			return packageVariableOf(v.info.Uses[x], "")
		case *ast.SelectorExpr:
			if id, ok := x.X.(*ast.Ident); ok && v.isPackageName(id) {
				return packageVariableOf(v.info.Uses[x.Sel], "")
			}
			selection := v.info.Selections[x]
			if selection == nil || selection.Kind() != types.FieldVal || selection.Indirect() {
				return nil
			}
			if _, viaPointer := pointee(v.info.TypeOf(x.X)); viaPointer {
				return nil
			}
			e = x.X
		default:
			return nil
		}
	}
}

// variableOfTarget returns the package-level variable whose storage a
// target is, assigned or of kind 3, or nil.
func (v *fnVerifier) variableOfTarget(t target) *types.Var {
	if variable := v.variableOfCells(t.cells); variable != nil {
		return variable
	}
	// A kind-3 variable lies at its own reference.
	if t.single && t.ref != nil && t.ref.Op == logic.OpConst && strings.HasPrefix(t.ref.Name, boxName) {
		return v.lookupKey(strings.TrimPrefix(t.ref.Name, boxName))
	}
	return nil
}
