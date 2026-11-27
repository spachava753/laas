package vego

import (
	"go/ast"
	"go/types"
)

// sort.Slice and sort.SliceStable take the slice they sort as an any and
// panic on anything else, which no entry can describe for every type the
// any may hold. A call is read through a typed view (D4 of F40): the
// generic signature func[S ~[]E, E any](x S, less func(i, j int) bool),
// instantiated at the static type of the argument before Go converts it to
// any. What the function does depends only on the dynamic value, which is
// that argument, so the instantiation means what the call does. Its entry
// is written under the function's own name against the view's parameters,
// and is read and checked as a generic one is (generics.go): asserts,
// type arguments that can hold code, instantiations, and compares. An
// argument whose static type is not a slice, an any or nil among them, is
// refused at the call (sortSliceRefusal).

// sortSliceViews names the functions read through the typed view.
var sortSliceViews = map[string]bool{"sort.Slice": true, "sort.SliceStable": true}

// sortSliceView returns the generic function object of the view of
// sort.Slice or sort.SliceStable, made once per package.
func (pv *pkgVerifier) sortSliceView(callee *types.Func) *types.Func {
	if view := pv.sliceViews[callee]; view != nil {
		return view
	}
	view := newSliceView(callee)
	if pv.sliceViews == nil {
		pv.sliceViews = map[*types.Func]*types.Func{}
	}
	pv.sliceViews[callee] = view
	return view
}

// newSliceView makes the generic function object of the view of sort.Slice
// or sort.SliceStable.
func newSliceView(callee *types.Func) *types.Func {
	pkg := callee.Pkg()
	e := types.NewTypeParam(types.NewTypeName(callee.Pos(), pkg, "E", nil), types.Universe.Lookup("any").Type())
	slice := types.NewInterfaceType(nil, []types.Type{types.NewUnion([]*types.Term{types.NewTerm(true, types.NewSlice(e))})})
	slice.Complete()
	s := types.NewTypeParam(types.NewTypeName(callee.Pos(), pkg, "S", nil), slice)
	less := callee.Type().(*types.Signature).Params().At(1)
	params := types.NewTuple(types.NewParam(callee.Pos(), pkg, "x", s), types.NewParam(less.Pos(), pkg, less.Name(), less.Type()))
	sig := types.NewSignatureType(nil, nil, []*types.TypeParam{s, e}, params, nil, false)
	return types.NewFunc(callee.Pos(), pkg, callee.Name(), sig)
}

// sortSliceAt returns the instantiation of the view of a call of
// sort.Slice or sort.SliceStable whose argument is a slice, or nil.
func (pv *pkgVerifier) sortSliceAt(call *ast.CallExpr, callee *types.Func) *types.Func {
	if !sortSliceViews[callee.FullName()] || len(call.Args) != 2 {
		return nil
	}
	arg := pv.info.TypeOf(call.Args[0])
	if arg == nil || !isSlice(arg) || pv.info.Types[call.Args[0]].IsNil() {
		return nil
	}
	view := pv.sortSliceView(callee)
	targs := []types.Type{arg, elemType(arg)}
	instSig, err := types.Instantiate(nil, view.Type(), targs, true)
	if err != nil {
		return nil
	}
	return pv.instantiate(view, targs, instSig.(*types.Signature))
}

// sortSliceRefusal says why a call of sort.Slice or sort.SliceStable that
// no view reads cannot be verified, or returns "".
func (pv *pkgVerifier) sortSliceRefusal(call *ast.CallExpr, callee *types.Func) string {
	if !sortSliceViews[callee.FullName()] || pv.instanceOf[callee] != nil {
		return ""
	}
	what := types.ExprString(call.Args[0])
	if t := pv.info.TypeOf(call.Args[0]); t != nil && !pv.info.Types[call.Args[0]].IsNil() {
		what += " of type " + types.TypeString(t, types.RelativeTo(pv.pass.Pkg))
	}
	return "it calls " + callee.FullName() + " with " + what + ", which is not a slice; " + callee.FullName() + " panics unless it is handed a slice, and vego knows what it sorts only from the static type " +
		"of the argument, so pass the slice itself, or call slices.SortFunc"
}
