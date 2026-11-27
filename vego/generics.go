package vego

import (
	"fmt"
	"go/ast"
	"go/types"
	"iter"
	"maps"
	"path/filepath"
	"slices"
	"strings"

	"github.com/spachava753/laas/vego/internal/logic"
	"golang.org/x/tools/go/types/typeutil"
)

// Verified code may call a generic function that it cannot verify when a
// trust entry gives it a contract, as slices.Contains has. The entry is
// written once, against the generic signature, and means at each
// instantiation what its clauses mean at the type arguments of that
// instantiation. So a call is checked against a contract of its own
// instantiation: calleeAt makes, for the call, a function object whose
// signature is the instantiated one, and trustedContract builds and checks
// a contract for that object as it does for any trusted function. Every
// check of an entry runs at each instantiation, and a contract that can be
// used at one instantiation is never taken to be usable at another.
//
// One instantiation is one function object, cached per package by its
// generic function and its type arguments, compared by types.Identical. It
// is not one set of parameters: a parameter whose type mentions no type
// parameter is the same object in the generic signature and in every
// instantiation, as n of slices.Grow is. So nothing keyed by a parameter
// may outlive the contract of one instantiation (fn.runs, fn.calls,
// fn.keeps, and fn.vouchedWrites are fields of one funcInfo).
//
// A function object made here is its own Origin, as go/types documents
// for every function it did not make. originOf maps it back to the generic
// function, and every map keyed by functions of the package is read
// through it; see byFunc.

// instance is what is known of an instantiation that calleeAt made.
type instance struct {
	origin *types.Func
	targs  []types.Type
	fn     *types.Func
}

// instanceAt returns the instantiation that a call names in its function,
// if it calls a generic function.
func instanceAt(info *types.Info, fun ast.Expr) (types.Instance, bool) {
	switch e := ast.Unparen(fun).(type) {
	case *ast.IndexExpr:
		return instanceAt(info, e.X)
	case *ast.IndexListExpr:
		return instanceAt(info, e.X)
	case *ast.SelectorExpr:
		inst, ok := info.Instances[e.Sel]
		return inst, ok
	case *ast.Ident:
		inst, ok := info.Instances[e]
		return inst, ok
	}
	return types.Instance{}, false
}

// calleeAt returns the function a call calls, as typeutil.Callee does, but
// for a call of a generic function the function object of its
// instantiation. It returns nil where Callee gives no function.
func (pv *pkgVerifier) calleeAt(call *ast.CallExpr) *types.Func {
	callee, _ := typeutil.Callee(pv.info, call).(*types.Func)
	if callee == nil {
		return nil
	}
	sig := callee.Type().(*types.Signature)
	if view := pv.sortSliceAt(call, callee); view != nil {
		return view
	}
	if sig.TypeParams() == nil || sig.Recv() != nil {
		return callee
	}
	inst, ok := instanceAt(pv.info, call.Fun)
	if !ok {
		return callee
	}
	instSig, ok := inst.Type.(*types.Signature)
	if !ok || instSig.TypeParams() != nil {
		return callee
	}
	return pv.instantiate(callee, slices.Collect(inst.TypeArgs.Types()), instSig)
}

// instantiate returns the function object of the instantiation of a
// generic function at the type arguments, whose signature is sig, made
// once per package; see calleeAt.
func (pv *pkgVerifier) instantiate(callee *types.Func, targs []types.Type, instSig *types.Signature) *types.Func {
	// A call inside generic code, with a type parameter of its own as a
	// type argument, is never verified, and has no instantiation to check.
	if slices.ContainsFunc(targs, func(t types.Type) bool { return mentionsTypeParam(t, map[types.Type]bool{}) }) {
		return callee
	}
	for _, made := range pv.instances[callee] {
		if slices.EqualFunc(made.targs, targs, types.Identical) {
			return made.fn
		}
	}
	made := &instance{origin: callee, targs: targs, fn: types.NewFunc(callee.Pos(), callee.Pkg(), callee.Name(), instSig)}
	if pv.instances == nil {
		pv.instances = map[*types.Func][]*instance{}
		pv.instanceOf = map[*types.Func]*instance{}
	}
	pv.instances[callee] = append(pv.instances[callee], made)
	pv.instanceOf[made.fn] = made
	return made.fn
}

// staticCalleeAt is calleeAt for a static call: nil for a call of a method
// of an interface, as typeutil.StaticCallee gives.
func (pv *pkgVerifier) staticCalleeAt(call *ast.CallExpr) *types.Func {
	if typeutil.StaticCallee(pv.info, call) == nil {
		return nil
	}
	return pv.calleeAt(call)
}

// originOf returns the generic function of an instantiation that calleeAt
// made, and otherwise what Origin gives.
func (pv *pkgVerifier) originOf(f *types.Func) *types.Func {
	if made := pv.instanceOf[f]; made != nil {
		return made.origin
	}
	return f.Origin()
}

// byFunc reads a map keyed by functions of the package, and panics on an
// instantiation that calleeAt made, which would miss its generic function
// without a word; read it with originOf. Such an object is a function of a
// package whose scope holds, under its name, a generic function that is
// another object.
func byFunc[V any](m map[*types.Func]V, f *types.Func) V {
	v, _ := byFuncOK(m, f)
	return v
}

// byFuncOK is byFunc that also reports whether the map holds the function.
func byFuncOK[V any](m map[*types.Func]V, f *types.Func) (V, bool) {
	if f != nil && f.Pkg() != nil && f.Type().(*types.Signature).Recv() == nil {
		if declared, ok := f.Pkg().Scope().Lookup(f.Name()).(*types.Func); ok && declared != f && isGeneric(declared) {
			panic(fmt.Sprintf("vego: internal error: a map of functions is read with an instantiation of %s; read it with originOf", f.FullName()))
		}
	}
	v, ok := m[f]
	return v, ok
}

// typeArgsNamed spells the type arguments of an instantiation as the
// generic signature names them, as in "E = Point", for messages.
func (pv *pkgVerifier) typeArgsNamed(f *types.Func) string {
	made := pv.instanceOf[f]
	if made == nil {
		return ""
	}
	params := made.origin.Type().(*types.Signature).TypeParams()
	var named []string
	for i, t := range made.targs {
		named = append(named, params.At(i).Obj().Name()+" = "+types.TypeString(t, types.RelativeTo(pv.pass.Pkg)))
	}
	return strings.Join(named, ", ")
}

// genericTypes maps each parameter and result of an instantiation to its
// type in the generic signature, by position; nil for a function that is
// not one.
func (pv *pkgVerifier) genericTypes(f *types.Func) map[*types.Var]types.Type {
	made := pv.instanceOf[f]
	if made == nil {
		return nil
	}
	generic, inst := made.origin.Type().(*types.Signature), f.Type().(*types.Signature)
	found := map[*types.Var]types.Type{}
	for _, pair := range [][2]*types.Tuple{{generic.Params(), inst.Params()}, {generic.Results(), inst.Results()}} {
		for i := range pair[1].Len() {
			found[pair[1].At(i)] = pair[0].At(i).Type()
		}
	}
	return found
}

// throughTypeParam returns why a path cannot be named in a contract of a
// generic function: it names a field, a state, or the address of a value
// whose type in the generic signature is a type parameter, which has none
// of these whatever its constraint. t is the type the path starts from in
// the generic signature. The answer is the same at every instantiation,
// so it is a defect of the entry. A path through types it cannot follow is
// left to the resolution at the instantiation.
//
// A step that names a state names one only when some type declares a state
// of that name (isState); otherwise the resolver reads the form as an
// application or a predicate, which this does not judge.
func throughTypeParam(what string, t types.Type, steps []logic.Step, isState func(string) bool) error {
	spelled := what
	for _, step := range steps {
		object := t
		if target, ok := types.Unalias(t).Underlying().(*types.Pointer); ok {
			object = target.Elem()
		}
		param, isParam := types.Unalias(object).(*types.TypeParam)
		switch {
		case isParam && step.Field != "":
			return entryDefect{fmt.Errorf("%s.%s names a field of a value of type %s, a type parameter, whose type arguments need not have that field; "+
				"%s name it", spelled, step.Field, param.Obj().Name(), genericDefect)}
		case isParam && step.State != "" && isState(step.State):
			return entryDefect{fmt.Errorf("%s(%s) names a state of a value of type %s, a type parameter, whose type arguments need not have that state; "+
				"%s name it", step.State, spelled, param.Obj().Name(), genericDefect)}
		case isParam && step.Addr:
			return entryDefect{fmt.Errorf("&%s takes the address of a value of type %s, a type parameter, whose type arguments need not be structs; "+
				"%s take it", spelled, param.Obj().Name(), genericDefect)}
		case step.Field != "":
			found, _, _ := types.LookupFieldOrMethod(t, true, nil, step.Field)
			field, ok := found.(*types.Var)
			if !ok {
				return nil
			}
			t, spelled = field.Type(), spelled+"."+step.Field
		case step.Index != nil:
			switch u := coreType(t).(type) {
			case *types.Slice:
				t = u.Elem()
			case *types.Map:
				t = u.Elem()
			default:
				return nil
			}
			spelled += "[...]"
		}
	}
	return nil
}

// coreType returns the underlying type of a type, and of a type parameter
// the one underlying type that every type of its constraint has, or nil.
func coreType(t types.Type) types.Type {
	param, ok := types.Unalias(t).(*types.TypeParam)
	if !ok {
		return t.Underlying()
	}
	iface, ok := param.Constraint().Underlying().(*types.Interface)
	if !ok {
		return nil
	}
	var core types.Type
	for embedded := range iface.EmbeddedTypes() {
		var terms []*types.Term
		if union, isUnion := embedded.(*types.Union); isUnion {
			terms = slices.Collect(union.Terms())
		} else {
			terms = []*types.Term{types.NewTerm(false, embedded)}
		}
		for _, term := range terms {
			u := coreType(term.Type())
			if u == nil || (core != nil && !types.Identical(core, u)) {
				return nil
			}
			core = u
		}
	}
	return core
}

// strictlyComparable reports whether == on values of a type never panics:
// the type is comparable and no interface lies in it, as the specification
// defines it.
func strictlyComparable(t types.Type) bool {
	switch u := t.Underlying().(type) {
	case *types.Interface:
		return false
	case *types.Struct:
		for field := range u.Fields() {
			if !strictlyComparable(field.Type()) {
				return false
			}
		}
		return true
	case *types.Array:
		return strictlyComparable(u.Elem())
	}
	return types.Comparable(t)
}

// methodReached returns a method that code given a value of type t may
// call: one of the method set of t or of *t, or of a type that such a value
// holds at any depth, through fields, elements, keys, and pointers. Generic
// code reaches these through the methods of its constraint, by converting
// the value to an interface, and by reflection; nil when there is none.
func methodReached(t types.Type, seen map[types.Type]bool) *types.Func {
	if t == nil || seen[t] {
		return nil
	}
	seen[t] = true
	if _, isIface := t.Underlying().(*types.Interface); !isIface {
		pointer := types.Type(types.NewPointer(t))
		if _, isPointer := t.Underlying().(*types.Pointer); isPointer {
			pointer = t
		}
		if set := types.NewMethodSet(pointer); set.Len() > 0 {
			return set.At(0).Obj().(*types.Func)
		}
	}
	switch u := t.Underlying().(type) {
	case *types.Pointer:
		return methodReached(u.Elem(), seen)
	case *types.Slice:
		return methodReached(u.Elem(), seen)
	case *types.Array:
		return methodReached(u.Elem(), seen)
	case *types.Map:
		if m := methodReached(u.Key(), seen); m != nil {
			return m
		}
		return methodReached(u.Elem(), seen)
	case *types.Struct:
		for field := range u.Fields() {
			if m := methodReached(field.Type(), seen); m != nil {
				return m
			}
		}
	}
	return nil
}

// typeParamClaims returns the type parameters of a generic function for
// which its entry claims, under asserts, that it runs no method of a value
// of the type parameter's type; see checkTypeArgs.
func typeParamClaims(entry *trustEntry, origin *types.Func) map[*types.TypeParam]bool {
	claimed := map[*types.TypeParam]bool{}
	if entry == nil {
		return claimed
	}
	params := origin.Type().(*types.Signature).TypeParams()
	for i := range params.Len() {
		for _, item := range entry.asserts {
			if item.name == params.At(i).Obj().Name() && len(item.dests) == 0 {
				claimed[params.At(i)] = true
			}
		}
	}
	return claimed
}

// isTypeParamName reports whether a name is that of a type parameter of
// the generic function of an instantiation.
func (pv *pkgVerifier) isTypeParamName(f *types.Func, name string) bool {
	made := pv.instanceOf[f]
	if made == nil {
		return false
	}
	params := made.origin.Type().(*types.Signature).TypeParams()
	for i := range params.Len() {
		if params.At(i).Obj().Name() == name {
			return true
		}
	}
	return false
}

// checkTypeArgs refuses a call of an instantiation whose type arguments
// the verifier cannot reason about at all, whatever the entry says:
//
//   - one that can hold code, as an interface or a function does: an entry
//     for every type argument would have to say what the function runs of
//     it, keeps, and vouches for, at those instantiations only;
//   - one the verifier does not model, as an array;
//   - one that is not strictly comparable where the constraint is
//     comparable: == on it may panic;
//   - one that holds a state, as a sync.Mutex does: such a value is never
//     copied or overwritten, and these functions copy their elements;
//   - one that has methods, or holds values that have them, unless the
//     entry claims under asserts that the function runs none of them:
//     generic code reaches them through its constraint, through an
//     interface, and by reflection, and they could write memory or call
//     back into the caller.
func (v *fnVerifier) checkTypeArgs(at ast.Node, callee *types.Func, entry *trustEntry) {
	if made := v.pkgVerifier.instanceOf[callee]; made != nil {
		if problem := v.pkgVerifier.typeArgProblem(made, entry); problem != "" {
			v.unsupported(at.Pos(), problem)
		}
	}
}

// typeArgProblem says why checkTypeArgs refuses an instantiation, or
// returns "".
func (pv *pkgVerifier) typeArgProblem(made *instance, entry *trustEntry) string {
	params := made.origin.Type().(*types.Signature).TypeParams()
	claimed := typeParamClaims(entry, made.origin)
	q := types.RelativeTo(pv.pass.Pkg)
	name := made.origin.Name()
	if made.origin.Pkg() != pv.pass.Pkg {
		name = made.origin.FullName()
	}
	for i, t := range made.targs {
		param := params.At(i)
		arg := fmt.Sprintf("%s = %s", param.Obj().Name(), types.TypeString(t, q))
		iface, _ := param.Constraint().Underlying().(*types.Interface)
		switch _, modelled := layoutOf(t); {
		case iface != nil && iface.IsComparable() && !strictlyComparable(t):
			return fmt.Sprintf("%s is called with %s, whose values == may compare with a panic; "+
				"its constraint is comparable, and only a type in which no interface lies can be passed", name, arg)
		case holdsCode(t, map[types.Type]bool{}):
			return fmt.Sprintf("%s is called with %s, which is or holds %s; "+
				"a generic function cannot be called yet with a type argument that can hold code", name, arg, heldCode(t, map[types.Type]bool{}))
		case !modelled:
			return fmt.Sprintf("%s is called with %s, a type that vego does not model", name, arg)
		}
		if _, holds := holdsState(t); holds {
			return fmt.Sprintf("%s is called with %s = %s; a generic function copies and overwrites values of its type arguments, "+
				"and a value that holds a state is never copied or overwritten", name, param.Obj().Name(), holding(t, q))
		}
		if method := methodReached(t, map[types.Type]bool{}); method != nil && !claimed[param] {
			return fmt.Sprintf("%s is called with %s, and %s may run the method %s, which a value of that type reaches; "+
				"if it runs no method of a value of type %s, claim it in the entry of %s with asserts: {%s: []}",
				name, arg, name, types.ObjectString(method, q), param.Obj().Name(), made.origin.FullName(), param.Obj().Name())
		}
	}
	return ""
}

// checkGenericCallee refuses a call of a generic function that has no
// trusted contract, and the type arguments checkTypeArgs refuses. A
// generic function of this package with an entry is called like one of
// another package; the call graph walks its body as that of any trusted
// function of the package.
func (v *fnVerifier) checkGenericCallee(call *ast.CallExpr, callee *types.Func, made *instance) {
	origin := made.origin
	name := v.calleeName(origin)
	if origin.Pkg() == v.pass.Pkg {
		if own := v.pkgVerifier.funcs[origin]; own != nil && own.annotated() {
			v.unsupported(call.Pos(), fmt.Sprintf("it calls %s, a generic function with annotations; generic functions cannot be verified yet", name))
		}

	}
	entry := v.pkgVerifier.entryFor(origin.FullName())
	if why := noEntryCan[origin.FullName()]; entry == nil && why != "" {
		v.unsupported(call.Pos(), fmt.Sprintf("it calls %s, which is not supported yet: %s", name, why))
	}
	if entry == nil {
		v.unsupported(call.Pos(), fmt.Sprintf("it calls %s, a generic function, which has no trusted contract; generic functions cannot be verified yet, "+
			"so a call of one needs a trusted contract: %s", name, strings.TrimPrefix(v.addEntryAdvice(origin.FullName()), "or ")))
	}
	v.checkTypeArgs(call, callee, entry)
}

// genericRunsValues reports, for a generic function, whether its entry may
// make it call through a value: it lists under runs a parameter that has
// no contract under calls. Its parameters of a type parameter's type hold
// no code, since checkTypeArgs refuses a type argument that can.
func genericRunsValues(entry *trustEntry) bool {
	for _, item := range entry.runs {
		if !slices.ContainsFunc(entry.calls, func(c trustCall) bool { return c.name == item.text }) {
			return true
		}
	}
	return false
}

// isGeneric reports whether a function object is a generic function, of
// which no contract is built: only its instantiations have one.
func isGeneric(f *types.Func) bool {
	sig := f.Type().(*types.Signature)
	return sig.TypeParams() != nil || sig.RecvTypeParams() != nil
}

// genericDefect is a part of the message of a clause of a generic entry
// that has no meaning at any type argument.
const genericDefect = "a contract of a generic function cannot"

// entryDefect is an error of a clause of a generic entry that is the same
// at every type argument: it names what no type parameter's value has.
type entryDefect struct{ error }

func (e entryDefect) Unwrap() error { return e.error }

// insteadOf ends the message of a contract of an instantiation that cannot
// be used there. For a problem of this instantiation it says what to call
// instead: the function of the same name with Func, which is handed a
// function literal, where it has an entry, and otherwise a loop. For a
// defect of the entry, it says to fix the entry.
func (pv *pkgVerifier) insteadOf(fn *funcInfo, entry *trustEntry, problem string) string {
	f := fn.obj
	if !fn.atTypes[problem] {
		return fmt.Sprintf("; the entry has this defect at every type argument, so fix the entry in %s", filepath.Base(entry.file.path))
	}
	if alternative := entry.key + "Func"; !strings.HasSuffix(entry.key, "Func") && pv.entryFor(alternative) != nil {
		return fmt.Sprintf("; call %s instead, with a function literal that compares what you need of the elements, or write a loop", alternative)
	}
	// A function over a slice or a map is written out as a loop.
	if made := pv.instanceOf[f]; made != nil {
		for param := range made.origin.Type().(*types.Signature).Params().Variables() {
			switch coreType(param.Type()).(type) {
			case *types.Slice, *types.Map:
				return "; write a loop instead"
			}
		}
	}
	return "; write out what it does instead"
}

// explicitInstance returns the generic function that an expression such as
// glib.IsPos[int] instantiates with its type arguments written out, or nil
// for an index of anything else.
func explicitInstance(info *types.Info, e ast.Expr) *types.Func {
	var x ast.Expr
	switch e := e.(type) {
	case *ast.IndexExpr:
		x = e.X
	case *ast.IndexListExpr:
		x = e.X
	default:
		return nil
	}
	var id *ast.Ident
	switch x := ast.Unparen(x).(type) {
	case *ast.Ident:
		id = x
	case *ast.SelectorExpr:
		if info.Selections[x] != nil {
			return nil
		}
		id = x.Sel
	default:
		return nil
	}
	f, ok := info.Uses[id].(*types.Func)
	if !ok || !isGeneric(f) {
		return nil
	}
	return f
}

// genericReceiver reports whether a receiver's type is a generic type or an
// instantiation of one, or a pointer to such a type.
func genericReceiver(t types.Type) bool {
	if pointer, ok := types.Unalias(t).(*types.Pointer); ok {
		t = pointer.Elem()
	}
	named, ok := types.Unalias(t).(*types.Named)
	return ok && (named.TypeParams() != nil || named.TypeArgs() != nil)
}

// byParam maps parameters of one contract to what its entry says of each,
// as runs, calls, keeps, and vouches for what is written do. It is read
// only through get, which panics on a parameter whose type mentions a type
// parameter: no contract is built for a generic function, so such a
// lookup is a site that paired arguments with the generic signature where
// it had to use the instantiation's; see calleeAt.
type byParam[V any] struct{ m map[*types.Var]V }

func (b *byParam[V]) get(p *types.Var) V {
	if p != nil && mentionsTypeParam(p.Type(), map[types.Type]bool{}) {
		panic(fmt.Sprintf("vego: internal error: a contract is read for the parameter %s of type %s, of a generic signature; "+
			"bind the call by the signature of its instantiation", p.Name(), p.Type()))
	}
	return b.m[p]
}

func (b *byParam[V]) set(p *types.Var, v V) {
	if b.m == nil {
		b.m = map[*types.Var]V{}
	}
	b.m[p] = v
}

func (b *byParam[V]) len() int { return len(b.m) }

// all ranges over the parameters and what is said of each.
func (b *byParam[V]) all() iter.Seq2[*types.Var, V] { return maps.All(b.m) }
