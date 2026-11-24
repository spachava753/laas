package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"maps"
	"path/filepath"
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

// The closed address (F3 of the design review of F32). The address of a
// kind-3 variable is closed when every use of it in the build is the
// receiver or an argument of a call, deferred or not but not in a go
// statement, of a trusted function that neither keeps it nor stores it,
// returns nothing that can hold memory, and runs no code that could be
// handed it: then no pointer outside such a call points into the variable
// (K2), and no interface value but the temporary converted at such a call
// has a row that holds a cell of it (K1). Verified callees are not sinks: one
// could convert its parameter and hand the interface value to another
// verified function, whose rows would then hold the variable.

// closedKey ends the key under which a proof relies on the address of a
// kind-3 variable being closed, and under which a package publishes a use
// that is not.
const closedKey = "&closed"

// addressUseWhy says why the use of a variable's address at the end of
// stack, as findChanges found it, is not closed, or "" when it is.
func (pv *pkgVerifier) addressUseWhy(stack []ast.Node) string {
	i := len(stack) - 1
	var cur ast.Expr = stack[i].(*ast.Ident)
	if i > 0 {
		if sel, ok := stack[i-1].(*ast.SelectorExpr); ok && sel.Sel == cur {
			cur, i = sel, i-1
		}
	}
	// call returns the call whose argument or function e is, outside
	// parentheses, and the index of the argument, -1 for the function.
	call := func(i int, e ast.Expr) (*ast.CallExpr, int, int) {
		for i--; i >= 0; i-- {
			if paren, ok := stack[i].(*ast.ParenExpr); ok {
				e = paren
				continue
			}
			c, ok := stack[i].(*ast.CallExpr)
			if !ok {
				return nil, 0, i
			}
			if c.Fun == e {
				return c, -1, i
			}
			for k, arg := range c.Args {
				if arg == e {
					return c, k, i
				}
			}
			return nil, 0, i
		}
		return nil, 0, i
	}
	inGo := func(i int) bool {
		_, ok := stack[max(i-1, 0)].(*ast.GoStmt)
		return i > 0 && ok
	}
	for i--; i >= 0; i-- {
		switch parent := stack[i].(type) {
		case *ast.ParenExpr:
			cur = parent
			continue
		case *ast.SelectorExpr:
			selection := pv.info.Selections[parent]
			if parent.X != cur || selection == nil {
				return "its address is let out at " + pv.placeOfPos(parent.Pos())
			}
			if selection.Kind() == types.FieldVal {
				cur = parent
				continue
			}
			c, k, at := call(i, parent)
			method, _ := selection.Obj().(*types.Func)
			switch {
			case c == nil || k != -1:
				return "a method value of it is made at " + pv.placeOfPos(parent.Pos())
			case inGo(at):
				return "its address is handed to a goroutine at " + pv.placeOfPos(parent.Pos())
			case method == nil:
				return "its address is let out at " + pv.placeOfPos(parent.Pos())
			}
			return pv.sinkWhy(method, 0, nil, parent.Pos(), 0)
		case *ast.UnaryExpr:
			if parent.Op != token.AND {
				return "its address is let out at " + pv.placeOfPos(parent.Pos())
			}
			c, k, at := call(i, parent)
			switch {
			case c == nil || k < 0:
				return "its address is let out at " + pv.placeOfPos(parent.Pos())
			case inGo(at):
				return "its address is handed to a goroutine at " + pv.placeOfPos(parent.Pos())
			}
			callee := pv.calleeAt(c)
			if callee == nil {
				return "its address is handed to a call that is not of a named function at " + pv.placeOfPos(parent.Pos())
			}
			index := k
			if callee.Type().(*types.Signature).Recv() != nil {
				index++
			}
			return pv.sinkWhy(callee, index, pv.info.TypeOf(parent), parent.Pos(), 0)
		default:
			return "its address is let out at " + pv.placeOfPos(parent.Pos())
		}
	}
	return "its address is let out"
}

// sinkWhy says why a trusted function is not a sink of the address handed
// to it as its parameter at index, or "". addr is the type of the address
// when it is handed as an argument, which converts it when the parameter
// is an interface, and nil for a receiver.
func (pv *pkgVerifier) sinkWhy(callee *types.Func, index int, addr types.Type, pos token.Pos, depth int) string {
	where := pv.placeOfPos(pos)
	if isGeneric(callee) || callee.Origin() != callee {
		return fmt.Sprintf("its address is handed to %s at %s, a generic function or a method of a generic type", callee.Name(), where)
	}
	fn := pv.trustedContract(callee)
	if fn == nil {
		return fmt.Sprintf("its address is handed to %s at %s, which is not a trusted function, and verified code could convert it", callee.Name(), where)
	}
	if len(fn.params) == 0 {
		return fmt.Sprintf("its address is handed to %s at %s", callee.Name(), where)
	}
	p := fn.params[min(index, len(fn.params)-1)]
	fail := func(why string) string {
		return fmt.Sprintf("its address is handed to %s at %s, whose trusted contract %s", callee.Name(), where, why)
	}
	if len(fn.keeps.get(p)) > 0 {
		return fail("keeps it")
	}
	for _, item := range fn.trust.stores {
		if item.text == p.Name() {
			return fail("stores under it")
		}
	}
	if p == fn.formatted || p == fn.encoded || p == fn.decoded {
		return fail("runs the methods of what it is handed there")
	}
	for result := range callee.Type().(*types.Signature).Results().Variables() {
		if !memoryFree(result.Type()) {
			return fail("returns a value that can hold memory")
		}
	}
	for _, cb := range fn.calls.all() {
		for param := range cb.sig.Params().Variables() {
			if !memoryFree(param.Type()) {
				return fail(fmt.Sprintf("calls %s with a value that can hold memory", cb.param.Name()))
			}
		}
	}
	for run := range fn.runs.all() {
		if run == p || run == fn.prints {
			continue
		}
		// A function it calls under its calls clause is handed what that
		// clause gives it, which the loop above checked.
		if fn.calls.get(run) != nil {
			continue
		}
		return fail(fmt.Sprintf("runs %s, which could be handed it", run.Name()))
	}
	run := fn.runs.get(p) || fn.prints == p
	switch {
	case !run:
		return ""
	case addr == nil || !isIface(p.Type()) || depth > 0:
		return fail("runs it")
	}
	// It runs the converted address itself: each method of it that the
	// interface takes must be a sink of its receiver.
	iface, _ := p.Type().Underlying().(*types.Interface)
	for m := range iface.Methods() {
		obj, _, _ := types.LookupFieldOrMethod(addr, true, m.Pkg(), m.Name())
		method, ok := obj.(*types.Func)
		if !ok {
			return fail("runs a method of it that cannot be found")
		}
		if why := pv.sinkWhy(method, 0, nil, pos, depth+1); why != "" {
			return why
		}
	}
	return ""
}

// noteAddressUse records a use of a variable's address that is not closed,
// and publishes one of a variable of another package, which a proof of
// that package may rely on being closed.
func (pv *pkgVerifier) noteAddressUse(variable *types.Var, stack []ast.Node, pos token.Pos) {
	// Only a struct variable of this package, or one its package
	// published as kind 3, can be relied on as closed.
	if variable.Pkg() == pv.pass.Pkg && !isStructType(variable.Type()) {
		return
	}
	if fact := pv.publishedFixed(variable); variable.Pkg() != pv.pass.Pkg && (fact == nil || !fact.Boxed[variable.Name()]) {
		return
	}
	why := pv.addressUseWhy(stack)
	if why == "" {
		return
	}
	if pv.openAt[variable] == "" {
		pv.openAt[variable] = why
	}
	if variable.Pkg() != pv.pass.Pkg {
		position := pv.pass.Fset.Position(pos)
		pv.writes = append(pv.writes, sentinelWrite{
			Key: errorKey(variable) + closedKey, Name: variable.Pkg().Name() + "." + variable.Name(), Package: pv.pass.Pkg.Path(),
			At: fmt.Sprintf("%s:%d", filepath.Base(position.Filename), position.Line), pos: pos,
		})
	}
}

// closedWhy says why the address of a kind-3 variable of this package is
// not closed, or "" when it is.
func (pv *pkgVerifier) closedWhy(variable *types.Var) string {
	if why := pv.openAt[variable]; why != "" {
		return why
	}
	if write, ok := pv.writtenInBuild()[errorKey(variable)+closedKey]; ok {
		return fmt.Sprintf("its address is let out at %s in package %s, which this package is built with", write.At, write.Package)
	}
	return ""
}

// apartFromClosed states that an allocation is none of the struct variables
// whose address is closed that the function met, relying on each being
// closed, or returns nil when there are none.
func (v *fnVerifier) apartFromClosed(alloc *logic.Term) *logic.Term {
	var apart []*logic.Term
	for _, key := range slices.Sorted(maps.Keys(v.boxedMet)) {
		variable := v.boxedMet[key]
		if variable.Pkg() != v.pass.Pkg || v.closedWhy(variable) != "" {
			continue
		}
		v.reliedKeys[key+closedKey] = true
		apart = append(apart, logic.Not(logic.Eq(alloc, boxRef(variable))))
	}
	if len(apart) == 0 {
		return nil
	}
	return logic.And(apart...)
}

// foreignBoxedWhy says why a kind-3 variable of another package cannot be
// read or named here (O-d of the design of F32).
func (pv *pkgVerifier) foreignBoxedWhy(variable *types.Var) string {
	return fmt.Sprintf("%s is a struct variable of package %s whose address is taken, and reading or naming one of another package "+
		"is not supported yet; a function of package %s can read it, and a contract here covers what such a function changes "+
		"by listing the state of package %s", pv.spelling(variable), variable.Pkg().Path(), variable.Pkg().Name(), variable.Pkg().Name())
}
