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
	// A frame asks after terms and notes nothing (F20 of the review of
	// step 4); what it reads is the same constant.
	if st == nil || v.frameNames != nil {
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
	// The fact between struct values is noted where the function reads
	// the variable; a frame that asks after an annotation notes nothing
	// (F20 of the review of step 4).
	var base types.Type
	if e.v.frameNames == nil {
		base = variable.Type()
	}
	val := e.v.fetchIn(e.sink, mem, e.v.cellsOf(variable.Type()), pointer[0], pointer[1], base)
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
			// A method called on a value has its receiver first among the
			// parameters of its entry; a method expression is handed it as
			// its first argument (F16 of the review of step 3).
			index := k
			if callee.Type().(*types.Signature).Recv() != nil && !pv.methodExpression(c) {
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
	if len(fn.params) == 0 || len(fn.defects) > 0 {
		return fmt.Sprintf("its address is handed to %s at %s, whose trusted contract cannot be used", callee.Name(), where)
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
	// An entry describes what the function's own code does, and says
	// nothing of code that a parameter it does not run carries; so no other
	// parameter may carry code that could be handed the address (F15 of the
	// review of step 3). A function under calls that is handed only values
	// that hold no memory, as once.Do's f, the values it formats, and the
	// writer it prints to are what the entry describes.
	for _, q := range fn.params {
		if q == p || !holdsCode(q.Type(), map[types.Type]bool{}) {
			continue
		}
		if cb := fn.calls.get(q); cb != nil {
			for param := range cb.sig.Params().Variables() {
				if !memoryFree(param.Type()) {
					return fail(fmt.Sprintf("calls %s with a value that can hold memory", q.Name()))
				}
			}
			continue
		}
		if q == fn.formatted || q == fn.prints {
			continue
		}
		return fail(fmt.Sprintf("takes %s, which can carry code that could be handed it", q.Name()))
	}
	if fn.calls.len() > 0 && depth == 0 {
		pv.runsAt = fmt.Sprintf("%s at %s runs a function it is handed while it has the address", callee.Name(), where)
	}
	if !holdsCode(p.Type(), map[types.Type]bool{}) {
		return ""
	}
	if addr == nil || depth > 0 {
		return fail("could run code it holds")
	}
	// The address converted to an interface may be asserted to any other
	// and any method of its type run, whether or not the entry runs it;
	// only what prints claims limits that, to Write. So every method that
	// takes its receiver's address must be a sink of it (F15).
	methods := types.NewMethodSet(addr)
	for i := range methods.Len() {
		method, ok := methods.At(i).Obj().(*types.Func)
		if !ok {
			continue
		}
		if p == fn.prints && method.Name() != "Write" {
			continue
		}
		if _, pointerRecv := method.Type().(*types.Signature).Recv().Type().(*types.Pointer); !pointerRecv {
			// A value receiver gets a copy of the struct, not its address.
			continue
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
	pv.runsAt = ""
	why := pv.addressUseWhy(stack)
	if why == "" {
		// A sink that runs code while it has the address, as once.Do, keeps
		// it closed but out of a group (F4 of the design of F32).
		if pv.runsAt != "" && pv.addressRuns[variable] == "" {
			pv.addressRuns[variable] = pv.runsAt
		}
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

// isolatedCall reports whether a call is of a trusted function whose entry
// claims that it runs no code but what the call hands it, and hands it
// none: no argument and no receiver can hold code (F11 of the review of the
// design of F32). Such a call reaches no code of the package.
func (pv *pkgVerifier) isolatedCall(call *ast.CallExpr, callee *types.Func) bool {
	entry := pv.entryFor(pv.originOf(callee).FullName())
	if entry == nil || !entry.isIsolated() {
		return false
	}
	operands := slices.Clone(call.Args)
	if sel, ok := ast.Unparen(call.Fun).(*ast.SelectorExpr); ok {
		if selection := pv.info.Selections[sel]; selection != nil && selection.Kind() == types.MethodVal {
			operands = append(operands, sel.X)
		}
	}
	for _, e := range operands {
		if holdsCode(pv.info.TypeOf(e), map[types.Type]bool{}) {
			return false
		}
	}
	// An argument converted to an interface hands the callee the methods of
	// its type, which it may run, as fmt runs String and the Write of the
	// writer it prints to: each must be isolated too.
	sig := callee.Type().(*types.Signature)
	args := call.Args
	if pv.methodExpression(call) && len(args) > 0 {
		// The receiver is the first argument, and no parameter.
		args = args[1:]
	}
	for i, arg := range args {
		param := sig.Params().Len() - 1
		if i < param || !sig.Variadic() {
			param = min(i, sig.Params().Len()-1)
		}
		if param < 0 {
			break
		}
		want := sig.Params().At(param).Type()
		if sig.Variadic() && param == sig.Params().Len()-1 && !call.Ellipsis.IsValid() {
			want = want.(*types.Slice).Elem()
		}
		t := pv.info.TypeOf(arg)
		if !isIface(want) || t == nil || isIface(t) {
			continue
		}
		methods := types.NewMethodSet(t)
		for j := range methods.Len() {
			method, ok := methods.At(j).Obj().(*types.Func)
			// Code of another package cannot call an unexported method.
			if !ok || !method.Exported() && method.Pkg() != callee.Pkg() {
				continue
			}
			if isolatedPackages()[method.Pkg().Path()] {
				continue
			}
			if entry := pv.entryFor(pv.originOf(method).FullName()); entry == nil || !entry.isIsolated() {
				return false
			}
		}
	}
	return true
}

// methodExpression reports whether a call is of a method expression, as
// (*T).M(x, y), which hands the receiver as the first argument.
func (pv *pkgVerifier) methodExpression(call *ast.CallExpr) bool {
	sel, ok := ast.Unparen(call.Fun).(*ast.SelectorExpr)
	if !ok {
		return false
	}
	selection := pv.info.Selections[sel]
	return selection != nil && selection.Kind() == types.MethodExpr
}
