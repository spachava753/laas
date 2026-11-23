package vego

import (
	"maps"
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"slices"
	"strings"

	"github.com/spachava753/laas/vego/internal/logic"
)

// An interface value other than an error is one reference, zero exactly
// for the nil interface. Which type it holds, and what value of that type,
// is not modelled, so code can compare two interface values only with nil:
// Go's == on two interface values compares the dynamic types and then the
// values, and panics when both hold the same type and that type is not
// comparable, and none of that can be decided without the dynamic types.
// A formula can also compare two of them by =, which is identity, as for
// errors: the same value, one copied from the other. Each conversion makes
// a reference that differs from those of the other conversions of the
// function, so two conversions of one concrete value are two values, where
// Go's == may say they are equal. When dynamic types bring == to code, it
// gets a term of its own, and = in a formula keeps this meaning.
//
// Converting a concrete value to an interface gives a reference that is
// not zero, also for a nil pointer, which in Go makes an interface that is
// not nil. Converting one interface value to another keeps the reference,
// so the nil interface stays nil.

// ifaceCompared is the message for == and != on interface values with
// anything but nil.
const ifaceCompared = "comparing interface values is not supported yet: == compares the types and values they hold, " +
	"which are not known, and panics when both hold the same type and it is not comparable; compare with nil instead"

// ifaceAsserted is the message for type assertions and type switches.
const ifaceAsserted = "type assertions and type switches are not supported yet: the type an interface value holds is not known"

// interfaceValue evaluates an expression that is assigned to something of
// an interface type other than error, where Go converts it to that type.
func (v *fnVerifier) interfaceValue(e ast.Expr, want types.Type, st *state, guard []*logic.Term) value {
	from := v.info.TypeOf(e)
	switch {
	case types.Identical(from, want):
		return v.eval(e, st, guard)
	case isIface(from):
		// The value keeps its methods, so a method of want must be one of
		// them, the very declaration, and so with the same contract.
		// A method of want that is not a declaration the value has must be
		// implied by the contract of the value's own method of the name
		// (F28): the value keeps its reference, so its home, its footprint,
		// and its states.
		v.convertByContract(e, from, want, st, guard)
		return v.eval(e, st, guard)
	case isError(from):
		if want.Underlying().(*types.Interface).NumMethods() > 0 {
			v.unsupported(e.Pos(), fmt.Sprintf("converting an error to %s is not supported; only any can hold an error", want))
		}
		// The nil error becomes the nil interface, and any other error an
		// interface value that is not nil.
		err := v.eval(e, st, guard)[0]
		v.held[ast.Unparen(e)] = value{err}
		held := v.fresh("iface", logic.Ref)
		st.assume(logic.Iff(logic.Eq(held, logic.RefLit(0)), logic.IsNil(err)))
		return value{held}
	case types.IsInterface(from):
		v.unsupported(e.Pos(), fmt.Sprintf("converting a %s to %s is not supported", from, want))
	}
	// An interface without methods can hold anything. Nothing can be done
	// with what it holds but pass it on. Each method of any other
	// interface is checked against its contract, for the value as it is
	// here.
	// A value converted to an interface whose methods may write behind
	// their receiver gets a footprint: none for a value whose methods write
	// nothing, and otherwise what they may write of what it holds, its
	// structural footprint, fixed at the conversion.
	footprinted := false
	var behind *types.Func
	if method := v.stateSpeaker(want); method != nil && (!v.hasStates(want) || v.hasFootprint(want)) {
		if behind = v.writingImplementation(from, want); behind != nil {
			if why := wrapsKept(from); why != "" {
				shown := func(t types.Type) string { return types.TypeString(t, types.RelativeTo(v.pass.Pkg)) }
				v.unsupported(e.Pos(), fmt.Sprintf("converting a value of type %s to %s is not supported yet: %s", shown(from), shown(want), why))
			}
			if why := growsUnbounded(from); why != "" {
				shown := func(t types.Type) string { return types.TypeString(t, types.RelativeTo(v.pass.Pkg)) }
				v.unsupported(e.Pos(), fmt.Sprintf("converting a value of type %s to %s is not supported: %s", shown(from), shown(want), why))
			}
			object, isPointer := pointee(from)
			if !isPointer {
				object = from
			}
			if through := ownsIfaceThrough(object, "", map[types.Type]bool{}); through != "" {
				shown := func(t types.Type) string { return types.TypeString(t, types.RelativeTo(v.pass.Pkg)) }
				v.unsupported(e.Pos(), fmt.Sprintf("converting a value of type %s to %s is not supported yet: %s owns an interface value through %s, "+
					"and what that value writes is not yet placed in the footprint of the conversion; own the interface value in %s itself, "+
					"or call the methods of %s on the pointer", shown(from), shown(want), shown(from), through, shown(object), shown(from)))
			}
			if shipped, _ := ownsDeclOf(object); v.ownsMemory(from) && shipped != nil {
				// A shipped owner itself is not converted: the bufio types
				// call through what they keep and the buffers grow without
				// a bound, which the refusals above say; any other shipped
				// owner keeps this refusal. An owner of the project, and a
				// struct of the project that holds a shipped owner by
				// value, are converted with what they own (step 4).
				shown := func(t types.Type) string { return types.TypeString(t, types.RelativeTo(v.pass.Pkg)) }
				how := "as through a strings.Builder or a bytes.Buffer it holds"
				if object, isPointer := pointee(from); isPointer && len(sourceOwnedFields(object)) > 0 {
					how = "as its // @Owns declaration says"
				}
				v.unsupported(e.Pos(), fmt.Sprintf("converting a value of type %s to %s is not supported yet: %s owns memory, %s, "+
					"and what that memory grows to is not part of the footprint fixed at the conversion; "+
					"call the methods of %s on the pointer instead", shown(from), shown(want), shown(from), how, shown(from)))
			}
		}
		footprinted = true
	}
	// The states of a value verified code makes are ghost: no method of it
	// reads them, and the method check chooses the state after a call that
	// changes them (madeAs). They start False (F28).
	ghost := v.stateSpeaker(want) != nil && v.hasStates(want)
	converted := v.evalConverted(e, want, st, guard)
	v.held[ast.Unparen(e)] = converted
	if want.Underlying().(*types.Interface).NumMethods() > 0 {
		v.madeInterface(e, converted, from, want, st, guard)
	}
	held := v.fresh("iface", logic.Ref)
	st.assume(logic.Ne(held, logic.RefLit(0)))
	// Each conversion makes a value of its own, which is not any value
	// another conversion of the function made, even of the same concrete
	// value: in a formula, two interface values are the same value only
	// when one was copied from the other.
	for _, other := range v.converted {
		st.assume(logic.Ne(held, other))
	}
	v.converted = append(v.converted, held)
	if ghost && !footprinted {
		// A home of its own, at which its states lie.
		at := v.alloc(st, true)
		st.assume(logic.Eq(home(held), at))
		v.falseStates(st, at, want)
	}
	if footprinted {
		// Its home is new, and its row is what its methods may write: the
		// invariant of rows. Later the row is a row like any other: what
		// an owner makes after the conversion is new memory, which no fact
		// keeps out of a row.
		at := v.alloc(st, true)
		st.assume(logic.Eq(home(held), at))
		if ghost {
			v.falseStates(st, at, want)
		}
		var defines func(alloc, pos *logic.Term) (*logic.Term, []*logic.Term)
		if behind != nil {
			defines = v.structuralFootprint(nil, maps.Clone(st.mem), converted, from)
			if v.ownsMemory(from) {
				v.convertsOwner = true
				if _, isPointer := pointee(from); isPointer {
					v.convertedOwners = append(v.convertedOwners, converted)
					v.convertedOwnerTypes = append(v.convertedOwnerTypes, from)
				}
			}
			if object, isPointer := pointee(from); isPointer && isStructType(object) {
				v.convertedStructs = append(v.convertedStructs, structValue{t: object, ref: converted[0], at: converted[1]})
			}
			text := types.ExprString(ast.Unparen(e))
			memory := "the memory that " + text + " points to"
			switch {
			case isSlice(from):
				memory = "the array that " + text + " holds, up to its capacity"
			case isMap(from):
				memory = "the map " + text
			}
			remedy := "list " + text + " in a // @Modifies clause"
			if _, isCall := ast.Unparen(e).(*ast.CallExpr); isCall {
				// A call cannot be listed.
				memory += ", which the call returned without saying that it is new, so it may be memory of the caller"
				remedy = "take it as a parameter and list it in a // @Modifies clause, or have the contract of the call say that it is new"
			} else if why := v.notListable(e, e.Pos()); why != "" {
				remedy = why
			}
			v.convertedAt[held.Name] = conversion{text: text, memory: memory, remedy: remedy, at: e.Pos()}
		}
		// A layer of the footprint region in which the row of that home
		// holds what defines says and every other row is what it was;
		// rowAt states it of each cell it reads.
		defined := v.fresh("mem'"+footprintRegion, footprintSort)
		v.layers[defined.Name] = &layer{prev: st.mem.region(footprintRegion, footprintSort), key: footprintRegion, growth: true, emptied: at, defines: defines}
		st.mem[footprintRegion] = defined
	}
	return value{held}
}

// writingImplementation returns a method of the interface want that writes
// behind its receiver and that the method of from which implements it may
// do as well: its contract lists a path from its receiver in Modifies, or
// it has none that can be read. It returns nil when no such method writes
// what its receiver reaches; what one writes beyond that is checked
// against the contract of the interface, as for any conversion.
func (v *fnVerifier) writingImplementation(from, want types.Type) *types.Func {
	for method := range want.Underlying().(*types.Interface).Methods() {
		if !v.footprintMethod(method) {
			continue
		}
		selection := types.NewMethodSet(from).Lookup(method.Pkg(), method.Name())
		if selection == nil {
			return method
		}
		impl, ok := selection.Obj().(*types.Func)
		if !ok {
			return method
		}
		fn := v.contractOf(impl)
		if fn == nil {
			return method
		}
		recv := impl.Type().(*types.Signature).Recv()
		for _, m := range fn.modifies {
			if recv == nil || m.name == recv.Name() {
				return method
			}
		}
	}
	return nil
}

// evalConverted evaluates an expression that Go converts to the interface
// type target here; see conversions.go. The walk that lists the
// conversions must have listed this one with that target.
func (v *fnVerifier) evalConverted(e ast.Expr, target types.Type, st *state, guard []*logic.Term) value {
	inner := ast.Unparen(e)
	if !slices.ContainsFunc(v.findConversions().converted[inner], func(t types.Type) bool { return types.Identical(t, target) }) {
		panic(fmt.Sprintf("internal error: %s at %s is checked as a conversion to %s, which the list of conversions does not have there",
			types.ExprString(e), v.pass.Fset.Position(e.Pos()), target))
	}
	v.converting[inner]++
	defer func() { v.converting[inner]-- }()
	return v.eval(e, st, guard)
}

// madeInterface checks every method of the interface want, for a value of
// the concrete type from that the expression e gives, against the contract
// of the method. A method is checked as a method value whose receiver is
// what the interface value holds: the value as it is here, which an
// interface keeps for as long as it lives, or, for a method with a value
// receiver of what a pointer points to, the struct read when the method
// runs, from memory the check knows nothing about.
func (v *fnVerifier) madeInterface(e ast.Expr, held value, from, want types.Type, st *state, guard []*logic.Term) {
	iface := want.Underlying().(*types.Interface)
	for method := range iface.Methods() {
		T := v.methodContract(method)
		if T == nil {
			v.unsupported(e.Pos(), fmt.Sprintf("converting a %s to %s is not supported: its method %s has no contract, so nothing would say "+
				"what code that calls it may rely on%s", from, want, methodTitle(method), v.entryHint(method.Pkg(), method.Pos(), method.FullName())))
		}
		v.usable(e.Pos(), T, methodTitle(method), st, guard, false)
	}
	for method := range iface.Methods() {
		concrete, why := concreteMethod(from, method.Pkg(), method.Name(), v.pass.Pkg)
		if why != "" {
			v.unsupported(e.Pos(), why)
		}
		recv := concrete.Type().(*types.Signature).Recv().Type()
		_, fromPointer := from.Underlying().(*types.Pointer)
		_, recvPointer := recv.(*types.Pointer)
		title := methodOf(recv, concrete, v.pass.Pkg)
		site := v.site(e.Pos(), "in %s used as a method of %s at %s", title, types.TypeString(want, types.RelativeTo(v.pass.Pkg)), v.placeOf(e.Pos()))
		fun := &ast.SelectorExpr{X: e, Sel: &ast.Ident{NamePos: e.End(), Name: concrete.Name()}}
		v.madeAs(e, fun, v.methodContract(method), concrete, "a method of "+types.TypeString(want, types.RelativeTo(v.pass.Pkg)), "an interface value", site,
			func(sv *fnVerifier, entry *state, carry *transport) value {
				kept := carry.value(held)
				sv.placeFootprint(entry, v.methodContract(method), kept, from)
				if !fromPointer || recvPointer {
					return kept
				}
				// Go reads what the pointer points to each time the method
				// runs, and panics if it is nil.
				sv.check(entry, nil, logic.Ne(kept[0], logic.RefLit(0)), e.Pos(),
					"%s has a value receiver, and the pointer that the interface value holds may be nil", title)
				object := from.Underlying().(*types.Pointer).Elem()
				read := sv.fetch(entry, entry.mem, sv.cellsOf(object), kept[0], kept[1])
				sv.noteTyped(entry, read, object)
				return read
			}, st, guard)
	}
}

// concreteMethod returns the method of a concrete type that a call through
// an interface value holding a value of the type runs, or says why it
// cannot be used as a method of an interface: one promoted from an
// embedded field, and one promoted from an embedded field that holds an
// interface value, which calls through that value. A conversion and the
// routes of encoding/json that call a writer's Write or a reader's Read on
// the value as it is (json.go, jsondecode.go) choose it here.
func concreteMethod(from types.Type, pkg *types.Package, name string, here *types.Package) (*types.Func, string) {
	shown := types.TypeString(from, types.RelativeTo(here))
	selection := types.NewMethodSet(from).Lookup(pkg, name)
	if selection == nil {
		return nil, fmt.Sprintf("%s has no method %s", shown, name)
	}
	concrete := selection.Obj().(*types.Func)
	switch {
	case isIfaceMethod(concrete):
		// A method promoted from an embedded interface field calls
		// through that field.
		return concrete, fmt.Sprintf("%s gets %s from an embedded field that holds an interface value, so it calls through that value, "+
			"and code that an interface value runs cannot do that yet: no contract of a method of an interface has a variant, "+
			"so nothing would prove that such calls end", shown, name)
	case len(selection.Index()) > 1:
		return concrete, fmt.Sprintf("%s gets %s from an embedded field, and a promoted method cannot be used as a method of an interface yet",
			shown, name)
	}
	return concrete, ""
}

// methodOf names a method of a concrete type in messages, as in
// (*Table).Price or Level.String.
func methodOf(recv types.Type, method *types.Func, pkg *types.Package) string {
	shown := types.TypeString(recv, types.RelativeTo(pkg))
	if _, isPointer := recv.(*types.Pointer); isPointer {
		shown = "(" + shown + ")"
	}
	return shown + "." + method.Name()
}

// foreignMethod returns a method of the interface want that the interface
// from does not have as the same declaration, or nil if there is none.
func (v *fnVerifier) foreignMethod(from, want types.Type) *types.Func {
	have := from.Underlying().(*types.Interface)
	need := want.Underlying().(*types.Interface)
	for method := range need.Methods() {
		found := false
		for own := range have.Methods() {
			if own == method {
				found = true
				break
			}
		}
		if !found {
			return method
		}
	}
	return nil
}

// A contract of an interface method is written in the doc comment of the
// method, in the declaration of a defined interface type:
//
//	type Pricer interface {
//		// @Requires 0 <= qty <= 1000
//		// @Ensures ok -> 0 <= cents
//		Price(sku string, qty int) (cents int, ok bool)
//	}
//
// It has Requires, Ensures, and Modifies over the parameters and results of
// the method, as the contract of a function type has; the receiver has no
// name, so nothing behind it can be listed. A contract is read only on a
// method declared in a package-level type declaration that is not an alias
// and has no type parameters. Two interface literals with the same methods
// are identical types with methods of their own, so a contract on one
// would let a value checked against it reach the other unchecked, which no
// conversion would notice. A defined type made from another interface type,
// as in type B A, has the methods of A, and so their contracts.

// methodDocumented reports whether a comment group is the doc comment of a
// method or an embedded type in an interface type of the file. It returns
// the method, nil for an embedded type, and whether the interface is one a
// contract can be declared on.
func (pv *pkgVerifier) methodDocumented(file *ast.File, group *ast.CommentGroup) (method *types.Func, defined, found bool) {
	contractable := map[*ast.InterfaceType]bool{}
	for _, decl := range file.Decls {
		gen, ok := decl.(*ast.GenDecl)
		if !ok || gen.Tok != token.TYPE {
			continue
		}
		for _, spec := range gen.Specs {
			spec := spec.(*ast.TypeSpec)
			if iface, ok := spec.Type.(*ast.InterfaceType); ok && !spec.Assign.IsValid() && spec.TypeParams == nil {
				contractable[iface] = true
			}
		}
	}
	ast.Inspect(file, func(n ast.Node) bool {
		iface, ok := n.(*ast.InterfaceType)
		if !ok || found {
			return !found
		}
		for _, field := range iface.Methods.List {
			if field.Doc != group {
				continue
			}
			found, defined = true, contractable[iface]
			if len(field.Names) == 1 {
				method, _ = pv.info.Defs[field.Names[0]].(*types.Func)
			}
			return false
		}
		return true
	})
	return method, defined, found
}

// addMethodContract records an annotation written in the doc comment of a
// method in an interface type.
func (pv *pkgVerifier) addMethodContract(method *types.Func, defined bool, c *clause) {
	switch {
	case method == nil:
		pv.unread = true
		pv.report(c.pos, "a contract cannot be written on an embedded interface; write it on the methods where they are declared")
		return
	case !defined:
		pv.unread = true
		pv.report(c.pos, "a contract can only be declared on a method of a defined interface type at package level without type parameters, "+
			"not on an interface literal or an alias: two interface literals with the same methods are the same type, and a value would carry either contract")
		return
	case c.kind != "Requires" && c.kind != "Ensures" && c.kind != "Modifies" && c.kind != "Receiver" && c.kind != "Vouches":
		pv.unread = true
		pv.report(c.pos, "%s annotations do not belong on a method of an interface; it can only have Receiver, Requires, Ensures, Modifies, and Vouches annotations", c.kind)
		return
	}
	fn := pv.ifaceMethods[method]
	if fn == nil {
		fn = newFuncInfo(withoutReceiver(method))
		fn.methodOf = method
		pv.ifaceMethods[method] = fn
	}
	if c.kind == "Receiver" {
		if problem := fn.setReceiver(strings.TrimSpace(c.text), method); problem != "" {
			pv.report(c.pos, "in Receiver annotation: %s", problem)
			fn.broken = true
		}
		return
	}
	pv.addValueClause(fn, c)
}

// withoutReceiver returns a function with the parameters and results of a
// method, but no receiver: what the contract of an interface method speaks
// of. It is named after the interface and the method, as in Pricer.Price,
// which is how messages about the contract name it.
func withoutReceiver(method *types.Func) *types.Func {
	sig := method.Type().(*types.Signature)
	plain := types.NewSignatureType(nil, nil, nil, sig.Params(), sig.Results(), sig.Variadic())
	return types.NewFunc(method.Pos(), method.Pkg(), methodTitle(method), plain)
}

// methodTitle names a method of an interface type in messages, as in
// Pricer.Price.
func methodTitle(method *types.Func) string {
	if recv := method.Type().(*types.Signature).Recv(); recv != nil {
		if named, ok := types.Unalias(recv.Type()).(*types.Named); ok {
			return named.Obj().Name() + "." + method.Name()
		}
	}
	return method.Name()
}

// methodContract returns the contract of a method of an interface type, or
// nil if it has none.
func (pv *pkgVerifier) methodContract(method *types.Func) *funcInfo {
	if method.Pkg() == pv.pass.Pkg {
		if fn := pv.ifaceMethods[method]; fn != nil {
			return fn
		}
		return pv.entryMethod(method)
	}
	if fn, done := pv.importedMethods[method]; done {
		return fn
	}
	pv.importedMethods[method] = nil
	fact := &contractFact{}
	if method.Pkg() == nil || !pv.pass.ImportObjectFact(method, fact) {
		fn := pv.entryMethod(method)
		pv.importedMethods[method] = fn
		return fn
	}
	fn := pv.contractFromFact(withoutReceiver(method), method.Pkg(), fact)
	if fact.Receiver != "" {
		if problem := fn.setReceiver(fact.Receiver, method); problem != "" {
			fn.defect("its receiver: %s", problem)
		}
	}
	if !fact.Verified {
		fn.defects = []string{fmt.Sprintf("the annotations of package %s were not all read", method.Pkg().Path())}
	}
	if pv.entryFor(method.FullName()) != nil {
		fn.defect("it has a contract where it is declared and also an entry %s in the trust file", method.FullName())
	}
	fn.methodOf = method
	pv.importedMethods[method] = fn
	return fn
}

// checkDroppedContracts reports an interface type that embeds or declares
// a method with a contract that is not part of it: when an interface gets a
// method of one name from two declarations, Go keeps one of them, and the
// contract of the other would be skipped without a word.
func (pv *pkgVerifier) checkDroppedContracts() {
	for _, file := range pv.pass.Files {
		ast.Inspect(file, func(n ast.Node) bool {
			node, ok := n.(*ast.InterfaceType)
			if !ok {
				return true
			}
			t, ok := pv.info.TypeOf(node).(*types.Interface)
			if !ok {
				return true
			}
			kept := map[string]*types.Func{}
			for method := range t.Methods() {
				kept[method.Name()] = method
			}
			var visit func(iface *types.Interface, seen map[*types.Interface]bool)
			visit = func(iface *types.Interface, seen map[*types.Interface]bool) {
				if seen[iface] {
					return
				}
				seen[iface] = true
				for method := range iface.ExplicitMethods() {
					if have := kept[method.Name()]; have != nil && have != method && pv.methodContract(method) != nil {
						pv.report(node.Pos(), "the contract of %s is not part of this interface: it has %s from %s, "+
							"and Go keeps one declaration of a method; declare the method once, with its contract",
							methodTitle(method), method.Name(), methodTitle(have))
					}
				}
				for embedded := range iface.EmbeddedTypes() {
					if inner, ok := embedded.Underlying().(*types.Interface); ok {
						visit(inner, seen)
					}
				}
			}
			visit(t, map[*types.Interface]bool{})
			return true
		})
	}
}

// isIfaceMethod reports whether a function is a method of an interface
// type, which a call reaches through an interface value.
func isIfaceMethod(callee *types.Func) bool {
	if callee == nil {
		return false
	}
	recv := callee.Type().(*types.Signature).Recv()
	return recv != nil && types.IsInterface(recv.Type())
}

// usableMethodContract returns the contract that a call of a method through
// an interface value is checked against, and the selector of the call, or
// stops the verification when the call is not of that form or the method
// has no contract that can be used.
func (v *fnVerifier) usableMethodContract(call *ast.CallExpr, callee *types.Func, st *state, guard []*logic.Term) (*funcInfo, *ast.SelectorExpr) {
	sel, _ := ast.Unparen(call.Fun).(*ast.SelectorExpr)
	var selection *types.Selection
	if sel != nil {
		selection = v.info.Selections[sel]
	}
	switch {
	case selection == nil || selection.Kind() != types.MethodVal:
		v.unsupported(call.Pos(), "a method expression, as in I.M(x), cannot be called yet; call the method on the value, as in x.M()")
	case len(selection.Index()) > 1:
		v.unsupported(call.Pos(), fmt.Sprintf("%s is a method of an interface value that %s holds in an embedded field; "+
			"calling it through %s is not supported yet; call it on the field", callee.Name(), types.ExprString(sel.X), types.ExprString(sel.X)))
	case !isIface(selection.Recv()):
		// The type of the value decides, and not the interface that
		// declares the method: an interface literal that embeds it is not
		// modelled.
		v.unsupported(call.Pos(), fmt.Sprintf("calling %s, a method of %s, is not supported yet%s", callee.Name(), selection.Recv(), unsupportedHint(selection.Recv())))
	}
	fn := v.methodContract(callee)
	if fn == nil {
		v.unsupported(call.Pos(), fmt.Sprintf("%s calls %s, which has no contract; a method of an interface gets one in its doc comment "+
			"where the interface is declared, with // @ annotations%s", types.ExprString(call.Fun), methodTitle(callee), v.entryHint(callee.Pkg(), callee.Pos(), callee.FullName())))
	}
	fn = v.usable(call.Pos(), fn, methodTitle(callee), st, guard, true)
	// The proof rests on which states the value has, or on it having none,
	// whatever the method says of them; see fileStates.
	v.ifaceStatesOf(selection.Recv())
	return fn, sel
}

// callMethod verifies a call of a method through an interface value. The
// interface value and the arguments are evaluated before the call, which is
// an event of the unit like any call; then the value must not be the nil
// interface, and the contract of the method applies. Which method runs
// depends on what the value holds: one that verified code converted was
// checked against the contract there, and any other is taken to meet it.
func (v *fnVerifier) callMethod(call *ast.CallExpr, callee *types.Func, st *state, guard []*logic.Term) []value {
	if isErrorText(v.info, call) {
		return v.errorText(call, st, guard)
	}
	fn, sel := v.usableMethodContract(call, callee, st, guard)
	u := v.unit
	operands := u.pushCeiling()
	held, args := v.methodOperands(call, sel, fn, st, guard)
	u.reach(operands)
	v.check(st, guard, logic.Ne(held[0], logic.RefLit(0)), call.Pos(), "the interface value %s may be nil", types.ExprString(sel.X))
	results := v.invoke(call, fn, args, st, guard)
	u.calls = append(u.calls, unitCall{name: types.ExprString(call.Fun), pos: call.Pos(),
		pure: v.callMemoryFree(fn, fn.obj.Type().(*types.Signature))})
	u.event()
	return results
}

// methodOperands evaluates the interface value of a method call and its
// arguments, and refuses an argument that carries code nobody has seen.
func (v *fnVerifier) methodOperands(call *ast.CallExpr, sel *ast.SelectorExpr, fn *funcInfo, st *state, guard []*logic.Term) (value, map[*types.Var]value) {
	bound := v.bindParams(call, fn)
	held := v.eval(sel.X, st, guard)
	args := map[*types.Var]value{}
	if fn.receiver != nil {
		// The contract speaks of the states of the value it is called on.
		args[fn.receiver] = held
	}
	for _, passed := range bound {
		args[passed.param] = v.evalPassed(passed, st, guard)
	}
	v.checkHandedToValue(call, fn, "the method "+types.ExprString(call.Fun))
	return held, args
}

// deferMethod executes the defer of a call of a method through an interface
// value: the value and the arguments are settled now, and the call runs when
// the frame returns. Go takes the method of the value at the defer
// statement, which panics there for the nil interface.
func (v *fnVerifier) deferMethod(s *ast.DeferStmt, callee *types.Func, st *state) {
	fn, sel := v.usableMethodContract(s.Call, callee, st, nil)
	var held value
	var args map[*types.Var]value
	v.evaluate(st, func() {
		defer v.begin()()
		held, args = v.methodOperands(s.Call, sel, fn, st, nil)
	})
	v.check(st, nil, logic.Ne(held[0], logic.RefLit(0)), s.Call.Pos(), "the interface value %s may be nil", types.ExprString(sel.X))
	st.deferred = append(slices.Clip(st.deferred), deferredCall{call: s.Call, fn: fn, args: args})
}

// fullyContracted reports whether every method of an interface type has a
// contract that can be used. A value of such a type runs only code that
// meets those contracts: code that verified code converted, which was
// checked there, or code from elsewhere, which is taken to meet them.
func (pv *pkgVerifier) fullyContracted(t types.Type) bool {
	if !isIface(t) {
		return false
	}
	iface := t.Underlying().(*types.Interface)
	if iface.NumMethods() == 0 {
		return false
	}
	for method := range iface.Methods() {
		if fn := pv.methodContract(method); fn == nil || fn.broken {
			return false
		}
	}
	return true
}

// conversion is where a value with a structural footprint was converted to
// an interface value, for messages: the expression converted, and the
// memory its footprint is, in words.
type conversion struct {
	text, memory, remedy string
	at                   token.Pos
}

// placeFootprint states, in the check of a method of a value made into an
// interface value whose contract lets it write behind its receiver, that
// the structural footprint of what the value holds lies in the row of the
// receiver. It holds at every call: at the conversion the row is that
// footprint, and rows keep the cells of memory that existed then, which
// the struct is.
func (v *fnVerifier) placeFootprint(entry *state, T *funcInfo, kept value, from types.Type) {
	if T == nil || T.receiver == nil || !v.hasFootprint(T.receiver.Type()) {
		return
	}
	defines := v.structuralFootprint(entry, entry.mem, kept, from)
	if v.heldReceiver != nil {
		name, shown := v.heldReceiver.Name(), types.TypeString(from, types.RelativeTo(v.pass.Pkg))
		_, isPointer := pointee(from)
		switch {
		case isPointer:
			v.heldRemedy = fmt.Sprintf("it is not part of the footprint of %s, which is the struct %s points to", shown, name)
		case isSlice(from):
			v.heldRemedy = fmt.Sprintf("it is not part of the footprint of %s, which is the array %s holds, up to its capacity", shown, name)
		case isMap(from):
			v.heldRemedy = fmt.Sprintf("it is not part of the footprint of %s, which is the map %s is", shown, name)
		default:
			v.heldRemedy = fmt.Sprintf("it is not part of the footprint of %s, which is empty: a value held by value is copied for each call of its methods, "+
				"and owns nothing its fields point to; keep what the method writes in a struct and convert a pointer to it, or pass what it writes as an argument", shown)
		}
	}
	if defines == nil {
		return
	}
	a, k := v.bound("a"), v.bound("k")
	inside, facts := defines(a, k)
	cell, more := v.rowAt(entry.mem.region(footprintRegion, footprintSort), home(v.entry[T.receiver][0]), a, k)
	entry.assume(logic.Forall(a, logic.Forall(k, logic.Implies(inside, logic.And(append(append(facts, more...), cell)...)))))
}

// wrapsKept says why a value of a shipped type that calls through what it
// keeps cannot be converted to an interface yet, with what to write
// instead, or returns "". Its Write or Read calls through the writer or
// the reader it keeps, and nothing proves yet that calls through values
// that wrap values end (item 12 of the roadmap).
func wrapsKept(t types.Type) string {
	object, isPointer := pointee(t)
	named, ok := object.(*types.Named)
	if !isPointer || !ok || named.Obj().Pkg() == nil {
		return ""
	}
	switch named.Obj().Pkg().Path() + "." + named.Obj().Name() {
	case "bufio.Writer":
		return "its Write calls through the writer it keeps, and nothing proves yet that calls through values that wrap values end; " +
			"pass the Writer itself to fmt.Fprintf, Fprint, or Fprintln, which then calls its own Write, or format into a string, as with fmt.Sprintf, " +
			"and pass it to the Writer's own Write as []byte(s)"
	case "bufio.Reader":
		return "its Read calls through the reader it keeps, and nothing proves yet that calls through values that wrap values end; " +
			"read with the Reader's own methods, such as ReadByte"
	}
	return ""
}

// growingMethods are the methods of bytes.Buffer and strings.Builder that
// may grow the buffer and have no shipped entry.
var growingMethods = map[string]bool{"ReadFrom": true}

// growsUnbounded says why a buffer, a value of bytes.Buffer or
// strings.Builder, cannot be converted to an interface whose methods write
// behind their receiver, or returns "".
func growsUnbounded(t types.Type) string {
	if object, isPointer := pointee(t); isPointer {
		t = object
	}
	named, ok := t.(*types.Named)
	if !ok || named.Obj().Pkg() == nil {
		return ""
	}
	switch named.Obj().Pkg().Path() + "." + named.Obj().Name() {
	case "bytes.Buffer", "strings.Builder":
		return fmt.Sprintf("its Write may panic when the buffer is too large to grow, and the contract of (io.Writer).Write has no bound for it; "+
			"pass the %s itself to fmt.Fprintf, Fprint, or Fprintln, which then calls its own Write, or write what you format with its own WriteString, "+
			"as in b.WriteString(fmt.Sprintf(...))", named.Obj().Name())
	}
	return ""
}

// isErrorText reports whether a call is err.Error() on a value of type
// error.
func isErrorText(info *types.Info, call *ast.CallExpr) bool {
	sel, ok := ast.Unparen(call.Fun).(*ast.SelectorExpr)
	if !ok || len(call.Args) != 0 {
		return false
	}
	selection := info.Selections[sel]
	return selection != nil && selection.Kind() == types.MethodVal && sel.Sel.Name == "Error" && isError(selection.Recv())
}

// errorText verifies err.Error() (F28): the error must be of an origin
// that formatting accepts, whose Error method returns and writes nothing
// verified code can see, and not nil. The text is a string about which one
// thing is known, what What a proof assumes says of the text of an error:
// that it can be printed on a line of its own, 2 * (|s| + 4096) + 65536 <=
// MaxAlloc. errors.New requires it of its text and fmt.Errorf proves it of
// what it builds, so verified code cannot make it false where the logic
// has a term for the length; what stays assumed is the text of errors from
// code that is not verified and the parts of a wrapped error that have none.
func (v *fnVerifier) errorText(call *ast.CallExpr, st *state, guard []*logic.Term) []value {
	sel := ast.Unparen(call.Fun).(*ast.SelectorExpr)
	if !v.knownError(v.bodyOrigins(), sel.X, -1) {
		v.unsupported(call.Pos(), fmt.Sprintf("calling Error on %s would run the methods of an error whose origin is not known; "+
			"only an error made by errors.New or fmt.Errorf, here or in a verified function, or one that a contract vouches for, "+
			"can be asked for its text%s", types.ExprString(sel.X), v.originWhy(sel.X)))
	}
	u := v.unit
	operands := u.pushCeiling()
	err := v.eval(sel.X, st, guard)
	u.reach(operands)
	v.check(st, guard, logic.Not(logic.IsNil(err[0])), call.Pos(), "the error %s may be nil", types.ExprString(sel.X))
	text := v.unknown("text of "+types.ExprString(sel.X), types.Typ[types.String], st)
	v.noteTyped(st, text, types.Typ[types.String])
	st.assume(errorTextFits(v, text[0]))
	u.calls = append(u.calls, unitCall{name: types.ExprString(call.Fun), pos: call.Pos(), pure: true})
	u.event()
	return []value{text}
}

// errorTextFits states that a text can be printed on a line of its own:
// 2 * (|s| + 4096) + 65536 <= MaxAlloc, the bound formatting proves.
func errorTextFits(v *fnVerifier, s *logic.Term) *logic.Term {
	return logic.Le(logic.Add(logic.Mul(logic.Add(logic.Len(s), logic.IntLit(fmtSlack)), logic.IntLit(2)), logic.IntLit(1<<16)), logic.BigLit(v.maxAlloc()))
}

// falseStates writes the states of a value converted to an interface with
// states at its new home: each is False, as an allocation zeroes the
// states of a struct (F9 of the design of footprints), and the row of
// every other home is what it was.
func (v *fnVerifier) falseStates(st *state, at *logic.Term, want types.Type) {
	row := v.fresh("states", logic.BoolSeq)
	for _, s := range v.ifaceStatesOf(want) {
		st.assume(logic.Not(logic.Select(row, s.position())))
	}
	st.storeRow(stateRegion, logic.Bool, at, row)
}

// convertByContract checks a conversion of an interface value of type from
// to want, an interface with methods from declarations the value does not
// have: each such method of want must be implied by the contract of the
// method of the same name of from, checked as a method check on one
// receiver (impliesMethod), and want must declare no state that from does
// not, nor claim less of keeping, vouching, and asserting (F28).
func (v *fnVerifier) convertByContract(e ast.Expr, from, want types.Type, st *state, guard []*logic.Term) {
	shown := func(t types.Type) string { return types.TypeString(t, types.RelativeTo(v.pass.Pkg)) }
	have := map[string]bool{}
	for _, s := range v.ifaceStatesOf(from) {
		have[s.title()] = true
	}
	for _, s := range v.ifaceStatesOf(want) {
		if !have[s.title()] {
			v.unsupported(e.Pos(), fmt.Sprintf("converting %s, %s %s, to %s is not supported: %s has the state %s, which %s does not declare, "+
				"so nothing says what it is of the value", types.ExprString(e), article(shown(from)), shown(from), shown(want), shown(want), s.name, shown(from)))
		}
	}
	own := from.Underlying().(*types.Interface)
	for method := range want.Underlying().(*types.Interface).Methods() {
		if slices.Contains(slices.Collect(own.Methods()), method) {
			continue
		}
		found, _, _ := types.LookupFieldOrMethod(from, false, method.Pkg(), method.Name())
		source, _ := found.(*types.Func)
		if source == nil {
			v.unsupported(e.Pos(), fmt.Sprintf("converting %s, %s %s, to %s is not supported: %s has no method %s", types.ExprString(e), article(shown(from)), shown(from), shown(want), shown(from), method.Name()))
		}
		TA, TB := v.methodContract(source), v.methodContract(method)
		if TA == nil || TB == nil {
			missing := source
			if TB == nil {
				missing = method
			}
			v.unsupported(e.Pos(), fmt.Sprintf("converting %s, %s %s, to %s is not supported: %s has no contract, so nothing says that %s meets %s",
				types.ExprString(e), article(shown(from)), shown(from), shown(want), methodTitle(missing), methodTitle(source), methodTitle(method)))
		}
		if why := v.claimsNoLess(TA, TB, source, method); why != "" {
			v.unsupported(e.Pos(), fmt.Sprintf("converting %s, %s %s, to %s is not supported: %s", types.ExprString(e), article(shown(from)), shown(from), shown(want), why))
		}
		v.impliesMethod(e, TA, TB, source, method, st, guard)
	}
}

// claimsNoLess says why the contract TA of a method of an interface does
// not claim of keeping, vouching, and asserting what the contract TB of a
// method of another interface claims, or "": A keeps no more than B,
// vouches for no less, and asserts no more.
func (v *fnVerifier) claimsNoLess(TA, TB *funcInfo, a, b *types.Func) string {
	keeps := func(fn *funcInfo) (map[int]bool, bool) {
		if fn.trust == nil {
			// A method of an interface declared in source may keep what
			// it is handed.
			return nil, true
		}
		kept := map[int]bool{}
		for _, k := range fn.trust.keeps {
			for i, p := range fn.params {
				if p.Name() == k.name || fn.paramNames[k.name] == p {
					kept[i] = true
				}
			}
		}
		return kept, false
	}
	keptA, allA := keeps(TA)
	keptB, allB := keeps(TB)
	for i := range TA.params {
		if !allB && (allA || keptA[i] && !keptB[i]) {
			return fmt.Sprintf("%s may keep what it is handed as its parameter %d, and %s keeps nothing there", methodTitle(a), i+1, methodTitle(b))
		}
	}
	for i := range TB.results {
		if TB.vouches[i] && !TA.vouches[i] {
			return fmt.Sprintf("%s vouches for the errors of its result %d, and %s does not", methodTitle(b), i+1, methodTitle(a))
		}
	}
	if TB.trust != nil && len(TB.trust.asserts) > 0 {
		if TA.trust == nil || len(TA.trust.asserts) == 0 {
			return fmt.Sprintf("%s claims what it finds on what it is handed, under asserts, and %s claims nothing", methodTitle(b), methodTitle(a))
		}
		listed := map[string][]string{}
		for _, k := range TB.trust.asserts {
			for _, d := range k.dests {
				listed[k.name] = append(listed[k.name], d.text)
			}
		}
		for _, k := range TA.trust.asserts {
			for _, d := range k.dests {
				if !slices.Contains(listed[k.name], d.text) {
					return fmt.Sprintf("%s may assert %s to %s, which %s does not allow", methodTitle(a), k.name, d.text, methodTitle(b))
				}
			}
		}
	}
	return ""
}

// impliesMethod checks that the contract TA of a method a of an interface
// implies the contract TB of the method b of the interface it is converted
// to: a verifier whose contract is TB calls a, with the same receiver and
// arguments, and must meet TB's Ensures and frame. The receiver is the one
// value, so its home, its footprint, and its states are the same on both
// sides.
func (v *fnVerifier) impliesMethod(e ast.Expr, TA, TB *funcInfo, a, b *types.Func, st *state, guard []*logic.Term) {
	TA = v.usable(e.Pos(), TA, methodTitle(a), st, guard, false)
	TB = v.usable(e.Pos(), TB, methodTitle(b), st, guard, false)
	site := v.site(e.Pos(), "in %s used as %s at %s", methodTitle(a), methodTitle(b), v.placeOf(e.Pos()))
	sv, entry, _ := v.subVerifier(TB, st, guard, site)
	args := map[*types.Var]value{}
	switch {
	case TA.receiver != nil && TB.receiver == nil:
		v.unsupported(e.Pos(), fmt.Sprintf("converting %s to the interface of %s is not supported: the contract of %s names its receiver, and that of %s does not, "+
			"so nothing would say what %s does to the value", types.ExprString(e), methodTitle(b), methodTitle(a), methodTitle(b), methodTitle(a)))
	case TA.receiver != nil:
		args[TA.receiver] = sv.entry[TB.receiver]
	}
	call := &ast.CallExpr{Fun: &ast.SelectorExpr{X: e, Sel: &ast.Ident{NamePos: e.End(), Name: a.Name()}}, Lparen: e.End(), Rparen: e.End()}
	if a.Type().(*types.Signature).Variadic() {
		call.Ellipsis = e.End()
	}
	for i, param := range TA.params {
		if i < len(TB.params) {
			args[param] = sv.entry[TB.params[i]]
			name := TB.params[i].Name()
			if name == "" || name == "_" {
				name = fmt.Sprintf("param%d", i+1)
			}
			call.Args = append(call.Args, &ast.Ident{NamePos: e.Pos(), Name: name})
		}
	}
	results := sv.invoke(call, TA, args, entry, nil)
	sv.atReturn(entry, results, e.Pos())
}

// article returns the indefinite article for a word as it is spoken.
func article(word string) string {
	if word != "" && strings.ContainsRune("aeiouAEIOU", rune(word[0])) {
		return "an"
	}
	return "a"
}
