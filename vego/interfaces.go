package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"

	"github.com/spachava753/laas/vego/internal/logic"
)

// An interface value other than an error is one reference, zero exactly
// for the nil interface. Nothing else is known of it: which type it holds,
// and what value of that type, is not modelled, so two interface values can
// only be compared with nil, in code and in formulas. Go's == on two
// interface values compares the dynamic types and then the values, and
// panics when both hold the same type and that type is not comparable;
// none of that can be decided without the dynamic types.
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
		if method := v.foreignMethod(from, want); method != nil {
			v.unsupported(e.Pos(), fmt.Sprintf("converting %s, a %s, to %s is not supported: %s declares %s itself, "+
				"which %s does not have; an interface value can be converted only to an interface whose methods are "+
				"declarations it has, as through embedding, or to any", types.ExprString(e), from, want, want, method.Name(), from))
		}
		return v.eval(e, st, guard)
	case isError(from):
		if want.Underlying().(*types.Interface).NumMethods() > 0 {
			v.unsupported(e.Pos(), fmt.Sprintf("converting an error to %s is not supported; only any can hold an error", want))
		}
		// The nil error becomes the nil interface, and any other error an
		// interface value that is not nil.
		err := v.eval(e, st, guard)[0]
		held := v.fresh("iface", logic.Ref)
		st.assume(logic.Iff(logic.Eq(held, logic.RefLit(0)), logic.IsNil(err)))
		return value{held}
	case types.IsInterface(from):
		v.unsupported(e.Pos(), fmt.Sprintf("converting a %s to %s is not supported", from, want))
	case want.Underlying().(*types.Interface).NumMethods() > 0:
		v.unsupported(e.Pos(), fmt.Sprintf("converting a %s to the interface %s is not supported yet", from, want))
	}
	// An interface without methods can hold anything. Nothing can be done
	// with what it holds but pass it on.
	v.eval(e, st, guard)
	held := v.fresh("iface", logic.Ref)
	st.assume(logic.Ne(held, logic.RefLit(0)))
	return value{held}
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
	case c.kind != "Requires" && c.kind != "Ensures" && c.kind != "Modifies":
		pv.unread = true
		pv.report(c.pos, "%s annotations do not belong on a method of an interface; it can only have Requires, Ensures, and Modifies annotations", c.kind)
		return
	}
	fn := pv.ifaceMethods[method]
	if fn == nil {
		fn = newFuncInfo(withoutReceiver(method))
		fn.methodOf = method
		pv.ifaceMethods[method] = fn
	}
	pv.addValueClause(fn, c)
}

// withoutReceiver returns a function with the name, parameters, and results
// of a method, but no receiver: what the contract of an interface method
// speaks of.
func withoutReceiver(method *types.Func) *types.Func {
	sig := method.Type().(*types.Signature)
	plain := types.NewSignatureType(nil, nil, nil, sig.Params(), sig.Results(), sig.Variadic())
	return types.NewFunc(method.Pos(), method.Pkg(), method.Name(), plain)
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
		return pv.ifaceMethods[method]
	}
	if fn, done := pv.importedMethods[method]; done {
		return fn
	}
	pv.importedMethods[method] = nil
	fact := &contractFact{}
	if method.Pkg() == nil || !pv.pass.ImportObjectFact(method, fact) {
		return nil
	}
	fn := pv.contractFromFact(withoutReceiver(method), method.Pkg(), fact)
	if !fact.Verified {
		fn.defects = []string{fmt.Sprintf("the annotations of package %s were not all read", method.Pkg().Path())}
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
