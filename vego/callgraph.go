package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"path/filepath"
	"slices"
	"strings"

	"golang.org/x/tools/go/types/typeutil"
)

// The call graph of a package says which of its functions a call may lead
// to, for the recursion check and for the rule that a proof which used the
// contract of a function whose own proof failed establishes nothing. Its
// nodes are the functions of the package that have a body, verified,
// trusted, or neither, since code of the package that is not verified is
// visible and a call back through it has to be found, and every function
// literal that is used as a value. A literal called or deferred where it
// is written, bound to a variable that is only called, or handed to a
// trusted function under calls, is part of the function around it.
//
// An edge is resolved when the call or the use names its target: a static
// call, and a function or method named anywhere but as the function of a
// call, which whoever gets the value may call now. Every other call is
// unresolved, and goes to every target that it can reach by Go's types:
//
//   - a call of an interface method M goes to every method named M of a
//     type of the package whose signature, receiver aside, is identical,
//     by name alone when the receiver's type or the signature has type
//     parameters. The dynamic type of an interface value has the method,
//     and when it is a type of the package, or a type of another package
//     that embeds one, the method is declared on a type of the package;
//   - a call through a function value of signature S, and a range over a
//     function, goes to every function, method value, method expression,
//     and literal of the package that is used as a value of a type whose
//     signature is identical to S, by any signature when either has type
//     parameters. A function of the package gets into a value only by being
//     named, taken as a method value or expression, or written as a
//     literal, so inside the package each way is an escape the graph sees.
//     Code of another package can name only the exported functions, and the
//     methods with exported names, of a value of any type it gets from the
//     package, so those are escapes too;
//   - a call of a function of another package runs code that its
//     arguments, its receiver among them, can hold at any depth: a function
//     value of signature S goes as a call through a value of S does; an
//     interface value of type I goes to I's methods as a call of each does,
//     and to every method with an exported name of every type of the
//     package, which the code may find by a type assertion or reflection,
//     also of a type of another package that embeds it. A parameter that
//     the entry of the function lists under formats is given only to
//     formatting, which runs methods named String, Error, Format, and
//     GoString, at any depth.
//
// What code of another package keeps and runs at another time, at a later
// call or on another goroutine, is not followed; see "What a proof
// assumes" in the guide.

// callNode is a function of the package with a body, or a function literal
// used as a value.
type callNode struct {
	fn    *funcInfo
	lit   *ast.FuncLit
	edges []callEdge
}

// callEdge is a call or a use of a function in a body.
type callEdge struct {
	to       *callNode
	at       token.Pos
	text     string
	resolved bool
	// why says, for an edge into code of another package that only the
	// types allow, what lets that code reach the target.
	why string
}

// callGraph holds the call graph of a package.
type callGraph struct {
	byObj map[*types.Func]*callNode
	lits  map[*ast.FuncLit]*callNode
	// escapes are the functions, methods, and literals used as values,
	// each with the type it is used as; ifaceValues the interface methods
	// used as method values, each standing for every method it may be.
	escapes     []valueEscape
	ifaceValues []*types.Func
	// sites holds the unresolved edges each call adds.
	sites map[*ast.CallExpr][]callEdge
}

// valueEscape is a function of the package used as a value of a type.
type valueEscape struct {
	node *callNode
	t    types.Type
}

// name names a node in a message.
func (pv *pkgVerifier) nodeName(n *callNode) string {
	if n.fn != nil {
		return funcTitle(n.fn.obj)
	}
	at := pv.pass.Fset.Position(n.lit.Pos())
	return fmt.Sprintf("the function literal at %s:%d:%d", filepath.Base(at.Filename), at.Line, at.Column)
}

// funcTitle names a function, or a method with its receiver type.
func funcTitle(obj *types.Func) string {
	recv := obj.Type().(*types.Signature).Recv()
	if recv == nil {
		return obj.Name()
	}
	t := recv.Type()
	star := ""
	if p, ok := t.(*types.Pointer); ok {
		t, star = p.Elem(), "*"
	}
	name := types.TypeString(t, func(*types.Package) string { return "" })
	if star != "" {
		return "(" + star + name + ")." + obj.Name()
	}
	return name + "." + obj.Name()
}

// callGraph returns the call graph of the package, built when it is first
// asked for, once the annotations are collected. A package with nothing to
// verify never builds it. It reads the trust files as written and checks
// no entry, which would ask Z3.
func (pv *pkgVerifier) callGraph() *callGraph {
	if pv.graph == nil {
		pv.buildGraph()
	}
	return pv.graph
}

// buildGraph builds the call graph of the package.
func (pv *pkgVerifier) buildGraph() {
	g := &callGraph{byObj: map[*types.Func]*callNode{}, lits: map[*ast.FuncLit]*callNode{}, sites: map[*ast.CallExpr][]callEdge{}}
	pv.graph = g
	for _, fn := range pv.order {
		if fn.decl.Body != nil {
			g.byObj[fn.obj] = &callNode{fn: fn}
		}
	}
	// The literals that are part of the function around them.
	inPlace := map[*ast.FuncLit]bool{}
	for _, file := range pv.pass.Files {
		ast.Inspect(file, func(n ast.Node) bool {
			switch n := n.(type) {
			case *ast.FuncDecl:
				if n.Body != nil {
					bound, _ := literalUses(pv.info, n.Body)
					for _, lit := range bound {
						inPlace[lit] = true
					}
				}
			case *ast.CallExpr:
				if lit, ok := ast.Unparen(n.Fun).(*ast.FuncLit); ok {
					inPlace[lit] = true
				}
				for _, arg := range pv.handedAsWritten(n) {
					if lit, ok := ast.Unparen(arg).(*ast.FuncLit); ok {
						inPlace[lit] = true
					}
				}
			}
			return true
		})
	}
	// Every literal used as a value is a node and an escape of its type,
	// also one that a verified function makes: the check of what such a
	// literal runs (stratification) does not count every call that the
	// graph follows, and it is not made when the verification of the
	// function stops before the literal.
	for _, file := range pv.pass.Files {
		ast.Inspect(file, func(n ast.Node) bool {
			if lit, ok := n.(*ast.FuncLit); ok && !inPlace[lit] {
				node := &callNode{lit: lit}
				g.lits[lit] = node
				g.escapes = append(g.escapes, valueEscape{node, pv.info.TypeOf(lit)})
			}
			return true
		})
	}
	pv.collectEscapes()
	for _, node := range g.byObj {
		pv.walkBody(node, node.fn.decl.Body)
	}
	for _, node := range g.lits {
		pv.walkBody(node, node.lit.Body)
	}
}

// collectEscapes finds every function and method of the package used as a
// value, and every one that code of another package can name.
func (pv *pkgVerifier) collectEscapes() {
	g := pv.graph
	called := map[ast.Expr]bool{}
	for _, file := range pv.pass.Files {
		ast.Inspect(file, func(n ast.Node) bool {
			if call, ok := n.(*ast.CallExpr); ok {
				called[ast.Unparen(call.Fun)] = true
			}
			return true
		})
	}
	for _, file := range pv.pass.Files {
		ast.Inspect(file, func(n ast.Node) bool {
			switch n := n.(type) {
			case *ast.SelectorExpr:
				selection := pv.info.Selections[n]
				method, _ := pv.info.Uses[n.Sel].(*types.Func)
				switch {
				case method == nil || called[n]:
				case selection != nil && isIfaceMethod(method):
					g.ifaceValues = append(g.ifaceValues, method)
				case g.byObj[method.Origin()] != nil:
					g.escapes = append(g.escapes, valueEscape{g.byObj[method.Origin()], pv.info.TypeOf(n)})
				}
				// The selected name is not a use of its own.
				ast.Inspect(n.X, func(m ast.Node) bool { return pv.escapeIdent(m, called) })
				return false
			}
			return pv.escapeIdent(n, called)
		})
	}
	// What code of another package can name.
	for _, fn := range pv.order {
		node := g.byObj[fn.obj]
		if node == nil || !fn.obj.Exported() {
			continue
		}
		sig := fn.obj.Type().(*types.Signature)
		if sig.Recv() == nil {
			g.escapes = append(g.escapes, valueEscape{node, sig})
			continue
		}
		g.escapes = append(g.escapes, valueEscape{node, withoutRecv(sig)})
		// As a method expression, with the receiver first, of the type and
		// of a pointer to it where the method set allows.
		recv := sig.Recv().Type()
		forms := []types.Type{recv}
		if _, isPointer := recv.(*types.Pointer); !isPointer {
			forms = append(forms, types.NewPointer(recv))
		}
		for _, form := range forms {
			params := append([]*types.Var{types.NewParam(token.NoPos, nil, "", form)}, slices.Collect(sig.Params().Variables())...)
			g.escapes = append(g.escapes, valueEscape{node, types.NewSignatureType(nil, nil, nil, types.NewTuple(params...), sig.Results(), sig.Variadic())})
		}
	}
}

// escapeIdent records a function of the package named anywhere but as the
// function of a call as an escape of its type there.
func (pv *pkgVerifier) escapeIdent(n ast.Node, called map[ast.Expr]bool) bool {
	id, ok := n.(*ast.Ident)
	if !ok || called[id] {
		return true
	}
	if named, ok := pv.info.Uses[id].(*types.Func); ok {
		if node := pv.graph.byObj[named.Origin()]; node != nil {
			pv.graph.escapes = append(pv.graph.escapes, valueEscape{node, pv.info.TypeOf(id)})
		}
	}
	return true
}

// withoutRecv returns a signature without its receiver.
func withoutRecv(sig *types.Signature) *types.Signature {
	return types.NewSignatureType(nil, nil, nil, sig.Params(), sig.Results(), sig.Variadic())
}

// signatureOf returns the signature of a function type, without receiver.
func signatureOf(t types.Type) *types.Signature {
	if t == nil {
		return nil
	}
	sig, ok := t.Underlying().(*types.Signature)
	if !ok {
		return nil
	}
	return withoutRecv(sig)
}

// mentionsTypeParam reports whether a type has a type parameter in it.
func mentionsTypeParam(t types.Type, seen map[types.Type]bool) bool {
	if t == nil || seen[t] {
		return false
	}
	seen[t] = true
	switch u := types.Unalias(t).(type) {
	case *types.TypeParam:
		return true
	case *types.Named:
		if u.TypeParams().Len() > 0 && u.TypeArgs().Len() == 0 {
			return true
		}
		for arg := range u.TypeArgs().Types() {
			if mentionsTypeParam(arg, seen) {
				return true
			}
		}
		return false
	case *types.Pointer:
		return mentionsTypeParam(u.Elem(), seen)
	case *types.Slice:
		return mentionsTypeParam(u.Elem(), seen)
	case *types.Array:
		return mentionsTypeParam(u.Elem(), seen)
	case *types.Map:
		return mentionsTypeParam(u.Key(), seen) || mentionsTypeParam(u.Elem(), seen)
	case *types.Chan:
		return mentionsTypeParam(u.Elem(), seen)
	case *types.Signature:
		for _, tuple := range []*types.Tuple{u.Params(), u.Results()} {
			for v := range tuple.Variables() {
				if mentionsTypeParam(v.Type(), seen) {
					return true
				}
			}
		}
		return u.TypeParams().Len() > 0
	case *types.Struct:
		for field := range u.Fields() {
			if mentionsTypeParam(field.Type(), seen) {
				return true
			}
		}
	case *types.Interface:
		for method := range u.Methods() {
			if mentionsTypeParam(method.Type(), seen) {
				return true
			}
		}
	}
	return false
}

// signaturesMeet reports whether a value of one signature can be one of the
// other: they are identical, or either has type parameters.
func signaturesMeet(a, b *types.Signature) bool {
	if a == nil || b == nil {
		return true
	}
	if mentionsTypeParam(a, map[types.Type]bool{}) || mentionsTypeParam(b, map[types.Type]bool{}) {
		return true
	}
	return types.Identical(a, b)
}

// methodsMatching returns the methods of the package that a call of an
// interface method of this name and signature may reach.
func (pv *pkgVerifier) methodsMatching(name string, sig *types.Signature) []*callNode {
	var found []*callNode
	for _, fn := range pv.order {
		node := pv.graph.byObj[fn.obj]
		msig := fn.obj.Type().(*types.Signature)
		if node == nil || msig.Recv() == nil || fn.obj.Name() != name {
			continue
		}
		if msig.RecvTypeParams().Len() > 0 || signaturesMeet(withoutRecv(msig), sig) {
			found = append(found, node)
		}
	}
	return found
}

// valuesMatching returns what a call through a function value of the given
// signature may reach.
func (pv *pkgVerifier) valuesMatching(sig *types.Signature) []*callNode {
	var found []*callNode
	seen := map[*callNode]bool{}
	add := func(nodes ...*callNode) {
		for _, node := range nodes {
			if !seen[node] {
				seen[node] = true
				found = append(found, node)
			}
		}
	}
	for _, escape := range pv.graph.escapes {
		if signaturesMeet(signatureOf(escape.t), sig) {
			add(escape.node)
		}
	}
	for _, method := range pv.graph.ifaceValues {
		if signaturesMeet(withoutRecv(method.Type().(*types.Signature)), sig) {
			add(pv.methodsMatching(method.Name(), withoutRecv(method.Type().(*types.Signature)))...)
		}
	}
	return found
}

// exportedMethods returns every method with an exported name of the
// package, which code of another package may find on a value it is given.
func (pv *pkgVerifier) exportedMethods() []*callNode {
	var found []*callNode
	for _, fn := range pv.order {
		if node := pv.graph.byObj[fn.obj]; node != nil && fn.obj.Type().(*types.Signature).Recv() != nil && fn.obj.Exported() {
			found = append(found, node)
		}
	}
	return found
}

// methodsNamed returns the methods of the package with one of the names.
func (pv *pkgVerifier) methodsNamed(names ...string) []*callNode {
	var found []*callNode
	for _, fn := range pv.order {
		if node := pv.graph.byObj[fn.obj]; node != nil && fn.obj.Type().(*types.Signature).Recv() != nil && slices.Contains(names, fn.obj.Name()) {
			found = append(found, node)
		}
	}
	return found
}

// codeTargets returns what code of another package may run that a value of
// the type can hold, at any depth.
func (pv *pkgVerifier) codeTargets(t types.Type, seen map[types.Type]bool) []*callNode {
	if t == nil || seen[t] {
		return nil
	}
	seen[t] = true
	if held, replaced := heldAs(t); replaced {
		return pv.codeTargets(held, seen)
	}
	switch u := t.Underlying().(type) {
	case *types.Signature:
		return pv.valuesMatching(withoutRecv(u))
	case *types.Interface:
		// What the value holds may be found by a type assertion or by
		// reflection: a value of any type of the package, with its
		// exported methods, or a function value of any type.
		found := pv.anythingTargets()
		for method := range u.Methods() {
			found = append(found, pv.methodsMatching(method.Name(), withoutRecv(method.Type().(*types.Signature)))...)
		}
		return found
	case *types.Basic:
		// An unsafe.Pointer may point to any value, which code of another
		// package can convert back to its type and call: it reaches what
		// an any reaches. The two types of the standard library whose
		// unsafe.Pointer their package fixes were walked as heldAs says
		// before they came here.
		if u.Kind() == types.UnsafePointer {
			return pv.anythingTargets()
		}
	case *types.Pointer:
		return pv.codeTargets(u.Elem(), seen)
	case *types.Slice:
		return pv.codeTargets(u.Elem(), seen)
	case *types.Array:
		return pv.codeTargets(u.Elem(), seen)
	case *types.Chan:
		return pv.codeTargets(u.Elem(), seen)
	case *types.Map:
		return append(pv.codeTargets(u.Key(), seen), pv.codeTargets(u.Elem(), seen)...)
	case *types.Struct:
		var found []*callNode
		for field := range u.Fields() {
			found = append(found, pv.codeTargets(field.Type(), seen)...)
		}
		return found
	}
	return nil
}

// anythingTargets returns what code of another package may run that a
// value which can hold anything holds: a value of any type of the package,
// found by a type assertion, by reflection, or by converting an
// unsafe.Pointer, with its exported methods, or a function value of any
// type.
func (pv *pkgVerifier) anythingTargets() []*callNode {
	return append(pv.exportedMethods(), pv.valuesMatching(nil)...)
}

// concreteMethods returns the methods with exported names declared on a
// type that is not an interface and on the types it holds at any depth,
// through fields, elements, and pointers: what code that is given a value
// of the type can find on it by assertion or reflection. What an interface
// or a function value inside holds is codeTargets'.
func (pv *pkgVerifier) concreteMethods(t types.Type, seen map[types.Type]bool) []*callNode {
	if t == nil || seen[t] {
		return nil
	}
	seen[t] = true
	if held, replaced := heldAs(t); replaced {
		return pv.concreteMethods(held, seen)
	}
	var found []*callNode
	if named, ok := types.Unalias(t).(*types.Named); ok {
		for method := range named.Origin().Methods() {
			if node := pv.graph.byObj[method]; node != nil && method.Exported() {
				found = append(found, node)
			}
		}
	}
	switch u := t.Underlying().(type) {
	case *types.Pointer:
		found = append(found, pv.concreteMethods(u.Elem(), seen)...)
	case *types.Slice:
		found = append(found, pv.concreteMethods(u.Elem(), seen)...)
	case *types.Array:
		found = append(found, pv.concreteMethods(u.Elem(), seen)...)
	case *types.Chan:
		found = append(found, pv.concreteMethods(u.Elem(), seen)...)
	case *types.Map:
		found = append(found, pv.concreteMethods(u.Key(), seen)...)
		found = append(found, pv.concreteMethods(u.Elem(), seen)...)
	case *types.Struct:
		for field := range u.Fields() {
			found = append(found, pv.concreteMethods(field.Type(), seen)...)
		}
	}
	return found
}

// formatTargets returns the methods that formatting a value of the type may
// run: String, Error, Format, and GoString of the type and of the types it
// holds through exported fields, elements, keys, and pointers, and of every
// type of the package when it holds an interface value there.
func (pv *pkgVerifier) formatTargets(t types.Type, seen map[types.Type]bool) []*callNode {
	if t == nil || seen[t] {
		return nil
	}
	seen[t] = true
	names := []string{"String", "Error", "Format", "GoString"}
	var found []*callNode
	// The method set of a pointer to the type has every method of the
	// type, those promoted from embedded fields included.
	if _, isIface := t.Underlying().(*types.Interface); !isIface {
		set := types.NewMethodSet(types.NewPointer(t))
		for selection := range set.Methods() {
			method, _ := selection.Obj().(*types.Func)
			if method == nil || !slices.Contains(names, method.Name()) {
				continue
			}
			if node := pv.graph.byObj[method.Origin()]; node != nil {
				found = append(found, node)
			}
		}
	}
	switch u := t.Underlying().(type) {
	case *types.Interface:
		return append(found, pv.methodsNamed(names...)...)
	case *types.Pointer:
		found = append(found, pv.formatTargets(u.Elem(), seen)...)
	case *types.Slice:
		found = append(found, pv.formatTargets(u.Elem(), seen)...)
	case *types.Array:
		found = append(found, pv.formatTargets(u.Elem(), seen)...)
	case *types.Map:
		found = append(found, pv.formatTargets(u.Key(), seen)...)
		found = append(found, pv.formatTargets(u.Elem(), seen)...)
	case *types.Struct:
		for field := range u.Fields() {
			if field.Exported() {
				found = append(found, pv.formatTargets(field.Type(), seen)...)
			}
		}
	}
	return found
}

// walkBody adds the edges of a body to its node. A literal used as a value
// is a node of its own and is not walked here.
func (pv *pkgVerifier) walkBody(node *callNode, body *ast.BlockStmt) {
	g := pv.graph
	trusted := node.fn != nil && pv.entryFor(node.fn.obj.FullName()) != nil
	var bound map[*types.Var]*ast.FuncLit
	if node.fn != nil {
		bound, _ = literalUses(pv.info, node.fn.decl.Body)
	}
	edge := func(to *callNode, at token.Pos, text string, resolved bool) callEdge {
		e := callEdge{to: to, at: at, text: text, resolved: resolved}
		node.edges = append(node.edges, e)
		return e
	}
	unresolved := func(call *ast.CallExpr, text, why string, targets []*callNode) {
		for _, to := range targets {
			e := edge(to, call.Pos(), text, false)
			e.why = why
			node.edges[len(node.edges)-1].why = why
			g.sites[call] = append(g.sites[call], e)
		}
	}
	ast.Inspect(body, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.FuncLit:
			return g.lits[n] == nil
		case *ast.Ident:
			if named, ok := pv.info.Uses[n].(*types.Func); ok {
				if to := g.byObj[named.Origin()]; to != nil {
					edge(to, n.Pos(), named.Name(), true)
				}
			}
		case *ast.RangeStmt:
			if rangesByCalling(pv.info.TypeOf(n.X)) {
				for _, to := range pv.valuesMatching(signatureOf(pv.info.TypeOf(n.X))) {
					edge(to, n.Pos(), "range over "+types.ExprString(n.X), false)
				}
			}
		case *ast.CallExpr:
			text := types.ExprString(n)
			for _, method := range pv.formattedMethods(n) {
				if to := g.byObj[method.Origin()]; to != nil {
					edge(to, n.Pos(), "formats with "+text, true)
				}
			}
			tv := pv.info.Types[n.Fun]
			if tv.IsType() || tv.IsBuiltin() {
				break
			}
			// json.NewEncoder(w).Encode(v) in one expression calls w.Write
			// and nothing else of w; what it encodes runs nothing of the
			// package (json.go). The NewEncoder inside it is part of it.
			if pv.isEncoderInner(n) {
				break
			}
			if w := pv.encoderInPlace(n); w != nil {
				encode := pv.staticCalleeAt(n)
				pv.handedCode(n, encode.Type().(*types.Signature), pv.entryFor(encode.FullName()), encode.Pkg(), false, false, encode.FullName(), false, text, unresolved)
				wt := pv.info.TypeOf(w)
				if obj, _, _ := types.LookupFieldOrMethod(wt, true, pv.pass.Pkg, "Write"); obj != nil {
					method := obj.(*types.Func)
					if isIface(wt) {
						unresolved(n, text, "", pv.methodsMatching("Write", withoutRecv(method.Type().(*types.Signature))))
					} else if to := g.byObj[method.Origin()]; to != nil {
						edge(to, n.Pos(), text, true)
					}
				}
				// What w is, as an argument written out, is walked as any
				// expression is.
				return true
			}
			if callee := pv.staticCalleeAt(n); callee != nil {
				if callee.Pkg() != pv.pass.Pkg {
					// What a call of a function of another package may run of
					// the code its arguments and receiver hold.
					origin := pv.originOf(callee)
					pv.handedCode(n, callee.Type().(*types.Signature), pv.entryFor(origin.FullName()), origin.Pkg(),
						errorConstructor(callee) && callee.Name() == "Errorf", true, origin.FullName(), false, text, unresolved)
				}
				break
			}
			switch fun := ast.Unparen(n.Fun).(type) {
			case *ast.FuncLit:
				return true
			case *ast.Ident:
				if variable, ok := pv.info.Uses[fun].(*types.Var); ok && bound[variable] != nil {
					return true
				}
				// A trusted function calls what its caller hands it under
				// calls, and that is followed where it is handed over.
				if variable, ok := pv.info.Uses[fun].(*types.Var); ok && trusted && pv.callsParam(node.fn, variable) {
					return true
				}
			}
			pv.valueCallArguments(n, text, unresolved)
			if method, _ := throughValue(pv.info, n); method != nil {
				unresolved(n, text, "", pv.methodsMatching(method.Name(), withoutRecv(method.Type().(*types.Signature))))
				break
			}
			unresolved(n, text, "", pv.valuesMatching(signatureOf(pv.info.TypeOf(n.Fun))))
		}
		return true
	})
}

// valueCallArguments adds what the implementation of a call with no static
// callee, an interface method or a function value, may run of what the
// call's arguments hold: it may be code of another package. A type entry
// of the trust file for the method or the function type may claim what it
// finds on them, as an entry for a function does.
func (pv *pkgVerifier) valueCallArguments(call *ast.CallExpr, text string, unresolved func(*ast.CallExpr, string, string, []*callNode)) {
	var sig *types.Signature
	var entry *trustEntry
	var from *types.Package
	who, inSource := "", false
	if method, _ := throughValue(pv.info, call); method != nil {
		sig, from, who = method.Type().(*types.Signature), method.Pkg(), method.FullName()
		entry = pv.entryFor(method.FullName())
		inSource = method.Pkg() != nil && pv.inAnalysedModule(method.Pkg(), method.Pos())
	} else {
		sig = signatureOf(pv.info.TypeOf(call.Fun))
		if named, ok := types.Unalias(pv.info.TypeOf(call.Fun)).(*types.Named); ok && named.Obj().Pkg() != nil {
			entry, from, who = pv.entryFor(funcTypeKey(named.Obj())), named.Obj().Pkg(), funcTypeKey(named.Obj())
			inSource = pv.inAnalysedModule(named.Obj().Pkg(), named.Obj().Pos())
		}
	}
	if sig == nil {
		return
	}
	pv.handedCode(call, sig, entry, from, false, false, who, inSource, text, unresolved)
}

// handedCode adds what code of another package may run of what a call
// gives it, its receiver too when withReceiver is set: by the entry's
// claims under asserts, formats, and calls, or else by type.
//
// who names the function, method, or function type whose entry could make
// the claim, for the advice of a report, and inSource is set for a type of
// the analysed module, whose contract is written in source and can claim
// nothing of the kind.
func (pv *pkgVerifier) handedCode(call *ast.CallExpr, sig *types.Signature, entry *trustEntry, from *types.Package, errorf, withReceiver bool,
	who string, inSource bool, text string, unresolved func(*ast.CallExpr, string, string, []*callNode)) {
	handed := map[ast.Expr]bool{}
	for _, arg := range pv.handedAsWritten(call) {
		handed[ast.Unparen(arg)] = true
	}
	// A type argument is code handed to the call: generic code may run
	// the methods of a value of its type, and of what such a value holds,
	// through its constraint, through an interface, or by reflection,
	// unless the entry claims under asserts that it runs none.
	if made := pv.instanceOf[pv.staticCalleeAt(call)]; made != nil {
		params := made.origin.Type().(*types.Signature).TypeParams()
		claimed := typeParamClaims(entry, made.origin)
		for i, t := range made.targs {
			if claimed[params.At(i)] {
				continue
			}
			if targets := pv.concreteMethods(t, map[types.Type]bool{}); len(targets) > 0 {
				unresolved(call, fmt.Sprintf("%s with %s = %s", text, params.At(i).Obj().Name(), types.TypeString(t, types.RelativeTo(pv.pass.Pkg))),
					fmt.Sprintf("a generic function may run the methods of a value of its type argument %s, and of what such a value holds, "+
						"through its constraint, through an interface, or by reflection\n"+
						"if %s runs no method of a value of type %s, add \"asserts: {%s: []}\" to its entry in %s, or call it with a type that has no methods",
						params.At(i).Obj().Name(), who, params.At(i).Obj().Name(), params.At(i).Obj().Name(), TrustFileName), targets)
			}
		}
	}
	formatted := map[*types.Var]bool{}
	if errorf {
		// fmt.Errorf formats its operands, as a function under formats
		// does.
		for param := range sig.Params().Variables() {
			formatted[param] = true
		}
	} else if entry != nil {
		for _, item := range entry.formats {
			for param := range sig.Params().Variables() {
				if param.Name() == item.text {
					formatted[param] = true
				}
			}
		}
	}
	// What a parameter under encodes is given runs no method of the
	// package: the walk of encoding/json refuses every type whose methods
	// encoding/json would call, but for three types of the standard
	// library (json.go), and encoding/json uses reflection on it only to
	// read it and to call those.
	encoded := map[*types.Var]bool{}
	if entry != nil {
		for _, item := range entry.encodes {
			for param := range sig.Params().Variables() {
				if param.Name() == item.text {
					encoded[param] = true
				}
			}
		}
	}
	var operands []ast.Expr
	paramOf := map[ast.Expr]*types.Var{}
	if sel, ok := ast.Unparen(call.Fun).(*ast.SelectorExpr); ok && withReceiver {
		if selection := pv.info.Selections[sel]; selection != nil && selection.Kind() == types.MethodVal {
			operands = append(operands, sel.X)
			paramOf[sel.X] = sig.Recv()
		}
	}
	// What the entry claims the function finds on what it is given; a
	// claim that cannot be read is no claim.
	claim, _ := pv.assertsClaim(entry, sig, from)
	formattedArgs, encodedArgs := map[ast.Expr]bool{}, map[ast.Expr]bool{}
	// What an argument is passed as: a value converted to an interface
	// type is one that code of the other package may assert to anything.
	passedAs := map[ast.Expr]types.Type{}
	for _, b := range bindArgsLoose(pv.info, call, sig) {
		if formatted[b.param] {
			formattedArgs[b.expr] = true
		}
		if encoded[b.param] {
			encodedArgs[b.expr] = true
		}
		paramOf[b.expr] = b.param
		t := b.param.Type()
		if sig.Variadic() && b.param == sig.Params().At(sig.Params().Len()-1) && call.Ellipsis == token.NoPos {
			t = elemType(t)
		}
		passedAs[b.expr] = t
	}
	operands = append(operands, call.Args...)
	for _, arg := range operands {
		inner := ast.Unparen(arg)
		named, method := pv.valueFormOf(inner)
		switch {
		case handed[inner]:
			// A handed literal is part of the body, and a handed function
			// is named, which is an edge.
		case pv.knownAtCall(arg):
			// An error of known origin holds a type of the standard
			// library, and nothing of this package.
		case encodedArgs[arg]:
			// It hands nothing of the package that can run.
		case formattedArgs[arg]:
			// Formatting runs the methods String, Error, Format, and
			// GoString of the value and of what it holds through exported
			// fields, elements, and pointers, which fmt reaches by
			// reflection; through an interface value, those of any type.
			// The value's own String or Error is the resolved edge that
			// formattedMethods gives; what it holds is reached by type.
			own := map[*callNode]bool{}
			for _, method := range pv.formattedMethods(call) {
				if node := g(pv).byObj[method.Origin()]; node != nil {
					own[node] = true
				}
			}
			unresolved(call, "formats with "+text, fmt.Sprintf("formatting %s runs the methods String, Error, Format, and GoString of what it holds, "+
				"through exported fields and, for an interface value, of any type of the package", types.ExprString(arg)),
				slices.DeleteFunc(pv.formatTargets(pv.info.TypeOf(arg), map[types.Type]bool{}), func(n *callNode) bool { return own[n] }))
		case g(pv).lits[asLit(inner)] != nil:
			// A literal written here is the code the argument holds.
			unresolved(call, fmt.Sprintf("hands the function literal to %s", text), "", []*callNode{g(pv).lits[asLit(inner)]})
		case claim != nil && paramOf[arg] != nil && claimFor(claim, paramOf[arg]) != nil:
			// The entry claims what the function finds on it.
			unresolved(call, fmt.Sprintf("hands %s to %s", types.ExprString(arg), text), "",
				pv.claimedTargets(paramOf[arg], claimFor(claim, paramOf[arg])))
		case named != nil || method != nil:
			// So is a function or a method named here.
			target := named
			if method != nil {
				target = method
			}
			if to := g(pv).byObj[target.Origin()]; to != nil {
				unresolved(call, fmt.Sprintf("hands %s to %s", types.ExprString(arg), text), "", []*callNode{to})
			}
		default:
			t := pv.info.TypeOf(arg)
			targets := pv.codeTargets(t, map[types.Type]bool{})
			why := fmt.Sprintf("%s holds an interface value or a function value, which may hold a value of any type of the package or any function it lets out, "+
				"and code of another package may call that, or an exported method of it, by a type assertion or reflection", types.ExprString(arg))
			switch {
			case types.IsInterface(t):
				why = fmt.Sprintf("%s is an interface value, which may hold a value of any type of the package or any function it lets out, "+
					"and code of another package may call that, or an exported method of it, by a type assertion or reflection", types.ExprString(arg))
			case heldCode(t, map[types.Type]bool{}) == "an unsafe.Pointer":
				why = fmt.Sprintf("%s holds an unsafe.Pointer, which may point to a value of any type of the package or any function it lets out, "+
					"and code of another package may convert it back and call that, or an exported method of it", types.ExprString(arg))
			}
			if as := passedAs[arg]; as != nil && types.IsInterface(as) && !types.IsInterface(t) {
				if len(targets) == 0 {
					why = fmt.Sprintf("%s is converted to %s there, and code of another package may call the exported methods of its type, "+
						"and of what it holds, by a type assertion or reflection", types.ExprString(arg), as)
				}
				// A value of a type that is not an interface, converted to
				// one here, has that type as its dynamic type: what the
				// other package can find on it by assertion or reflection
				// are the methods of that type and of the types it holds.
				targets = append(targets, pv.concreteMethods(pv.info.TypeOf(arg), map[types.Type]bool{})...)
			}
			// What can be done: an entry that says what the code finds on
			// the parameter, where an entry can be written.
			advice := "Hand that code a value whose type holds no interface value and no function value, or keep what it may reach from calling back"
			if param := paramOf[arg]; param != nil && who != "" {
				kind := "the methods of " + types.TypeString(param.Type(), types.RelativeTo(pv.pass.Pkg))
				switch {
				case inSource:
					advice = fmt.Sprintf("the contract of %s in source cannot say what its implementations find on %s; "+
						"hand it a value whose type holds no interface value and no function value, or keep what it may reach from calling back", who, param.Name())
				case entry != nil:
					advice = fmt.Sprintf("nothing in the entry of %s says what it finds on %s; if it calls only %s, add \"asserts: {%s: []}\" to its entry in %s",
						who, param.Name(), kind, param.Name(), TrustFileName)
				default:
					advice = fmt.Sprintf("%s has no entry that says what it finds on %s; if it calls only %s, give it an entry with \"asserts: {%s: []}\" in %s",
						who, param.Name(), kind, param.Name(), TrustFileName)
				}
			}
			unresolved(call, fmt.Sprintf("hands %s to %s", types.ExprString(arg), text), why+"\n"+advice, targets)
		}
	}
}

// handedAsWritten returns the arguments of a call that the entry of its
// callee, as written and unchecked, gives a contract under calls.
func (pv *pkgVerifier) handedAsWritten(call *ast.CallExpr) []ast.Expr {
	callee := pv.staticCalleeAt(call)
	if callee == nil {
		return nil
	}
	entry := pv.entryFor(pv.originOf(callee).FullName())
	if entry == nil || len(entry.calls) == 0 {
		return nil
	}
	sig := callee.Type().(*types.Signature)
	bound, _ := bindArgs(pv.info, call, paramsOf(sig), sig.Variadic())
	var handed []ast.Expr
	for _, b := range bound {
		if !b.packed && slices.ContainsFunc(entry.calls, func(c trustCall) bool { return c.name == b.param.Name() }) {
			handed = append(handed, b.expr)
		}
	}
	return handed
}

// knownAtCall reports whether an argument is an error whose origin can be
// seen at the call: nil, an error that errors.New or fmt.Errorf makes there,
// or a sentinel of the package, which holds one of those. Its dynamic type
// is then the standard library's.
func (pv *pkgVerifier) knownAtCall(arg ast.Expr) bool {
	arg = ast.Unparen(arg)
	if !isError(pv.info.TypeOf(arg)) {
		return false
	}
	if pv.info.Types[arg].IsNil() {
		return true
	}
	switch e := arg.(type) {
	case *ast.CallExpr:
		return errorConstructor(typeutil.StaticCallee(pv.info, e))
	case *ast.Ident:
		variable, ok := pv.info.Uses[e].(*types.Var)
		return ok && pv.sentinels[variable]
	}
	return false
}

// claimFor returns the types a claim lists for a parameter, compared by
// position and name, since a generic function's instantiation has
// parameters of its own; nil when the claim has no key for it.
func claimFor(claim map[*types.Var][]types.Type, param *types.Var) []types.Type {
	for p, listed := range claim {
		if p == param || (p.Name() == param.Name() && p.Pos() == param.Pos()) {
			return listed
		}
	}
	return nil
}

// g returns the call graph.
func g(pv *pkgVerifier) *callGraph { return pv.callGraph() }

// asLit returns an expression as a function literal, or nil.
func asLit(e ast.Expr) *ast.FuncLit {
	lit, _ := e.(*ast.FuncLit)
	return lit
}

// valueFormOf returns the function or the method that an expression names
// as a value, if it does: a function's name, or a method value.
func (pv *pkgVerifier) valueFormOf(e ast.Expr) (named, method *types.Func) {
	switch e := e.(type) {
	case *ast.IndexExpr, *ast.IndexListExpr:
		return explicitInstance(pv.info, e), nil
	case *ast.Ident:
		named, _ = pv.info.Uses[e].(*types.Func)
	case *ast.SelectorExpr:
		if selection := pv.info.Selections[e]; selection != nil && selection.Kind() == types.MethodVal {
			method, _ = selection.Obj().(*types.Func)
			if isIfaceMethod(method) {
				method = nil
			}
			return nil, method
		}
		named, _ = pv.info.Uses[e.Sel].(*types.Func)
	}
	return named, method
}

// bindArgsLoose pairs the arguments of a call with the parameters they are
// given to, the arguments of a variadic parameter each with it.
func bindArgsLoose(info *types.Info, call *ast.CallExpr, sig *types.Signature) []struct {
	param *types.Var
	expr  ast.Expr
} {
	var bound []struct {
		param *types.Var
		expr  ast.Expr
	}
	params := sig.Params()
	for i, arg := range call.Args {
		at := i
		if at >= params.Len() {
			at = params.Len() - 1
		}
		if at < 0 {
			break
		}
		bound = append(bound, struct {
			param *types.Var
			expr  ast.Expr
		}{params.At(at), arg})
	}
	return bound
}

// cycle is a way back from a call to the function it is made in.
type cycle struct {
	steps []callEdge
	from  []*callNode
}

// cycleThrough looks for a way from the targets of a call back to the
// node, and returns the shortest one, first among those that go only
// through resolved edges when wantResolved is set, and otherwise among
// those that go through at least one unresolved edge. first is the edge of
// the call itself.
func (pv *pkgVerifier) cycleThrough(self *callNode, first []callEdge, wantResolved bool) *cycle {
	type state struct {
		node       *callNode
		unresolved bool
	}
	type visit struct {
		state
		prev *visit
		edge callEdge
		from *callNode
	}
	seen := map[state]bool{}
	var queue []*visit
	for _, e := range first {
		s := state{e.to, !e.resolved}
		if wantResolved && s.unresolved || seen[s] {
			continue
		}
		seen[s] = true
		queue = append(queue, &visit{state: s, edge: e, from: self})
	}
	for len(queue) > 0 {
		v := queue[0]
		queue = queue[1:]
		if v.node == self && v.unresolved != wantResolved {
			c := &cycle{}
			for at := v; at != nil; at = at.prev {
				c.steps = append([]callEdge{at.edge}, c.steps...)
				c.from = append([]*callNode{at.from}, c.from...)
			}
			return c
		}
		if v.node == self {
			continue
		}
		for _, e := range v.node.edges {
			s := state{e.to, v.unresolved || !e.resolved}
			if wantResolved && s.unresolved || seen[s] {
				continue
			}
			seen[s] = true
			queue = append(queue, &visit{state: s, prev: v, edge: e, from: v.node})
		}
	}
	return nil
}

// describe writes a cycle out, one call after another.
func (pv *pkgVerifier) describeCycle(c *cycle) string {
	var parts []string
	for i, step := range c.steps {
		at := pv.pass.Fset.Position(step.at)
		where := fmt.Sprintf("%s:%d:%d", filepath.Base(at.Filename), at.Line, at.Column)
		from := pv.nodeName(c.from[i])
		switch {
		case step.resolved:
			parts = append(parts, fmt.Sprintf("%s calls %s at %s", from, pv.nodeName(step.to), where))
		case strings.HasPrefix(step.text, "hands ") || strings.HasPrefix(step.text, "formats with "):
			parts = append(parts, fmt.Sprintf("%s %s at %s, which may run %s", from, step.text, where, pv.nodeName(step.to)))
		default:
			parts = append(parts, fmt.Sprintf("%s calls %s at %s, which may run %s", from, step.text, where, pv.nodeName(step.to)))
		}
	}
	return strings.Join(parts, ", ")
}

// callEdges returns the edges a call makes, from the graph where the call
// is in it, and otherwise from its contract: a call that a function used
// as a value or a run of a trusted function makes is not in a body.
func (pv *pkgVerifier) callEdges(call *ast.CallExpr, fn *funcInfo) []callEdge {
	g := pv.callGraph()
	var edges []callEdge
	switch {
	case fn.methodOf != nil:
		if sites, ok := g.sites[call]; ok {
			return sites
		}
		for _, to := range pv.methodsMatching(fn.methodOf.Name(), withoutRecv(fn.methodOf.Type().(*types.Signature))) {
			edges = append(edges, callEdge{to: to, at: call.Pos(), text: types.ExprString(call)})
		}
		return edges
	case fn.valueOf != nil:
		if sites, ok := g.sites[call]; ok {
			return sites
		}
		for _, to := range pv.valuesMatching(signatureOf(fn.valueOf.Type())) {
			edges = append(edges, callEdge{to: to, at: call.Pos(), text: types.ExprString(call)})
		}
		return edges
	}
	if to := byFunc(g.byObj, pv.originOf(fn.obj)); to != nil {
		edges = append(edges, callEdge{to: to, at: call.Pos(), text: fn.obj.Name(), resolved: true})
	}
	return append(edges, g.sites[call]...)
}

// spreadCallees returns the functions of the package a function may lead
// to directly, for the rule that failure spreads from callee to caller.
func (pv *pkgVerifier) spreadCallees(fn *funcInfo) []*funcInfo {
	node := pv.callGraph().byObj[fn.obj]
	if node == nil {
		return nil
	}
	var callees []*funcInfo
	seen := map[*callNode]bool{}
	var visit func(n *callNode)
	visit = func(n *callNode) {
		for _, e := range n.edges {
			if seen[e.to] {
				continue
			}
			seen[e.to] = true
			if e.to.fn != nil {
				callees = append(callees, e.to.fn)
			} else {
				// A literal used as a value is called through it.
				visit(e.to)
			}
		}
	}
	visit(node)
	return callees
}
