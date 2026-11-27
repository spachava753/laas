package vego

import (
	"fmt"
	"go/ast"
	"go/types"
	"slices"
	"strings"
)

// Verified code of another package may run code of this package that it
// holds but was not handed at the call that leads to it: a hook kept in a
// package-level variable, or a value it wraps that code which is not
// verified put together. "What a proof assumes" covers what code that is
// not verified keeps and runs later; it says nothing of verified code, so
// the call graph follows it (F43, step 0).
//
// Two published marks say where it may happen:
//
//   - ReadsHeldCode in the contract of a function: running it may read a
//     package-level variable, of any package, whose type can hold code, and
//     so call what another call left there. A call of such a function of
//     another package may run any method with an exported name of this
//     package and any function it lets out, whatever the call hands it.
//   - heldCodeFact of a package: the methods with exported names and the
//     functions used as values of the package, by name and canonical
//     signature, whose verification was attempted and that may call through
//     a value. A call of an interface method or of a function value in this
//     package may reach such an implementation of another package, made into
//     a value by code that is not verified around code of this package, and
//     so may run the same.
//
// Only what this package can see is counted: the packages it imports, at any
// depth. An implementation in a package that it cannot see is the limit
// "What a proof assumes" states.

// heldCodeFact lists, for a package, what of it may run code it holds when
// it is called through a value.
type heldCodeFact struct {
	// Methods holds "Name|signature" of each method with an exported name
	// of a type of the package that may call through a value.
	Methods []string
	// Funcs holds the signature of each function, method value, and literal
	// of the package that is used as a value, or exported, and that may
	// call through a value.
	Funcs []string
}

func (*heldCodeFact) AFact() {}

func (f *heldCodeFact) String() string {
	return fmt.Sprintf("heldcode(%d methods, %d functions)", len(f.Methods), len(f.Funcs))
}

// readsHeldLocally reports whether a node's own body reads a package-level
// variable that code other than its package's initialisers may set to code,
// or calls a function of another package that is marked so.
func (pv *pkgVerifier) readsHeldLocally(body ast.Node) bool {
	found := false
	ast.Inspect(body, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.Ident:
			v, ok := pv.info.Uses[n].(*types.Var)
			found = found || ok && pv.holdsSetCode(v)
		case *ast.CallExpr:
			found = found || pv.callReadsHeld(n)
		}
		return !found
	})
	return found
}

// callReadsHeld reports whether a call is of a function of another package
// whose contract says it may read such a variable.
func (pv *pkgVerifier) callReadsHeld(call *ast.CallExpr) bool {
	callee := pv.staticCalleeAt(call)
	if callee == nil || callee.Pkg() == nil || callee.Pkg() == pv.pass.Pkg {
		return false
	}
	fact := &contractFact{}
	return pv.pass.ImportObjectFact(pv.originOf(callee).Origin(), fact) && fact.ReadsHeldCode
}

// readsHeldCode reports whether running a function may read a package-level
// variable whose type can hold code: its node or a node it reaches in the
// graph does, or calls a function of another package that may.
func (pv *pkgVerifier) readsHeldCode(obj *types.Func) bool {
	g := pv.callGraph()
	start := g.byObj[obj]
	if start == nil {
		return false
	}
	if pv.readsHeld == nil {
		pv.readsHeld = map[*callNode]bool{}
		for _, node := range g.byObj {
			pv.readsHeld[node] = pv.readsHeldLocally(node.fn.decl.Body)
		}
		for _, node := range g.lits {
			pv.readsHeld[node] = pv.readsHeldLocally(node.lit.Body)
		}
	}
	seen := map[*callNode]bool{start: true}
	queue := []*callNode{start}
	for len(queue) > 0 {
		n := queue[0]
		queue = queue[1:]
		if pv.readsHeld[n] || n.heldImpl {
			return true
		}
		for _, e := range n.edges {
			if !seen[e.to] {
				seen[e.to] = true
				queue = append(queue, e.to)
			}
		}
	}
	return false
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

// exportHeldCode publishes what of the package may run code it holds when it
// is called through a value: the methods with exported names and the
// functions used as values or exported, whose verification was attempted,
// that may call through a value.
func (pv *pkgVerifier) exportHeldCode() {
	// A package with nothing to verify builds no graph, and has nothing
	// to publish here.
	if !slices.ContainsFunc(pv.order, (*funcInfo).annotated) {
		return
	}
	g := pv.callGraph()
	fact := &heldCodeFact{}
	methods, funcs := map[string]bool{}, map[string]bool{}
	for _, fn := range pv.order {
		if g.byObj[fn.obj] == nil || !fn.annotated() || !pv.mayCallValues(fn.obj) {
			continue
		}
		sig := fn.obj.Type().(*types.Signature)
		if sig.Recv() != nil && fn.obj.Exported() {
			methods[fn.obj.Name()+"|"+canonSig(withoutRecv(sig))] = true
		}
	}
	for _, escape := range g.escapes {
		if escape.node.fn == nil || !escape.node.fn.annotated() || !pv.mayCallValues(escape.node.fn.obj) {
			continue
		}
		if sig := signatureOf(escape.t); sig != nil {
			funcs[canonSig(sig)] = true
		}
	}
	if len(methods) == 0 && len(funcs) == 0 {
		return
	}
	fact.Methods = slices.Sorted(mapKeysOf(methods))
	fact.Funcs = slices.Sorted(mapKeysOf(funcs))
	pv.pass.ExportPackageFact(fact)
}

// visibleHeld returns the heldCodeFacts of the packages this one imports, at
// any depth, joined.
func (pv *pkgVerifier) visibleHeld() (methods, funcs map[string]bool) {
	if pv.heldMethods == nil {
		pv.heldMethods, pv.heldFuncs = map[string]bool{}, map[string]bool{}
		for _, published := range pv.pass.AllPackageFacts() {
			if fact, ok := published.Fact.(*heldCodeFact); ok && published.Package != pv.pass.Pkg {
				for _, k := range fact.Methods {
					pv.heldMethods[k] = true
				}
				for _, k := range fact.Funcs {
					pv.heldFuncs[k] = true
				}
			}
		}
	}
	return pv.heldMethods, pv.heldFuncs
}

// heldMethodMeets reports whether an implementation of another package that
// may run code it holds has the name and signature of an interface method.
func (pv *pkgVerifier) heldMethodMeets(method *types.Func) bool {
	if !method.Exported() {
		return false
	}
	methods, _ := pv.visibleHeld()
	sig := withoutRecv(method.Type().(*types.Signature))
	key := canonSig(sig)
	for k := range methods {
		name, s, _ := strings.Cut(k, "|")
		if name == method.Name() && (s == key || s == "*" || key == "*") {
			return true
		}
	}
	return false
}

// heldFuncMeets reports whether a function of another package used as a
// value that may run code it holds has a signature.
func (pv *pkgVerifier) heldFuncMeets(sig *types.Signature) bool {
	_, funcs := pv.visibleHeld()
	if sig == nil {
		return len(funcs) > 0
	}
	key := canonSig(sig)
	return funcs[key] || funcs["*"] || key == "*" && len(funcs) > 0
}

// heldWhy says why a call may run code of the package that verified code of
// another package holds.
func heldWhy(what string) string {
	return what + ", which may call code that it holds and was not handed at this call, as a hook kept in a package-level variable " +
		"or a value that code which is not verified gave it, and that code may be any method with an exported name of the package " +
		"or any function it lets out"
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
