package vego

import (
	"go/ast"
	"go/types"
	"slices"
)

// A call of a function that never assigns a variable leaves it as it was
// (S1 of F31's coder, built in F32). Modifies v of an assigned variable
// covers its storage and what it refers to; when the callee, and all it may
// run, never assigns the storage, a caller keeps it, as if the callee
// ensured v' = v, and forgets only what v refers to. Built for kind 2 and
// for variables of interface types, whose storage is reached only by name
// (V1); a struct variable whose address is taken may be written through
// any pointer that reaches it, which no syntax shows.

// mayAssign reports whether a verified function of the package, or what it
// may run, may assign the storage of an assigned variable of the package:
// an assignment of it or of a part of it, in its body or a literal there,
// deferred or not; a call into another package of an exported variable; a
// trusted call, or a call through a value or of a method of an interface,
// whose contract lists it or the state of its package; or code of the
// package that such a call may run, by the call graph, which assigns it.
func (pv *pkgVerifier) mayAssign(fn *funcInfo, variable *types.Var) bool {
	if fn == nil || fn.obj == nil || fn.obj.Pkg() != pv.pass.Pkg || fn.trust != nil || fn.valueOf != nil || fn.methodOf != nil {
		return true
	}
	start := pv.callGraph().byObj[pv.originOf(fn.obj)]
	if start == nil {
		return true
	}
	seen := map[*callNode]bool{start: true}
	work := []*callNode{start}
	for len(work) > 0 {
		node := work[len(work)-1]
		work = work[:len(work)-1]
		if pv.nodeMayAssign(node, variable) {
			return true
		}
		for _, e := range node.edges {
			if !seen[e.to] {
				seen[e.to] = true
				work = append(work, e.to)
			}
		}
	}
	return false
}

// nodeMayAssign reports whether the body of a node of the call graph
// assigns the variable, or calls what may by its contract.
func (pv *pkgVerifier) nodeMayAssign(node *callNode, variable *types.Var) bool {
	var body ast.Node
	switch {
	case node.lit != nil:
		body = node.lit.Body
	case node.fn != nil && node.fn.decl != nil:
		body = node.fn.decl.Body
	}
	if body == nil {
		return true
	}
	lists := func(contract *funcInfo) bool {
		if contract == nil {
			return true
		}
		for _, m := range contract.modifies {
			if pkg, named, _ := pv.modifiesPackage(contract, m); named {
				if slices.Contains(pv.covers(pkg), variable.Pkg().Path()) {
					return true
				}
				continue
			}
			if pv.modifiesVariableOf(contract, m) == variable {
				return true
			}
		}
		return false
	}
	found := false
	var stack []ast.Node
	ast.Inspect(body, func(n ast.Node) bool {
		if n == nil {
			stack = stack[:len(stack)-1]
			return true
		}
		stack = append(stack, n)
		if found {
			return false
		}
		switch n := n.(type) {
		case *ast.Ident:
			if pv.info.Uses[n] == variable {
				if change := pv.useOf(stack).change; change != "" && kindOfChange(change) == changeAssigned {
					found = true
				}
			}
		case *ast.CallExpr:
			if tv := pv.info.Types[n.Fun]; tv.IsType() || tv.IsBuiltin() {
				break
			}
			callee := pv.calleeAt(n)
			switch {
			case callee == nil:
				// A call through a value: its contract, and what of the
				// package it may run, which the graph's edges follow.
				if _, isLit := ast.Unparen(n.Fun).(*ast.FuncLit); !isLit && calledLiteral(pv.info, nil, n) == nil {
					if contract := pv.valueContract(pv.info.TypeOf(n.Fun)); contract != nil && lists(contract) {
						found = true
					}
				}
			case callee.Type().(*types.Signature).Recv() != nil && isIface(callee.Type().(*types.Signature).Recv().Type()):
				if lists(pv.methodContract(callee)) {
					found = true
				}
			case callee.Pkg() != pv.pass.Pkg:
				// Another package can assign only an exported variable, or
				// one its trusted contract lists.
				if variable.Exported() {
					found = true
				} else if contract := pv.contractOf(callee); contract != nil && contract.trust != nil && lists(contract) {
					found = true
				}
			}
		}
		return true
	})
	return found
}

// keepUnassigned drops, from what a call of a verified function writes, the
// storage of each assigned variable of the package, or of an interface type,
// that the callee lists and never assigns.
func (v *fnVerifier) keepUnassigned(fn *funcInfo, written []target) []target {
	if fn.trust != nil || fn.valueOf != nil || fn.methodOf != nil || fn.obj == nil || fn.obj.Pkg() != v.pass.Pkg {
		return written
	}
	return slices.DeleteFunc(slices.Clone(written), func(t target) bool {
		variable := v.variableOfCells(t.cells)
		return variable != nil && variable.Pkg() == v.pass.Pkg && !v.mayAssign(fn, variable)
	})
}
