package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
)

// Pointers to single values (F37, step 2).
//
// A pointer to a number, a boolean, or a string points to a box: an
// allocation of one cell, of a struct type of one field that vego makes
// for each underlying type (boxOf). new(T) makes one, and so does a local
// variable or a parameter whose address is taken, which then lives in it;
// every rule of pointers to structs is then the rule of these pointers. In
// a formula, *p reads the box's field (a Deref step of a path), so *p',
// old(*p), and Modifies p mean what they mean of a field of a struct.
//
// Since F42 such a pointer may also point to a field, an element of a
// slice or an array, or a package-level variable of the package: a field
// that a pointer can point to lies in the place region of its type with
// the boxes, and an element in its elem region, and the pointer's #arr says
// which (layout.go, addressed.go). Nothing is assumed of where a pointer
// from code that is not verified points.

// interiorRefusal says why the address of a single value cannot be taken,
// by taking, which says how: "taking the address of x", or "calling Inc
// takes the address of x, which". What is left refused is a place that Go
// can address and vego does not model as memory: a package-level variable
// of another package, or one that a directive or assembly names.
func interiorRefusal(taking string, t types.Type) string {
	return fmt.Sprintf("%s is not supported yet: it is a value of type %s that does not lie in memory vego models; "+
		"a pointer to a number, a boolean, or a string can point to a local variable, what new makes, a field or an element in memory, "+
		"or a package-level variable of this package whose address is taken; copy the value into a local variable and take its address", taking, t)
}

// placeTargets returns the &x of a body that errors.As, errors.AsType, or a
// function with decodes is handed as what it writes into. Those write the
// place x by a route of their own (jsondecode.go, dyntypes_as.go), so a
// number, a boolean, or a string whose address is taken only there does not
// live in memory, as before pointers to single values; one whose address is
// also taken elsewhere lives in its box, and the route writes the box.
func (v *fnVerifier) placeTargets(body *ast.BlockStmt) map[*ast.UnaryExpr]bool {
	targets := map[*ast.UnaryExpr]bool{}
	ast.Inspect(body, func(n ast.Node) bool {
		call, ok := n.(*ast.CallExpr)
		if !ok {
			return true
		}
		callee := v.pkgVerifier.calleeAt(call)
		_, _, limited := v.pkgVerifier.decoderInPlace(call)
		writes := limited || callee != nil && isAsCall(callee)
		if !writes && callee != nil {
			if fn := v.contractOf(callee); fn != nil && fn.decoded != nil {
				writes = true
			}
		}
		for _, arg := range call.Args {
			if address, ok := ast.Unparen(arg).(*ast.UnaryExpr); ok && writes && address.Op == token.AND {
				targets[address] = true
			}
		}
		return true
	})
	return targets
}
