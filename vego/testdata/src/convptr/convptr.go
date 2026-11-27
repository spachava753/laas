// Package convptr converts pointers between named interface types and
// between named function types of one underlying type, which is refused
// (F20 of the review of step 2 of F42).
package convptr

// T returns 1.
type T struct{}

// M returns 1.
//
// @Ensures r = 1
func (T) M() (r int) {
	return 1
}

// A promises 1.
type A interface {
	// @Ensures r = 1
	M() (r int)
}

// B promises 2.
type B interface {
	// @Ensures r = 2
	M() (r int)
}

// Conv is false: a holds T, whose M returns 1, and the pointer conversion
// makes it a B with no check of B's contract.
//
// @Ensures r = 2
func Conv() (r int) {
	var a A = T{}
	pb := (*B)(&a) // want `vego: cannot verify Conv: converting \&a from \*A to \*B is not supported: the `
	return (*pb).M()
}

// F promises a result of 1.
//
// @Ensures r = 1
type F func(x int) (r int)

// G promises a result of 2.
//
// @Ensures r = 2
type G func(x int) (r int)

// one returns 1.
//
// @Ensures r = 1
func one(x int) (r int) {
	return 1
}

// ConvFunc is false: f is one, which returns 1, seen as a G.
//
// @Ensures r = 2
func ConvFunc() (r int) {
	var f F = one
	pg := (*G)(&f) // want `vego: cannot verify ConvFunc: converting \&f from \*F to \*G is not supported: `
	return (*pg)(0)
}
