// Package badshapes has struct types whose invariants cannot be used. Such
// a package hands nothing to other packages as verified, so the types
// stand apart from the ones in package shapes that other tests rely on.
package badshapes

// Broken has an invariant that cannot be read, which importing packages
// must not take for no invariant.
//
// @Invariant X > // want `syntax error in Invariant annotation: expected an expression, found "end of annotation"`
type Broken struct{ X int }

// Never has invariants no value can meet. A function of another package
// that takes one must not be verified from that contradiction.
//
// @Invariant X = 0 And X = 1 // want `the invariants of Never contradict each other, so no value of the type could exist`
type Never struct{ X int }
