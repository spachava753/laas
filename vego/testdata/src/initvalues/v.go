// Package initvalues calls through values and interface values in
// initialisers, which may run a verified function of the package outside
// the Requires it meets (F22 of the review of step 5 of F32).
package initvalues

// @Invariant n >= 0
var n int

// Setter sets n.
//
// @Requires k >= 0
// @Modifies n
// @Ensures True
type Setter func(k int) (r int)

// set sets n.
//
// @Requires k >= 0
// @Modifies n
// @Ensures True
func set(k int) (r int) {
	n = k
	return 0
}

var setter Setter = set

var _ = setter(-1) // want `vego: precondition of setter may not hold in an initialiser, where a verified function relies on it for what it writes: k >= 0`

// Sets sets n through a method.
type Sets interface {
	// Set sets n.
	//
	// @Requires k >= 0
	// @Modifies n
	// @Ensures True
	Set(k int) (r int)
}

// impl sets n.
type impl struct{}

// Set sets n.
//
// @Requires k >= 0
// @Modifies n
// @Ensures True
func (impl) Set(k int) (r int) {
	n = k
	return 0
}

var sets Sets = impl{}

var _ = sets.Set(-1) // want `vego: precondition of sets.Set may not hold in an initialiser, where a verified function relies on it for what it writes: k >= 0`

var _ = func() int {
	return setter(-2) // want `vego: setter is called in a function literal in the initialiser of a package-level variable, where its Requires is not checked`
}()

var _ = setter(2)

// Get reads n.
//
// @Ensures r >= 0
func Get() (r int) {
	return n
}
