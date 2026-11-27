// Package wrapr wraps a J in a T whose M calls it (k3 of the reply to the
// design review of F43).
package wrapr

// I is what wrapq calls.
type I interface {
	// @Ensures True
	M()
}

// J is what a T wraps.
type J interface {
	// @Ensures True
	N()
}

// T holds a J.
type T struct{ inner J }

// @Ensures True
func Wrap(j J) (t T) { return T{inner: j} }

// @Ensures True
func (t T) M() {
	if t.inner != nil {
		t.inner.N()
	}
}
