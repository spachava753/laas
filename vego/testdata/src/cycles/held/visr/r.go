// Package visr wraps a J in a T whose M calls it. visq, which calls M,
// does not import it; visp, which hands a T to visq, does.
package visr

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
