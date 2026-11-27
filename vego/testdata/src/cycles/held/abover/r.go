// Package abover wraps an abovep.J in a T whose M calls it.
package abover

import "cycles/held/abovep"

// T holds a J.
type T struct{ inner abovep.J }

// @Ensures True
func (t T) M() {
	if t.inner != nil {
		t.inner.N() // want `this call may not end: T.M calls t.inner.N\(\) at r.go:\d+:\d+, which may run T.M; a method N of a type of a package this one imports may be what t.inner.N\(\) runs` `cannot verify M: code that the call may run writes abovep.Made`
	}
}

// Setup is not verified.
func Setup() { abovep.SetMade(T{inner: abovep.QT{}}) }
