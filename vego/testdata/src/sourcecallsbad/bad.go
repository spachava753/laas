// Package sourcecallsbad holds Calls annotations written where they are
// not read, or that cannot be read (F14 of the design review of F40).
package sourcecallsbad

// @Calls x() // want `a Calls annotation gives x a contract, and its type int is not a function type`
// @Ensures True
func NotFunc(x int) {}

// @Calls g() // want `a Calls annotation names g, which is not a parameter of Missing`
// @Ensures True
func Missing(f func()) {}

// @Calls f // want `a Calls annotation names a function parameter and its parameters, as in // @Calls f\(x\) When 0 <= x, and "f" does not`
// @Ensures True
func Malformed(f func()) {}

// @Calls f(a, b) // want `a Calls annotation names 2 parameters for f, whose type func\(int\) has 1`
// @Ensures True
func Count(f func(int)) {}

// Hook is a named function type, whose contract stands in its own doc
// comment.
type Hook func(x int)

// @Calls h(x) // want `a Calls annotation gives h a contract, and its type sourcecallsbad.Hook has a name`
// @Ensures True
func Named(h Hook) {}

// @Ensures True
func InBody(f func()) {
	// @Calls f() // want `Calls annotation stands inside InBody`
	f()
}
