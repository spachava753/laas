// Package recclosuresbad holds contracts of recursive closures written
// where they are not read, each an error (F14 of the design review of F40).
package recclosuresbad

// AboveDeclaration writes the contract above var f.
//
// @Ensures True
func AboveDeclaration() {
	// @Requires True // want `Requires annotation stands above the declaration of f; the contract of a recursive closure stands directly above its assignment f = func\.\.\.`
	var f func()
	f = func() {}
	f()
}

// AboveOther writes a contract above an assignment that is no closure.
//
// @Ensures True
func AboveOther() {
	x := 0
	// @Ensures x' = 1 // want `Ensures annotation stands inside AboveOther; put it in the doc comment of the function, or, for the contract of a recursive closure, directly above its assignment v = func\.\.\., after var v func\(\.\.\.\)`
	x = 1
	_ = x
}

// InvariantThere writes an Invariant in the contract of a closure.
//
// @Ensures True
func InvariantThere() {
	var f func()
	// @Invariant True // want `Invariant annotation stands in the contract of the closure f, directly above its assignment, where only Requires, Modifies, Variant, and Ensures belong; put it between statements`
	f = func() {}
	f() // want `the contract of the closure f cannot be used: some annotations of the closure f could not be read, as reported at them`
}

// ExitsThere writes an Exits in the contract of a closure.
//
// @Ensures True
func ExitsThere() {
	var f func()
	// @Exits // want `an Exits annotation cannot stand above a recursive closure: a recursive closure may not end the process`
	f = func() {}
	f() // want `the contract of the closure f cannot be used: some annotations of the closure f could not be read, as reported at them`
}

// Unverified has a closure with a contract in a function that is not
// verified.
func Unverified() {
	var f func()
	// @Ensures True
	f = func() {} // want `the closure f has a contract, but Unverified around it is not verified, so nothing reads it; annotate Unverified`
	f()
}
