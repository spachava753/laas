// Package boxedclient covers what boxedlib changes through its state.
package boxedclient

import (
	"io"

	"boxedlib"
)

// Listed covers Set through the state of boxedlib.
//
// @Modifies boxedlib
// @Ensures True
func Listed() {
	boxedlib.Set(1)
}

// Unlisted does not.
//
// @Ensures True
func Unlisted() {
	boxedlib.Set(1) // want `vego: Set may modify the state of package boxedlib \(boxedlib\.Cfg\), which Unlisted may not modify; list boxedlib in a // @Modifies clause`
}

// Kept reads Get around a call that lists no state.
//
// @Ensures r = s
func Kept() (r, s int) {
	r = boxedlib.Get()
	s = boxedlib.Get()
	return r, s
}

// Lost reads Get around Set.
//
// @Modifies boxedlib
// @Ensures r = s
func Lost() (r, s int) {
	r = boxedlib.Get()
	boxedlib.Set(2)
	s = boxedlib.Get()
	return r, s // want `vego: postcondition may not hold: r = s`
}

// Reads reads the variable of the other package directly.
//
// @Ensures True
func Reads() (r int) {
	return boxedlib.Cfg.N // want `vego: cannot verify Reads: boxedlib\.Cfg is a struct variable of package boxedlib whose address is taken, and reading or naming one of another package is not supported yet; a function of package boxedlib can read it, and a contract here covers what such a function changes by listing the state of package boxedlib`
}

// Names names it in a contract.
//
// @Modifies boxedlib.Cfg // want `vego: in Modifies annotation: boxedlib\.Cfg is a struct variable of package boxedlib whose address is taken, which a contract of another package cannot name yet; list the state of package boxedlib, as // @Modifies boxedlib`
// @Ensures True
func Names() {
	boxedlib.Set(3)
}

// Leak lets the address of boxedlib.Buf out, which boxedlib relies on not
// happening.
func Leak() io.Writer {
	return &boxedlib.Buf // want `vego: the address of boxedlib\.Buf is let out here, but proofs in package boxedlib rely on it being handed only to trusted functions that neither keep it nor run code that could be handed it`
}
