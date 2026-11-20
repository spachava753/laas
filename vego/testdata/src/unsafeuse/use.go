// Package unsafeuse hands a value that holds an unsafe.Pointer to a
// trusted function and to a function value.
package unsafeuse

import "unsafelib"

// Call hands h to a trusted function whose entry does not list it under
// runs.
//
// @Requires h != nil
// @Ensures True
func Call(h *unsafelib.Holder) {
	unsafelib.Run(h) // want `vego: cannot verify Call: h is passed to Run, which is trusted, and is a value of type \*unsafelib.Holder, which is or holds an unsafe.Pointer; Run could run code through it that nobody has seen`
}

// CallListed hands it to one whose entry does.
//
// @Requires h != nil
// @Ensures True
func CallListed(h *unsafelib.Holder) { unsafelib.RunListed(h) }

// Use takes a holder.
//
// @Ensures True
type Use func(h *unsafelib.Holder)

// CallValue hands h to a function value.
//
// @Requires f != nil
// @Ensures True
func CallValue(f Use, h *unsafelib.Holder) {
	f(h) // want `vego: cannot verify CallValue: h is passed to the function value f and is a value of type \*unsafelib.Holder, which can hold an unsafe.Pointer; the value may come from code that is not verified, which could run code through it that nobody has seen`
}
