// Package unsafelib has a trusted function that runs code it reaches
// through an unsafe.Pointer.
package unsafelib

import "unsafe"

// Holder holds a pointer to a function value, as unsafe.Pointer.
type Holder struct{ P unsafe.Pointer }

// Run calls the function that h.P points to.
func Run(h *Holder) { (*(*func())(h.P))() }

// RunListed is Run, with an entry that lists h under runs.
func RunListed(h *Holder) { (*(*func())(h.P))() }
