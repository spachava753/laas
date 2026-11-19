// Package stateb calls a method of the interface and declares no state.
package stateb

import "statelib"

// Holder holds a connection.
type Holder struct {
	C statelib.Conn
}

// End stops a connection it reads from memory, through no parameter of
// the interface type.
//
// @Requires h != nil And h.C != nil
// @Ensures True
func End(h *Holder) {
	h.C.Stop()
}
