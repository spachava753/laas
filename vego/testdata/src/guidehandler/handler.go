// Package guidehandler changes the state of guidestats, for the guide.
package guidehandler

import "guidestats"

// Serve counts a request.
//
// @Modifies guidestats
// @Ensures True
func Serve() {
	guidestats.Hit()
}
