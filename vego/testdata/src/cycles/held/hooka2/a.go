// Package hooka2 is hooka with Fire one level down, behind hookc.G.
package hooka2

import (
	"cycles/held/hookb"
	"cycles/held/hookc"
)

// @Ensures True
func h() (n int) { return X() } // want `this call may not end: h calls X at a.go:\d+:\d+, X calls hookc.G\(\) at a.go:\d+:\d+, which may run h; G reads a package-level variable that can hold code`

// Setup registers h; it is not verified.
func Setup() {
	hookb.Register(h)
}

// @Ensures True
func X() (n int) {
	return hookc.G() // want `the contract of cycles/held/hookc.G cannot be used: its verification failed`
}
