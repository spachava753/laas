// Package letoutmain installs letoutp's check from code that is not
// verified and then runs Bump.
package letoutmain

import (
	"letoutp"
	"letoutq"
)

// Run is not verified.
func Run() {
	letoutp.Install(letoutq.Slot())
	letoutp.Bump()
}
