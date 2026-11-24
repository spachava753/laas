// Package exportedmain stores exportedp.Check into letoutq's box from code
// that is not verified, and runs Bump; before, Bump verified and Check
// divided by zero.
package exportedmain

import (
	"exportedp"
	"letoutq"
)

// Run is not verified.
func Run() {
	if b := letoutq.Slot(); b != nil {
		b.H = exportedp.Check
	}
	exportedp.Bump()
}
