// Package exportedmain2 stores exportedp2.Check into letoutq's box from
// code that is not verified, and runs Bump; before, Bump verified and
// Check divided by zero (F10 of the review of the design of F32).
package exportedmain2

import (
	"exportedp2"
	"letoutq"
)

// Run stores Check and runs Bump.
func Run() {
	if b := letoutq.Slot(); b != nil {
		b.H = exportedp2.Check
	}
	exportedp2.Bump()
}
