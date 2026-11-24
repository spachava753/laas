// Package chainreport reasons about chainstats across calls of chainapp.
package chainreport

import (
	"chainapp"
	"chainstats"
)

// Twice claims the count is the same around chainapp.Run, which lists the
// state of chainhandler, whose state covers that of chainstats.
//
// @Modifies chainapp
// @Ensures same
func Twice() (same bool) {
	a := chainstats.Count()
	chainapp.Run()
	b := chainstats.Count()
	return a == b // want `^vego: postcondition may not hold: same$`
}

// Quiet keeps the count across a call that changes nothing.
//
// @Ensures same
func Quiet() (same bool) {
	a := chainstats.Count()
	chainapp.RunOther()
	b := chainstats.Count()
	return a == b
}

// Run covers what chainapp.Run changes by naming chainapp.
//
// @Modifies chainapp
// @Ensures True
func Run() {
	chainapp.Run()
}
