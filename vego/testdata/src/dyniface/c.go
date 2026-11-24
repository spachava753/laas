// Package dyniface writes through a writer whose Write calls dynlib.ViaIface.
package dyniface

import (
	"io"

	"dynlib"
)

type writer struct{}

// Write counts through dynlib, and is not verified.
func (writer) Write(p []byte) (int, error) {
	dynlib.ViaIface()
	return len(p), nil
}

// Around claims Count is the same around a write through w. Before, it
// verified and was false.
//
// @Requires w != nil
// @Modifies w
// @Ensures r
func Around(w io.Writer) (r bool) {
	a := dynlib.Count
	w.Write([]byte("x")) // want `^vego: w.Write may modify the state of package dynlib \(dynlib.Count\), which Around may not modify; list dynlib in a // @Modifies clause$`
	return dynlib.Count == a
}
