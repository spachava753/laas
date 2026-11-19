// Package gonereader is built with gonemid, which changes gonelib.ErrGone,
// so it does not take ErrGone to hold the error it was declared with.
package gonereader // want `vego: gonelib.ErrGone is changed at gonemid.go:6 in package gonemid, which this package is built with, but proofs in package gonelib rely on it being the error it was declared with`

import (
	"gonelib"
	_ "gonemid"
)

// Gone returns ErrGone.
//
// @Ensures err != nil
func Gone() (err error) {
	return gonelib.ErrGone // want `vego: cannot verify Gone: gonelib.ErrGone is changed at gonemid.go:6 in package gonemid, which this package is built with, so it is not known to hold the error it was declared with`
}
