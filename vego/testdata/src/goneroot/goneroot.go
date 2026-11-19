// Package goneroot is built with both gonelib and gonemid, and is where the
// change and the proof that relies on it meet.
package goneroot // want `vego: gonelib.ErrGone is changed at gonemid.go:6 in package gonemid, which this package is built with, but proofs in package gonelib rely on it being the error it was declared with` `vego: gonelib.ErrOpaque is changed at gonemid.go:9 in package gonemid, which this package is built with, but proofs in package gonelib rely on it being the error it was declared with` `vego: gonelib.ErrTarget is changed at gonemid.go:10 in package gonemid, which this package is built with, but proofs in package gonelib rely on it being the error it was declared with`

import (
	"gonelib"
	_ "gonemid"
)

// Use calls Fail.
func Use() error { return gonelib.Fail(false) }
