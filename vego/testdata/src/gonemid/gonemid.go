// Package gonemid changes the sentinel of gonelib, and is not verified.
package gonemid

import "gonelib"

func init() { gonelib.ErrGone = nil } // want `vego: gonelib.ErrGone may be changed here, but proofs in package gonelib rely on it being the error it was declared with`

func change() {
	gonelib.ErrOpaque = nil // want `vego: gonelib.ErrOpaque may be changed here, but proofs in package gonelib rely on it being the error it was declared with`
	gonelib.ErrTarget = nil // want `vego: gonelib.ErrTarget may be changed here, but proofs in package gonelib rely on it being the error it was declared with`
}
