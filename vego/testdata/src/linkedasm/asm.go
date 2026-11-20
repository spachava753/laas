// Package linkedasm reads error variables that its assembly refers to: one
// of its own, and one of a package whose path has a dot.
package linkedasm

import (
	"errors"

	"linked.example/lib"
)

var ErrAsm = errors.New("asm")

func load() error

func clear()

// NotNil relies on ErrAsm.
//
// @Ensures r
func NotNil() (r bool) {
	return ErrAsm != nil // want `vego: cannot verify NotNil: ErrAsm is referred to in assembly at asm_amd64.s:5, so it is not known to hold the error it was declared with`
}

// FarNotNil relies on lib.ErrFar.
//
// @Ensures r
func FarNotNil() (r bool) {
	return lib.ErrFar != nil // want `vego: cannot verify FarNotNil: lib.ErrFar is referred to in assembly at asm_amd64.s:14 in this package, so it is not known to hold the error it was declared with`
}
