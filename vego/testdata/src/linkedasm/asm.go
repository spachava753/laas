// Package linkedasm reads an error variable that its assembly refers to.
package linkedasm

import "errors"

var ErrAsm = errors.New("asm")

func load() error

// NotNil relies on ErrAsm.
//
// @Ensures r
func NotNil() (r bool) {
	return ErrAsm != nil // want `vego: cannot verify NotNil: ErrAsm is referred to in assembly at asm_amd64.s:5, so it is not known to hold the error it was declared with`
}
