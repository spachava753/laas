// Package gonereader is built with gonemid, which changes gonelib.ErrGone,
// so it does not take ErrGone to hold the error it was declared with.
package gonereader // want `vego: gonelib.ErrGone is changed at gonemid.go:6 in package gonemid, which this package is built with, but proofs in package gonelib rely on it being the error it was declared with` `vego: gonelib.ErrOpaque is changed at gonemid.go:9 in package gonemid, which this package is built with, but proofs in package gonelib rely on it being the error it was declared with` `vego: gonelib.ErrTarget is changed at gonemid.go:10 in package gonemid, which this package is built with, but proofs in package gonelib rely on it being the error it was declared with`

import (
	"errors"

	"gonelib"
	_ "gonemid"
)

// Gone returns ErrGone.
//
// @Ensures err != nil
func Gone() (err error) {
	return gonelib.ErrGone // want `vego: cannot verify Gone: gonelib.ErrGone is changed at gonemid.go:6 in package gonemid, which this package is built with, so it is not known to hold the error it was declared with`
}

// Opaque returns ErrOpaque, which gonemid changes.
//
// @Ensures True
func Opaque() (err error) {
	return gonelib.ErrOpaque // want `vego: cannot verify Opaque: gonelib.ErrOpaque is changed at gonemid.go:9 in package gonemid, which this package is built with, so it is not known to hold the error it was declared with`
}

// Aliased compares ErrAliased with an error of this package. gonemid
// changes ErrTarget, so ErrAliased holds the value ErrTarget had when
// ErrAliased was initialised, and nothing more is known of it. The proofs
// of this package do not rely on ErrTarget, as the package clause shows.
//
// @Ensures True
func Aliased() (same bool) {
	return gonelib.ErrAliased == errMine
}

var errMine = errors.New("mine")

// AliasedNotNil cannot show that it is not nil.
//
// @Ensures r
func AliasedNotNil() (r bool) {
	return gonelib.ErrAliased != nil // want `vego: postcondition may not hold: r`
}
