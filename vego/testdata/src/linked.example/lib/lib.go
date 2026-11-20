// Package lib has a path with a dot, which assembly spells with a middle
// dot and a division slash. Package linkedasm refers to its variable.
package lib

import "errors"

var ErrFar = errors.New("far")

// NotNil relies on ErrFar.
//
// @Ensures r
func NotNil() (r bool) { return ErrFar != nil }
