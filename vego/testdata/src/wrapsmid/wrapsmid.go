// Package wrapsmid puts an error of its own into io.EOF. Packages that do
// not depend on each other are initialised in the order of their paths, so
// this runs before wrapsp is initialised, and ErrRead wraps it. Nothing
// this package is built with relies on io.EOF, so nothing is reported here.
package wrapsmid

import "io"

type weird []int

func (weird) Error() string { return "weird" }

func init() { io.EOF = weird{1} }
