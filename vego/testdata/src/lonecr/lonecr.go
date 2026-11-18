// Package lonecr has a carriage return in the middle of a line, before an
// annotation. An editor may show the annotation on a line of its own; Go
// reads it as the rest of the comment before it.
package lonecr

// F returns fifty.
//
// note// @Ensures r > 100 // want `vego: this file has annotations and a carriage return that does not end a line; remove it, so that what is read is what is seen`
func F(x int) (r int) {
	return 50
}
