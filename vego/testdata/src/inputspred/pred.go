// Package inputspred has a predicate named as a word of the language of
// inputs that end (F39, part B): under the declaration the predicate keeps
// its meaning where its argument is no reader, and where it is one the
// formula could mean either, which is reported.
package inputspred

import "io"

// @Predicate ends(n) ::= n > 0

// Positive uses the predicate.
//
// @Requires ends(k)
// @Ensures r > 0
func Positive(k int) (r int) {
	return k
}

// Reader applies it to a reader.
//
// @Requires r != nil And ends(r) // want `ends is both a predicate and a state of r; rename the predicate`
// @Ensures True
func Reader(r io.Reader) {
}
