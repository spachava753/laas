// Package unread has a comment that looks like an annotation and is not
// read as one. Whatever it was meant to say is missing from the proofs of
// the package, so none of its contracts may be relied on from elsewhere.
package unread

// Value has a contract that holds, and an assertion written with a keyword
// of another language.
//
// @Ensures r = 0
func Value() (r int) {
	// @Check False // want `vego: unknown annotation "Check"; an annotation starts with one of .*`
	return 0
}

// Other has nothing wrong with it, but the unread comment may have been
// meant for any function of the package.
//
// @Ensures r = 1
func Other() (r int) {
	return 1
}

// Sized has a clause in its doc comment that a type cannot have. It may
// have been meant for a function.
//
// @Requires False // want `vego: Requires annotations do not belong on a type; a type can only have Invariant annotations`
type Sized struct{ n int }
