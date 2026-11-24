// Package mustcompile compiles patterns with regexp.MustCompile, whose entry
// holds only where the initialiser of a package-level variable calls it
// (step 6 of F32).
package mustcompile

import "regexp"

var word = regexp.MustCompile("^[a-z]+$")

// isWord matches; word is not nil, by the entry of MustCompile.
//
// @Ensures True
func isWord(s string) (ok bool) {
	return word.MatchString(s)
}

// keep returns its pattern.
//
// @Requires re != nil
// @Ensures r = re
func keep(re *regexp.Regexp) (r *regexp.Regexp) { return re }

var kept = keep(regexp.MustCompile("x+"))

// isKept matches with a pattern handed through a verified function.
//
// @Ensures True
func isKept(s string) (ok bool) {
	return kept.MatchString(s)
}

// compileHere compiles inside a function, where a deferred recover could
// go on after the panic.
//
// @Ensures True
func compileHere(s string) (ok bool) {
	re := regexp.MustCompile("^a") // want `vego: cannot verify compileHere: MustCompile panics when it fails, and its trusted contract holds only where the initialiser of a package-level variable calls it, outside every function: a panic there stops the program, or the plugin that holds the package, before any code reads the variable; elsewhere call a function that returns an error and check it, as regexp.Compile`
	return re.MatchString(s)
}

var lazy = func() *regexp.Regexp {
	return regexp.MustCompile("^b") // want `vego: MustCompile panics when it fails, and its trusted contract holds only where the initialiser of a package-level variable calls it`
}()

var later *regexp.Regexp

// init compiles in an init function, which runs after every initialiser
// and is a function: a deferred recover there could catch the panic.
//
// @Modifies later
// @Ensures True
func init() {
	later = regexp.MustCompile("^c") // want `vego: cannot verify init: MustCompile panics when it fails`
}
