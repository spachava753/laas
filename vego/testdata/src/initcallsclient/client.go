// Package initcallsclient reads what initcallslib published of its
// initialisers.
package initcallsclient

import "initcallslib"

// Third reads the last element of the table.
//
// @Ensures True
func Third() (r int) {
	return initcallslib.Table[2]
}

// Fourth reads past it.
//
// @Ensures True
func Fourth() (r int) {
	return initcallslib.Table[3] // want `vego: index may be out of range`
}

// IsWord matches with the pattern, which is not nil.
//
// @Ensures True
func IsWord(s string) (ok bool) {
	return initcallslib.Word.MatchString(s)
}

// ReadSeven knows the value.
//
// @Ensures r = 7
func ReadSeven() (r int) {
	return initcallslib.Seven
}

// NotEight does not hold.
//
// @Ensures r = 8
func NotEight() (r int) {
	return initcallslib.Seven // want `vego: postcondition may not hold: r = 8`
}
