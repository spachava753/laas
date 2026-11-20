// Package globalsembed reads a variable whose value a go:embed directive
// gives.
package globalsembed

import _ "embed"

//go:embed hello.txt
var greeting string

// Greeting would return the empty string if the variable had its zero
// value.
//
// @Ensures |r| = 0
func Greeting() (r string) {
	return greeting // want `vego: postcondition may not hold: \|r\| = 0`
}

//go:embed hello.txt

var spaced string

// Spaced reads a variable whose directive a blank line separates from it.
//
// @Ensures |r| = 0
func Spaced() (r string) {
	return spaced // want `vego: postcondition may not hold: \|r\| = 0`
}

var (
	//go:embed hello.txt

	// The comment above is a directive all the same.
	inBlock string
)

// InBlock reads a variable of a block whose directive a comment separates
// from it.
//
// @Ensures |r| = 0
func InBlock() (r string) {
	return inBlock // want `vego: postcondition may not hold: \|r\| = 0`
}
