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
