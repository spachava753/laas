// Package inputsbig reads whole files under both declarations, with more
// inputs than five times the memory, which a file read whole cannot be.
package inputsbig

import (
	"io"
	"os"
	"strings"
)

// Config reads a file and upper-cases it, which the declared memory bounds.
//
// @Ensures True
func Config(path string) (text string, err error) {
	data, err := os.ReadFile(path) // want `precondition of ReadFile may not hold under the declared memory: Inputs \+ 1 <= 5 \* Memory \+ 65536`
	if err != nil {
		return "", err
	}
	return strings.ToUpper(string(data)), nil
}

// All reads standard input and joins it to itself.
//
// @Ensures True
func All() (text string) {
	data, _ := io.ReadAll(os.Stdin)
	s := string(data)
	return s + s
}
