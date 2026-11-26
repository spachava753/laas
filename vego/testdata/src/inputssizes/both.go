// Package inputssizes reads whole files under both declarations.
package inputssizes

import (
	"io"
	"os"
	"strings"
)

// Config reads a file and upper-cases it, which the declared memory bounds.
//
// @Ensures True
func Config(path string) (text string, err error) {
	data, err := os.ReadFile(path)
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
