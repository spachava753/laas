// Package plog stands for code that is not verified and prints: functions
// that format as fmt does and write to a writer, whose entries in the trust
// file of the tests claim prints. Fprintf is such a function; Checked
// panics on a long format, so its entry requires a bound, which an entry
// with prints may not; the entry of Counted lists more than its writer in
// modifies, which an entry with prints may not either.
package plog

import (
	"fmt"
	"io"
)

// Fprintf formats as fmt.Fprintf does.
func Fprintf(w io.Writer, format string, a ...any) (n int, err error) {
	return fmt.Fprintf(w, format, a...)
}

// Sprintf formats as fmt.Sprintf does.
func Sprintf(format string, a ...any) string {
	return fmt.Sprintf(format, a...)
}

// Checked is Fprintf for a format of at most ten bytes.
func Checked(w io.Writer, format string, a ...any) (n int, err error) {
	if len(format) > 10 {
		panic("long format")
	}
	return fmt.Fprintf(w, format, a...)
}

// Calls counts the calls of Counted.
var Calls int

// Counted is Fprintf, and counts its calls.
func Counted(w io.Writer, format string, a ...any) (n int, err error) {
	Calls++
	return fmt.Fprintf(w, format, a...)
}
