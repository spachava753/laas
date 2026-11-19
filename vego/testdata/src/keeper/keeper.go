// Package keeper is not verified. Keep keeps the error it is given, and
// Flush later runs a method of it.
package keeper

var kept error

// Keep keeps an error.
func Keep(e error) { kept = e }

// KeepUnlisted keeps an error too, and its entry does not list it under runs.
func KeepUnlisted(e error) { kept = e }

// Flush runs a method of the error Keep kept.
func Flush() {
	if kept != nil {
		_ = kept.Error()
	}
}
