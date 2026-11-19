// Package sentinelfar does not import io, but uses a contract that names
// io.EOF, and one that names an error variable of sentinellib.
package sentinelfar

import "sentinellib"

// End passes on what sentinellib.End returns.
//
// @Ensures err = nil <-> ok
func End(ok bool) (err error) {
	return sentinellib.End(ok)
}
