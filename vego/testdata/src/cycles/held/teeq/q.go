// Package teeq reads from what it is handed.
package teeq

import "io"

// @Requires r != nil
// @Modifies r
// @Ensures True
func Read1(r io.Reader) {
	buf := make([]byte, 1)
	_, _ = r.Read(buf)
}
