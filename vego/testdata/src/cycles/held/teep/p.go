// Package teep hands teeq.Read1 a reader that code which is not verified
// made with io.TeeReader around a W, whose Write calls back into G. The
// base found the cycle by the strict reading of r, which reaches
// everything; since F43 the call reaches what teeq.Read1 runs (Read), and
// the teeReader of io runs the W it kept at the TeeReader call. It is the
// assumption "What a proof assumes" states of code that is not verified,
// which carries the narrowing of an interface operand by a summary as it
// carries a call r.Read() made in G itself.
package teep

import (
	"io"
	"strings"

	"cycles/held/teeq"
)

// W writes and calls back into G; it is not verified.
type W struct{}

func (W) Write(b []byte) (int, error) {
	G(Made)
	return len(b), nil
}

// Made is set by code that is not verified.
var Made io.Reader

// Setup is not verified.
func Setup() { Made = io.TeeReader(strings.NewReader("x"), W{}) }

// @Requires r != nil
// @Modifies r
// @Ensures True
func G(r io.Reader) { teeq.Read1(r) }
