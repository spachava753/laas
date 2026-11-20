package q

import (
	"io"

	"cycles/r34/p"
)

// T implements p.Sink by writing to the writer it is given.
type T struct{}

func (T) Take(w io.Writer) int { w.Write([]byte("x")); return 0 }

func Wire() int {
	var s p.Sink = T{}
	return p.F(s, p.W{S: s})
}
