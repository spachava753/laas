package boxed

import (
	"fmt"
	"io"
)

// tally is written through a writer that holds its address.
type tally struct{ n int }

// Write counts.
//
// @Requires t != nil
// @Modifies t
// @Ensures n = |p| And err = nil
func (t *tally) Write(p []byte) (n int, err error) {
	if t.n < 1000000 {
		t.n++
	}
	return len(p), nil
}

var counted tally

// Hand converts the address of counted, so it is not apart from writers.
func Hand() io.Writer { return &counted }

// keep writes through w and claims c.n is kept, which holds when c is
// apart from what w writes.
//
// @Requires w != nil And c != nil
// @Modifies w
// @Ensures c.n' = c.n
func keep(w io.Writer, c *tally) {
	fmt.Fprint(w, "x")
}

// run hands keep the address of counted beside a writer that may write it.
//
// @Requires w != nil
// @Modifies w
// @Ensures True
func run(w io.Writer) {
	keep(w, &counted) // want `vego: the footprint of what is passed to keep as w may hold memory that what is passed as &counted reaches, and keep relies on it not doing so: it is the address of the package-level variable counted, which code elsewhere may hold; take it as a parameter instead`
}
