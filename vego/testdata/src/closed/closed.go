// Package closed holds struct variables whose address is closed, and twins
// whose address is not, beside writes through a writer.
package closed

import (
	"bytes"
	"fmt"
	"io"
	"strings"
	"sync"
)

var sb strings.Builder

// note writes into sb and through w, and keeps the length of sb across
// the write through w: no writer's footprint holds sb.
//
// @Requires w != nil And |sb| <= 100
// @Modifies sb, w
// @Ensures |sb'| = |sb| + 1
func note(w io.Writer) {
	sb.WriteString("x")
	fmt.Fprint(w, "y")
}

// noteFormatted formats into sb, which converts its address at a call
// that only writes it.
//
// @Requires w != nil And |sb| <= 100
// @Modifies sb, w
// @Ensures True
func noteFormatted(w io.Writer) {
	fmt.Fprintf(&sb, "%d", 1)
	fmt.Fprint(w, "y")
}

var mu sync.Mutex

// locked writes through w while it holds mu, and still holds it after.
//
// @Requires w != nil And ~held(mu)
// @Modifies mu, w
// @Ensures ~held(mu')
func locked(w io.Writer) {
	mu.Lock()
	fmt.Fprint(w, "y")
	mu.Unlock()
}

var open strings.Builder

// Open lets the address of open out, so a writer may hold it.
func Open() io.Writer { return &open }

// noteOpen loses the length of open across the write through w.
//
// @Requires w != nil And |open| <= 100
// @Modifies open, w
// @Ensures |open'| = |open| + 1
func noteOpen(w io.Writer) {
	open.WriteString("x")
	fmt.Fprint(w, "y")
} // want `vego: postcondition may not hold: \|open'\| = \|open\| \+ 1`

var mu2 sync.Mutex

// Lock2 is a method value of mu2's Lock, which is not closed.
var Lock2 = mu2.Lock

// lockedOpen loses whether it holds mu2 across the write through w.
//
// @Requires w != nil And ~held(mu2)
// @Modifies mu2, w
// @Ensures True
func lockedOpen(w io.Writer) {
	mu2.Lock()
	fmt.Fprint(w, "y")
	mu2.Unlock() // want `vego: precondition of Unlock may not hold: held\(m\)`
}

var bb bytes.Buffer

// Peek returns the bytes of bb, a result that holds memory of bb, so its
// address is not closed.
func Peek() []byte { return bb.Bytes() }

// noteBytes loses the length of bb across the write through w.
//
// @Requires w != nil And |bb| <= 100
// @Modifies bb, w
// @Ensures |bb'| = |bb| + 1
func noteBytes(w io.Writer) {
	bb.WriteString("x")
	fmt.Fprint(w, "y")
} // want `vego: postcondition may not hold: \|bb'\| = \|bb\| \+ 1`

// Tally counts what is written to it.
type Tally struct{ n int }

// Write counts, and is verified, so a converted address handed to it is
// not closed.
//
// @Requires t != nil
// @Modifies t
// @Ensures n = |p| And err = nil
func (t *Tally) Write(p []byte) (n int, err error) {
	if t.n < 1000000 {
		t.n++
	}
	return len(p), nil
}

var tally Tally

// Count writes into tally through fmt, which runs its Write.
func Count() { fmt.Fprint(&tally, "x") }

// keepTally loses tally.n across the write through w.
//
// @Requires w != nil
// @Modifies w
// @Ensures tally.n' = tally.n
func keepTally(w io.Writer) {
	fmt.Fprint(w, "y")
} // want `vego: postcondition may not hold: tally\.n' = tally\.n`

var printed Tally

// Show formats the address of printed, which fmt may hand to its methods.
func Show() string { return fmt.Sprint(&printed) }

// keepPrinted loses printed.n across the write through w.
//
// @Requires w != nil
// @Modifies w
// @Ensures printed.n' = printed.n
func keepPrinted(w io.Writer) {
	fmt.Fprint(w, "y")
} // want `vego: postcondition may not hold: printed\.n' = printed\.n`

var once sync.Once

// onced runs once.Do, which hands the function it calls nothing, and keeps
// what it ensures across the write through w.
//
// @Requires w != nil And ~running(once)
// @Modifies once, w
// @Ensures ~running(once')
func onced(w io.Writer) {
	once.Do(func() {})
	fmt.Fprint(w, "y")
}

var mu3 sync.Mutex

// Spawn locks mu3 on another goroutine, so its address is not closed.
func Spawn() { go mu3.Lock() }

// lockedSpawn loses whether it holds mu3 across the write through w.
//
// @Requires w != nil And ~held(mu3)
// @Modifies mu3, w
// @Ensures True
func lockedSpawn(w io.Writer) {
	mu3.Lock()
	fmt.Fprint(w, "y")
	mu3.Unlock() // want `vego: precondition of Unlock may not hold: held\(m\)`
}
