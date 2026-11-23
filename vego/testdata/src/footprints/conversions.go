package footprints

import (
	"bufio"
	"bytes"
	"fmt"
	"io"
	"log"
	"strings"
)

// The conversions of step 5: a value of the project as an interface value
// whose methods write behind their receiver, whose footprint is the struct
// it points to, fixed at the conversion.

// Incr is incremented.
type Incr interface {
	// @Receiver r
	// @Modifies r
	// @Ensures True
	Inc()
}

// Clicker counts up to a bound in its own struct.
type Clicker struct{ n int }

// @Requires c != nil
// @Modifies c
// @Ensures True
func (c *Clicker) Inc() {
	if c.n < 1000 {
		c.n++
	}
}

// Bump increments c through an Incr (E5).
//
// @Requires c != nil
// @Modifies c
// @Ensures True
func Bump(c *Clicker) {
	var i Incr = c
	i.Inc()
}

// BumpUnlisted is Bump without c listed.
//
// @Requires c != nil
// @Ensures True
func BumpUnlisted(c *Clicker) {
	var i Incr = c
	i.Inc() // want `vego: i.Inc may modify the footprint of i, which BumpUnlisted may not modify; it is the memory that c points to, converted at conversions.go:\d+:\d+; list c in a // @Modifies clause`
}

// BumpLocal increments a counter it made, which needs no Modifies.
//
// @Ensures True
func BumpLocal() {
	c := &Clicker{}
	var i Incr = c
	i.Inc()
	i.Inc()
}

// ReadAfter reads the counter after a call through the Incr, which may
// have changed it (E3).
//
// @Ensures r = 0
func ReadAfter() (r int) {
	c := &Clicker{}
	var i Incr = c
	i.Inc()
	return c.n // want `vego: postcondition may not hold: r = 0`
}

// MayBeSame keeps d across a call through an Incr made of c, which may be
// the same counter.
//
// @Requires c != nil And d != nil
// @Modifies c
// @Ensures d.n' = d.n
func MayBeSame(c *Clicker, d *Clicker) {
	var i Incr = c
	i.Inc()
} // want `vego: postcondition may not hold: d.n' = d.n`

// Linked writes the counter its pointer field points to.
type Linked struct {
	n    int
	next *Linked
}

// @Requires l != nil
// @Modifies l.next
// @Ensures True
func (l *Linked) Inc() {
	if l.next != nil && l.next.n < 1000 {
		l.next.n++
	}
}

// BumpLinked converts a Linked, whose Inc writes outside its struct.
//
// @Requires l != nil
// @Modifies l, l.next
// @Ensures True
func BumpLinked(l *Linked) {
	var i Incr = l // want `vego: Inc may modify what it calls l.next, which Incr.Inc may not modify; it is not part of the footprint of \*Linked, which is the struct l points to`
	i.Inc()
}

// ConvertedInLoop converts c in each iteration and calls through the last
// conversion after the loop. At the head of the loop the home of that
// conversion is new, and nothing is known of its row (F18 of the design
// review), so the call is refused.
//
// @Requires c != nil And k >= 0
// @Modifies c
// @Ensures True
func ConvertedInLoop(c *Clicker, k int) {
	var i Incr
	// @Variant k - j
	for j := 0; j < k; j++ {
		i = c
	}
	if i != nil {
		i.Inc() // want `vego: i.Inc may modify the footprint of i, which ConvertedInLoop may not modify`
	}
}

// Quiet writes nothing when it is nil.
type Quiet struct{ n int }

// @Requires |p| <= 100
// @Modifies q
// @Ensures 0 <= n <= |p|
func (q *Quiet) Put(p []byte) (n int) {
	if q == nil {
		return 0
	}
	if q.n < 1000 {
		q.n++
	}
	return 0
}

// PutsNil converts a nil pointer, whose footprint is empty, and lists
// nothing.
//
// @Ensures True
func PutsNil() {
	var q *Quiet
	var s Sink = q
	_ = s.Put(nil)
}

// report logs the number of items through l, and keeps what items holds.
//
// @Requires l != nil And ready(l) And |items| > 0 And |items[0]| = 1
// @Modifies l
// @Ensures |items'[0]| = 1
func report(l *log.Logger, items []string) {
	l.Println(len(items))
}

// LogsReport hands report a logger it made over w, with data: what the
// logger writes is new or lies in the footprint of w, as the contract of
// log.New says.
//
// @Requires w != nil And |items| > 0 And |items[0]| = 1
// @Modifies w
// @Ensures True
func LogsReport(w io.Writer, items []string) {
	l := log.New(w, "", 0)
	report(l, items)
}

// Greets writes a Buffer, whose Write may panic when the buffer is too
// large to grow; its length cannot be stated yet.
//
// @Ensures True
func Greets() {
	var b bytes.Buffer
	b.WriteString("!") // want `vego: cannot verify Greets: it calls \(\*bytes.Buffer\).WriteString, which grows the buffer: the methods of Buffer that write may panic when the buffer is too large to grow, and the length of a Buffer cannot be stated yet, so no contract of them can say when they return. A trusted contract for it without such a bound would be false`
}

// FormatsIntoBuffer converts a Buffer to an io.Writer, refused for the same
// reason.
//
// @Ensures True
func FormatsIntoBuffer() {
	var b bytes.Buffer
	fmt.Fprintf(&b, "x") // want `vego: cannot verify FormatsIntoBuffer: converting a value of type \*bytes.Buffer to io.Writer is not supported yet: the methods of Buffer that write may panic when the buffer is too large to grow`
}

// BuildsName writes a Builder, refused for the same reason.
//
// @Ensures True
func BuildsName() {
	var b strings.Builder
	b.WriteByte('x') // want `vego: cannot verify BuildsName: it calls \(\*strings.Builder\).WriteByte, which grows the buffer`
}

// WrapsWriter converts a Writer it made over w to an io.Writer, whose
// Write calls through the writer it keeps.
//
// @Requires w != nil
// @Modifies w
// @Ensures True
func WrapsWriter(w io.Writer) (err error) {
	bw := bufio.NewWriter(w)
	var x io.Writer = bw // want `vego: cannot verify WrapsWriter: Write may call through a function value or an interface value`
	_, err = x.Write([]byte("x"))
	return err
}

// BumpInLoop converts c before the loop and calls through it in the loop,
// whose head keeps the row of a home made before it.
//
// @Requires c != nil And k >= 0
// @Modifies c
// @Ensures True
func BumpInLoop(c *Clicker, k int) {
	var i Incr = c
	// @Variant k - j
	for j := 0; j < k; j++ {
		i.Inc()
	}
}
