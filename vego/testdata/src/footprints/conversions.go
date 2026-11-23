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
		i.Inc() // want `vego: i.Inc may modify the footprint of i, which ConvertedInLoop may not modify; i holds a value converted at conversions.go:\d+:\d+ in a loop, and at the head of the loop nothing is known of the footprint of a value converted in an earlier iteration; convert it after the loop, or before it`
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

// Scores is a slice whose Inc writes its first element, held by value in an
// interface value, whose footprint is the array up to its capacity.
type Scores []int

// @Modifies s
// @Ensures True
func (s Scores) Inc() {
	if len(s) > 0 && s[0] < 1000 {
		s[0]++
	}
}

// GrowsAfter converts s, appends to it past its capacity, and calls through
// the interface value, which writes the old array and not the new one.
//
// @Requires |s| = 1 And cap(s) = 1
// @Modifies s
// @Ensures r = 7
func GrowsAfter(s Scores) (r int) {
	var i Incr = s
	t := append(s, 7)
	i.Inc()
	return t[1]
}

// KeepsOldArray is GrowsAfter reading the old array, which the call may
// have written.
//
// @Requires |s| = 1 And cap(s) = 1 And s[0] = 3
// @Modifies s
// @Ensures r = 3
func KeepsOldArray(s Scores) (r int) {
	var i Incr = s
	i.Inc()
	return s[0] // want `vego: postcondition may not hold: r = 3`
}

// ByValue is a struct held by value whose Inc writes what its pointer
// field points to, which is no part of its footprint.
type ByValue struct{ p *Clicker }

// @Requires b.p != nil
// @Modifies b.p
// @Ensures True
func (b ByValue) Inc() {
	b.p.Inc()
}

// BumpByValue converts a ByValue.
//
// @Requires c != nil
// @Modifies c
// @Ensures True
func BumpByValue(c *Clicker) {
	var i Incr = ByValue{p: c} // want `vego: Inc may modify what it calls b.p, which Incr.Inc may not modify; it is not part of the footprint of ByValue, which is empty: a value held by value is copied for each call of its methods, and owns nothing its fields point to; keep what the method writes in a struct and convert a pointer to it, or pass what it writes as an argument`
	i.Inc()
}

// BumpTwice converts c twice, and each footprint is its struct.
//
// @Requires c != nil
// @Modifies c
// @Ensures True
func BumpTwice(c *Clicker) {
	var i Incr = c
	var j Incr = c
	i.Inc()
	j.Inc()
}

// GrowsUnlisted is GrowsAfter without s listed.
//
// @Requires |s| = 1 And cap(s) = 1
// @Ensures True
func GrowsUnlisted(s Scores) {
	var i Incr = s
	i.Inc() // want `vego: i.Inc may modify the footprint of i, which GrowsUnlisted may not modify; it is the array that s holds, up to its capacity, converted at conversions.go:\d+:\d+; list s in a // @Modifies clause`
}

// useBoth increments i and keeps what log holds.
//
// @Requires i != nil And |log| = 1 And |log[0]| = 2
// @Modifies i
// @Ensures |log'[0]| = 2
func useBoth(i Incr, log []string) {
	i.Inc()
}

// UsesConversion hands useBoth a counter it was given, converted at the
// call, and a slice of strings, which no value of that type can refer to a
// Clicker through (F21).
//
// @Requires c != nil And |log| = 1 And |log[0]| = 2
// @Modifies c
// @Ensures True
func UsesConversion(c *Clicker, log []string) {
	useBoth(c, log)
}

// UsesConvertedVar converts c into a variable first.
//
// @Requires c != nil And |log| = 1 And |log[0]| = 2
// @Modifies c
// @Ensures True
func UsesConvertedVar(c *Clicker, log []string) {
	var i Incr = c
	useBoth(i, log)
}

// useWith increments i and keeps what other points to.
//
// @Requires i != nil And other != nil
// @Modifies i
// @Ensures other.n' = other.n
func useWith(i Incr, other *Clicker) {
	i.Inc()
}

// UsesConversionAlias hands useWith a converted counter and a counter that
// may be the same one.
//
// @Requires c != nil And d != nil
// @Modifies c
// @Ensures True
func UsesConversionAlias(c *Clicker, d *Clicker) {
	useWith(c, d) // want `vego: the footprint of what is passed to useWith as c may hold memory that what is passed as d reaches, and useWith relies on it not doing so: the footprint of c is the struct that c points to, which a value of type \*Clicker can refer to`
}

// CounterShelf hands out a counter it holds.
type CounterShelf interface {
	// @Ensures c != nil
	Peek() (c *Clicker)
}

// BumpPeeked converts a counter a call returned, which may be memory of
// the caller.
//
// @Requires g != nil
// @Ensures True
func BumpPeeked(g CounterShelf) {
	var i Incr = g.Peek()
	i.Inc() // want `vego: i.Inc may modify the footprint of i, which BumpPeeked may not modify; it is the memory that g.Peek\(\) points to, which the call returned without saying that it is new, so it may be memory of the caller, converted at conversions.go:\d+:\d+; take it as a parameter and list it in a // @Modifies clause, or have the contract of the call say that it is new`
}

// ConvWithin says that the counter lies in the footprint of the value it
// was converted to, which the row defined at the conversion holds.
//
// @Requires c != nil
// @Ensures i != nil And within(c, i)
func ConvWithin(c *Clicker) (i Incr) {
	return c
}

// useAny increments i and keeps how many values xs holds.
//
// @Requires i != nil
// @Modifies i
// @Ensures True
func useAny(i Incr, xs []any) {
	i.Inc()
}

// UsesConversionAny hands useAny a converted counter and values of type
// any, which can hold the counter.
//
// @Requires c != nil
// @Modifies c
// @Ensures True
func UsesConversionAny(c *Clicker, xs []any) {
	useAny(c, xs) // want `the footprint of c is the struct that c points to, which a value of type \[\]any can refer to`
}

// UsesNewConversion converts a counter it made, which the strings cannot
// reach either.
//
// @Requires |log| = 1 And |log[0]| = 2
// @Ensures True
func UsesNewConversion(log []string) {
	useBoth(&Clicker{}, log)
}
