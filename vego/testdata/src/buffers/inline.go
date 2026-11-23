package buffers

import (
	"bytes"
	"strings"
)

// Printer holds a Builder by value, so it owns what the Builder owns.
type Printer struct {
	lines int
	out   strings.Builder
}

// Print writes s and a newline to the Builder p holds, under Modifies p.
//
// @Requires p != nil And |p.out| <= 1000000 And |s| <= 1000 And p.lines < 1000000
// @Modifies p
// @Ensures |p.out'| = |p.out| + |s| + 1 And p.lines' = p.lines + 1
func (p *Printer) Print(s string) {
	p.out.WriteString(s)
	p.out.WriteByte('\n')
	p.lines++
}

// PrintUnlisted writes the Builder p holds without listing p.
//
// @Requires p != nil And |p.out| <= 1000000
// @Ensures True
func PrintUnlisted(p *Printer) {
	p.out.WriteByte('x') // want `WriteByte may modify p.out, which PrintUnlisted may not modify; list it in a // @Modifies clause, as p.out`
}

// PrintTwice prints twice: what the Builder owns after the first call is
// what it owned or new memory, so the second call writes only what p owns.
//
// @Requires p != nil And |p.out| <= 1000 And p.lines < 1000
// @Modifies p
// @Ensures |p.out'| = |p.out| + 4
func PrintTwice(p *Printer) {
	p.Print("a")
	p.Print("b")
}

// PrintLoopSlice prints in a loop beside a slice it was handed, which may
// be the array p's Builder owns: what the loop writes includes that array.
//
// @Requires p != nil And |s| > 0 And |p.out| <= 1000 And p.lines < 1000 And 0 <= k And k <= 10
// @Modifies p
// @Ensures s'[0] = s[0]
func PrintLoopSlice(p *Printer, s []byte, k int) {
	// @Invariant 0 <= i And i <= k And |p.out| <= |old(p.out)| + 2 * i And p.lines = old(p.lines) + i
	// @Variant k - i
	for i := 0; i < k; i++ {
		p.Print("a")
	}
} // want `postcondition may not hold: s'\[0\] = s\[0\]`

// NewPrinter returns a new Printer that has written a line, so its Builder
// owns an array, which is new too.
//
// @Ensures fresh(p) And |p.out| = 3 And p.lines = 1
func NewPrinter() (p *Printer) {
	p = &Printer{}
	p.Print("hi")
	return p
}

// UsesNewPrinter prints to a new Printer, whose Builder owns only new
// memory, with no Modifies clause.
//
// @Ensures True
func UsesNewPrinter() {
	p := NewPrinter()
	p.Print("x")
}

// TwoPrinters writes one Printer and keeps the length of the other.
//
// @Requires p != nil And q != nil And p != q And |p.out| <= 1000 And p.lines < 1000000
// @Modifies p
// @Ensures |q.out'| = |q.out|
func TwoPrinters(p, q *Printer) {
	p.Print("x")
}

// TwoPrintersSame is TwoPrinters where q may be p.
//
// @Requires p != nil And q != nil And |p.out| <= 1000 And p.lines < 1000000
// @Modifies p
// @Ensures |q.out'| = |q.out|
func TwoPrintersSame(p, q *Printer) {
	p.Print("x")
} // want `postcondition may not hold: \|q.out'\| = \|q.out\|`

// PrintsField lists only the Builder p holds.
//
// @Requires p != nil And |p.out| <= 1000
// @Modifies p.out
// @Ensures |p.out'| = |p.out| + 1
func PrintsField(p *Printer) {
	p.out.WriteByte('x')
}

// Elements writes the first of a slice of Builders, listed as an element.
//
// @Requires |bs| > 1 And |bs[0]| <= 1000
// @Modifies bs[0]
// @Ensures |bs'[0]| = |bs[0]| + 1
func Elements(bs []strings.Builder) {
	bs[0].WriteByte('x')
}

// ElementsWhole lists the slice, which covers its elements but not what
// they own.
//
// @Requires |bs| > 1 And |bs[0]| <= 1000
// @Modifies bs
// @Ensures True
func ElementsWhole(bs []strings.Builder) {
	bs[0].WriteByte('x') // want `WriteByte may modify what bs\[0\] owns, which ElementsWhole may not modify; list bs\[0\] in a // @Modifies clause, which covers what it owns; a slice listed whole covers its elements, not what they own`
}

// ElementsUnlisted writes the first of a slice of Builders without listing
// it.
//
// @Requires |bs| > 1 And |bs[0]| <= 1000
// @Ensures True
func ElementsUnlisted(bs []strings.Builder) {
	bs[0].WriteByte('x') // want `WriteByte may modify bs\[0\], which ElementsUnlisted may not modify; list it in a // @Modifies clause, as bs`
}

// Writer is an interface whose method writes behind its receiver.
type Writer interface {
	// @Receiver w
	// @Modifies w
	// @Ensures True
	Note()
}

// @Requires p != nil
// @Modifies p.lines
// @Ensures True
func (p *Printer) Note() {
	if p.lines < 1000000 {
		p.lines++
	}
}

// ConvertsPrinter converts a Printer, which owns what its Builder owns, to
// an interface whose method writes behind its receiver: refused, as a
// Buffer or a Builder is.
//
// @Requires p != nil
// @Modifies p
// @Ensures True
func ConvertsPrinter(p *Printer) {
	var w Writer = p // want `converting a value of type \*Printer to Writer is not supported yet: \*Printer owns memory`
	w.Note()
}

// BufferHolder holds a named type over a Buffer.
type BufferHolder struct{ b NB }

// HolderNB writes the NB a BufferHolder holds, under Modifies h.
//
// @Requires h != nil And |h.b| <= 1000
// @Modifies h
// @Ensures |h.b'| = |h.b| + 1
func HolderNB(h *BufferHolder) {
	(*bytes.Buffer)(&h.b).WriteByte('x')
}
