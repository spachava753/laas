package guide

import (
	"bytes"
	"fmt"
	"io"
)

// The programs of the section "Converting a value of your own type".

// LineCount counts the lines it is given.
type LineCount struct{ N int }

// @Requires t != nil And |line| <= 100
// @Modifies t
// @Ensures True
func (t *LineCount) Record(line string) {
	if t.N < 1000000 {
		t.N++
	}
}

// @Requires t != nil
// @Modifies t
// @Ensures True
func Track(t *LineCount) {
	var r Recorder = t
	r.Record("start")
}

// @Requires t != nil
// @Ensures True
func TrackUnlisted(t *LineCount) {
	var r Recorder = t
	r.Record("start") // want `vego: r.Record may modify the footprint of r, which TrackUnlisted may not modify; it is the memory that t points to, converted at conversions.go:\d+:\d+; list t in a // @Modifies clause`
}

// @Ensures n = 0
func TrackBack() (n int) {
	t := &LineCount{}
	var r Recorder = t
	r.Record("start")
	return t.N // want `vego: postcondition may not hold: n = 0`
}

// Forward passes each line on to the tally it points to.
type Forward struct{ To *LineCount }

// @Requires f != nil And |line| <= 100
// @Modifies f.To
// @Ensures True
func (f *Forward) Record(line string) {
	if f.To != nil {
		f.To.Record(line)
	}
}

// @Requires f != nil And f.To != nil
// @Modifies f, f.To
// @Ensures True
func TrackForward(f *Forward) {
	var r Recorder = f // want `vego: Record may modify what it calls f.To, which Recorder.Record may not modify; it is not part of the footprint of \*Forward, which is the struct f points to`
	r.Record("start")
}

// @Ensures True
func FormatToBuffer() {
	var b bytes.Buffer
	fmt.Fprintf(&b, "%d items", 3)
}

// @Ensures True
func BufferAsWriter() {
	var b bytes.Buffer
	var w io.Writer = &b // want `vego: cannot verify BufferAsWriter: converting a value of type \*bytes.Buffer to io.Writer is not supported: its Write may panic when the buffer is too large to grow, and the contract of \(io.Writer\).Write has no bound for it; declare the memory of the machines the program runs on under sizes in vego-trusted.yaml, under which a buffer converts, or pass the Buffer itself to fmt.Fprintf, Fprint, or Fprintln, which then calls its own Write, or write what you format with its own WriteString, as in b.WriteString\(fmt.Sprintf\(...\)\)`
	fmt.Fprintf(w, "%d items", 3)
}
