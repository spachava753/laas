package footprints

import (
	"bufio"
	"bytes"
	"io"
)

// ReadThenWrite reads a byte of p before it writes to bw, whose buffer p
// may be.
//
// @Requires bw != nil And ready(bw) And |p| > 0
// @Modifies bw
// @Ensures r = p[0]
func ReadThenWrite(bw *bufio.Writer, p []byte) (r byte) {
	r = p[0]
	_ = bw.WriteByte('x')
	return r
}

// WriteThenRead reads the byte after the write, which may have written the
// buffer bw owns, which p may be.
//
// @Requires bw != nil And ready(bw) And |p| > 0
// @Modifies bw
// @Ensures r = p[0]
func WriteThenRead(bw *bufio.Writer, p []byte) (r byte) {
	_ = bw.WriteByte('x')
	return p[0] // want `vego: postcondition may not hold: r = p\[0\]`
}

// KeptOwn writes to bw and reads a byte of its own, which lies apart from
// what bw owned on entry and from what it may own since.
//
// @Requires bw != nil And ready(bw)
// @Modifies bw
// @Ensures r = 7
func KeptOwn(bw *bufio.Writer) (r byte) {
	p := make([]byte, 1)
	p[0] = 7
	_ = bw.WriteByte('x')
	_ = bw.Flush()
	return p[0]
}

// resetWriter is trusted by the project to write bw, with nothing said of
// how what bw owns changes.
func resetWriter(bw *bufio.Writer) { *bw = bufio.Writer{} }

// ResetsByProject calls a function the project trusts to write a Writer,
// which may make it own memory of its caller.
//
// @Requires bw != nil
// @Modifies bw
// @Ensures True
func ResetsByProject(bw *bufio.Writer) {
	resetWriter(bw) // want `vego: cannot verify ResetsByProject: resetWriter may modify bw, a \*bufio.Writer, which owns memory, and only a contract that comes with vego or a verified function says how what such a value owns may change`
}

// CopiesBuffer copies a Buffer, which would share what the Buffer owns.
//
// @Requires b != nil
// @Ensures True
func CopiesBuffer(b *bytes.Buffer) {
	c := *b // want `vego: cannot verify CopiesBuffer: \*b copies a value of type bytes.Buffer, which owns memory; use a pointer to it; a value that owns memory must not be copied or overwritten, since a copy would share what the original owns, which only the methods of each may write`
	_ = c
}

// WriteAllKeeps writes through a Writer and keeps the lines it was handed
// beside it, which lie outside what the Writer's own writer writes.
//
// @Requires bw != nil And ready(bw) And |lines| > 0 And |lines[0]| = 1
// @Modifies bw
// @Ensures |lines'[0]| = 1
func WriteAllKeeps(bw *bufio.Writer, lines []string) {
	_ = bw.WriteByte('a')
	_ = bw.WriteByte('b')
}

// KeepsBeside writes through a Writer and keeps a pair handed in beside it.
//
// @Requires bw != nil And ready(bw) And p != nil
// @Modifies bw
// @Ensures p.A' = p.A
func KeepsBeside(bw *bufio.Writer, p *Pair) {
	_ = bw.WriteByte('a')
}

// CallsWriteAll hands on a Writer it lists, with lines of its own.
//
// @Requires bw != nil And ready(bw) And |lines| > 0 And |lines[0]| = 1
// @Modifies bw
// @Ensures True
func CallsWriteAll(bw *bufio.Writer, lines []string) {
	WriteAllKeeps(bw, lines)
}

// CallsWriteAllLocal hands on a Writer it made over w (test 5). What the
// Writer's writer writes is new or lies in the footprint of w, as the
// contract of NewWriter says, and the lines reach neither: the fourth case
// of the proof at a call.
//
// @Requires w != nil And |lines| > 0 And |lines[0]| = 1
// @Modifies w
// @Ensures True
func CallsWriteAllLocal(w io.Writer, lines []string) {
	bw := bufio.NewWriter(w)
	WriteAllKeeps(bw, lines)
}

// WriterBox holds a Writer beside a number.
type WriterBox struct {
	W *bufio.Writer
	N int
}

// KeepsHolder writes through bw and keeps what h holds.
//
// @Requires bw != nil And ready(bw) And h != nil
// @Modifies bw
// @Ensures h.N' = h.N
func KeepsHolder(bw *bufio.Writer, h *WriterBox) {
	_ = bw.WriteByte('x')
}

// StoresThenKeeps makes a Writer over w and stores it where h reaches it,
// so h reaches memory that the Writer's writer may write.
//
// @Requires w != nil And h != nil
// @Modifies w, h
// @Ensures True
func StoresThenKeeps(w io.Writer, h *WriterBox) {
	bw := bufio.NewWriter(w)
	h.W = bw
	KeepsHolder(bw, h) // want `the footprint of what is owned by what is passed to KeepsHolder as bw may hold memory that what is passed as h reaches, and KeepsHolder relies on it not doing so: .*`
}

// Server holds the writer it answers on.
type Server struct{ Out io.Writer }

// OverUnplaced makes a Writer over a writer that a struct holds, whose
// footprint nothing places.
//
// @Requires s != nil And s.Out != nil And h != nil
// @Modifies s.Out
// @Ensures True
func OverUnplaced(s *Server, h *WriterBox) {
	bw := bufio.NewWriter(s.Out)
	KeepsHolder(bw, h) // want `bw is not a parameter whose footprint OverUnplaced's own Modifies lists, or a value made from such parameters by a call whose contract says so with fresh\(result, w\), so nothing places it`
}
