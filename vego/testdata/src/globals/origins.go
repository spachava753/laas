package globals

import "io"

// What a package-level variable refers to is outside every footprint only
// while the variable holds the only reference to it. Before F31 a read of
// any package-level variable counted as outside, and Outer verified: code
// that is not verified can hand what sinkBuf points to in as the writer,
// and then Keep's write through w changes p.n. Main2 and Main3 make Keep return
// false at run time (F1 of the design review of F31).

type Counter struct{ n int }

func (b *Counter) Write(p []byte) (int, error) { b.n++; return len(p), nil }

var sinkBuf = &Counter{}

// Outer hands Keep a package-level variable beside its writer.
//
// @Requires w != nil
// @Modifies w
// @Ensures True
func Outer(w io.Writer) (r bool) {
	return Keep(w, sinkBuf) // want `^vego: the footprint of what is passed to Keep as w may hold memory that what is passed as sinkBuf reaches, and Keep relies on it not doing so: it is read from the package-level variable sinkBuf, whose memory code elsewhere may refer to$`
}

// Keep keeps p across a write through w.
//
// @Requires p != nil And w != nil
// @Modifies w
// @Ensures r
func Keep(w io.Writer, p *Counter) (r bool) {
	a := p.n
	w.Write([]byte("x"))
	return p.n == a
}

// Main2 hands Outer the variable's memory as the writer, and is not
// verified.
func Main2() bool { return Outer(sinkBuf) }

func asWriter(b *Counter) io.Writer { return b }

// Main3 converts it in a helper, and is not verified.
func Main3() bool { return Outer(asWriter(sinkBuf)) }

var weights = []int{3, 5}

// Weight reads contents that are only read across a write through w.
//
// @Requires w != nil
// @Modifies w
// @Ensures r = 5
func Weight(w io.Writer) (r int) {
	w.Write([]byte("x"))
	return weights[1]
}
