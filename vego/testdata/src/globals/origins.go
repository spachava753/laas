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
	return Keep(w, sinkBuf) // want `^vego: the footprint of what is passed to Keep as w may hold memory that what is passed as sinkBuf reaches, and Keep relies on it not doing so: it is read from the package-level variable sinkBuf, and code elsewhere may hold a reference to what it refers to; take it as a parameter instead$`
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

// Get returns the variable.
//
// @Ensures True
func Get() (r *Counter) { return sinkBuf }

// ThroughGetter hands Keep what Get returns, which verified before F31.
//
// @Requires w != nil
// @Modifies w
// @Ensures True
func ThroughGetter(w io.Writer) (r bool) {
	p := Get()
	if p == nil {
		return true
	}
	return Keep(w, p) // want `^vego: the footprint of what is passed to Keep as w may hold memory that what is passed as p reaches, and Keep relies on it not doing so: it comes from the call of Get at origins.go:58:7, whose contract does not say that it is new or lies within an argument$`
}

type Box struct{ c *Counter }

var box = &Box{c: &Counter{}}

// Field hands Keep a pointer read through a field of a variable, which
// verified before F31.
//
// @Requires w != nil And box.c != nil
// @Modifies w
// @Ensures True
func Field(w io.Writer) (r bool) {
	return Keep(w, box.c) // want `^vego: the footprint of what is passed to Keep as w may hold memory that what is passed as box.c reaches, and Keep relies on it not doing so: it is read from the package-level variable box, and code elsewhere may hold a reference to what it refers to; take it as a parameter instead$`
}

// Main4 and Main6 make Keep return false through ThroughGetter and Field,
// and are not verified.
func Main4() bool { return ThroughGetter(sinkBuf) }
func Main6() bool { return Field(box.c) }

// OuterParam takes the value as a parameter, the remedy the message gives.
//
// @Requires w != nil And p != nil
// @Modifies w
// @Ensures True
func OuterParam(w io.Writer, p *Counter) (r bool) {
	return Keep(w, p)
}

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
