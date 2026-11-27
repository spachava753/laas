// Package promoted: a method promoted from an embedded field is handed
// that field, not the value it is selected on (F43). Guarded embeds a
// mutex beside a reader; Lock gets the mutex, which holds no code, so
// Pull is no cycle through it. Buffered embeds a *bufio.Reader whose
// reader calls back, and ReadByte, which reads from it, is one.
package promoted

import (
	"bufio"
	"io"
	"sync"
)

// Guarded holds a reader beside the mutex it embeds.
type Guarded struct {
	sync.Mutex
	src io.Reader
}

// Back reads and calls Pull; it is not verified.
type Back struct{ g *Guarded }

func (b Back) Read(p []byte) (n int, err error) {
	Pull(b.g)
	return 0, io.EOF
}

// @Requires g != nil And ~held(g.Mutex)
// @Modifies g.Mutex
// @Ensures True
func Pull(g *Guarded) {
	g.Lock()
	g.Unlock()
}

// Buffered reads through the *bufio.Reader it embeds.
type Buffered struct {
	*bufio.Reader
}

// Again reads, and its Read, which is not verified, calls First.
type Again struct{ b *Buffered }

func (a Again) Read(p []byte) (n int, err error) {
	First(a.b)
	return 0, io.EOF
}

// @Requires b != nil And b.Reader != nil And ready(b.Reader)
// @Modifies b.Reader
// @Ensures True
func First(b *Buffered) {
	_, _ = b.ReadByte() // want `this call may not end: First hands b to b.ReadByte\(\) at promoted.go:\d+:\d+, which may run Again.Read, Again.Read calls First at promoted.go:\d+:\d+; a cycle`
}
