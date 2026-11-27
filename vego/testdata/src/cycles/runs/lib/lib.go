// Package lib is called by app, which hands it values whose methods call
// back (F43, step 1). What each function may run of what it is handed is
// its summary, computed from its body and published.
package lib

import (
	"bufio"
	"encoding/json"
	"fmt"
	"io"
	"strings"
	_ "unsafe"

	"cycles/runs/third"
)

// Hook returns a number.
//
// @Ensures True
type Hook func() (n int)

// Box holds a reader, a hook, and a count.
type Box struct {
	R io.Reader
	F Hook
	N int
}

// Count reads only the count: it runs nothing of what it is handed.
//
// @Requires b != nil
// @Ensures True
func Count(b *Box) (n int) { return b.N }

// Pull reads from the reader the box holds: it runs Read.
//
// @Requires b != nil And b.R != nil
// @Modifies b.R
// @Ensures True
func Pull(b *Box) {
	buf := make([]byte, 1)
	_, _ = b.R.Read(buf)
}

// Fire calls the hook the box holds: it runs a Hook.
//
// @Requires b != nil
// @Ensures True
func Fire(b *Box) (n int) {
	if b.F == nil {
		return 0
	}
	return b.F()
}

// Via hands its reader to third.Use, which runs Read.
//
// @Requires r != nil
// @Modifies r
// @Ensures True
func Via(r io.Reader) { third.Use(r) }

// Later reads in a deferred call.
//
// @Requires b != nil And b.R != nil
// @Modifies b.R
// @Ensures True
func Later(b *Box) {
	buf := make([]byte, 1)
	defer b.R.Read(buf)
}

// Source yields bytes.
type Source interface {
	// @Ensures True
	Next() (c byte)
}

// wrap reads one byte through the reader it wraps; it is not verified.
type wrap struct{ in io.Reader }

func (w wrap) Next() byte {
	buf := make([]byte, 1)
	_, _ = w.in.Read(buf)
	return buf[0]
}

// NewWrap wraps r; it is not verified.
func NewWrap(r io.Reader) Source { return wrap{in: r} }

// Namer names.
type Namer interface {
	// @Ensures True
	Name() (s string)
}

// Encoded is a Namer whose Name encodes what it holds, which runs the
// MarshalJSON of what that is; it is not verified.
type Encoded struct{ V any }

func (e Encoded) Name() string {
	b, _ := json.Marshal(e.V)
	return string(b)
}

// Runner runs.
type Runner interface {
	// @Ensures True
	Run()
}

// Valued is a Runner whose Run takes a method value of the reader it holds
// and calls it; it is not verified.
type Valued struct{ BR *bufio.Reader }

func (v Valued) Run() {
	f := v.BR.ReadByte
	_, _ = f()
}

//go:linkname hiddenF cycles/runs/hidden.F
func hiddenF()

// Timer times.
type Timer interface {
	// @Ensures True
	Time() (n int64)
}

// Timed is a Timer whose Time calls a function of a package that lib does
// not import, by its symbol, which may run any code; it is not verified.
type Timed struct{}

func (Timed) Time() int64 {
	hiddenF()
	return 0
}

// Labeler labels.
type Labeler interface {
	// @Ensures True
	Label() (s string)
}

// Printed is a Labeler whose Label formats what it holds, which runs the
// String of what that is; it is not verified.
type Printed struct{ V any }

func (p Printed) Label() string { return fmt.Sprint(p.V) }

// Ranger ranges.
type Ranger interface {
	// @Ensures True
	Range()
}

// Ranged is a Ranger whose Range ranges over the function it holds; it is
// not verified.
type Ranged struct{ Seq func(yield func(int) bool) }

func (r Ranged) Range() {
	for range r.Seq {
	}
}

// Valuer values.
type Valuer interface {
	// @Ensures True
	Val()
}

// MethodValued is a Valuer whose Val takes the method value Read of the
// reader it holds and calls it; it is not verified.
type MethodValued struct{ R io.Reader }

func (m MethodValued) Val() {
	f := m.R.Read
	_, _ = f(nil)
}

// Pred is a predicate.
//
// @Ensures True
type Pred func(r rune) (b bool)

// Index hands the predicate it is handed to strings.IndexFunc, which calls
// it.
//
// @Requires p != nil
// @Ensures True
func Index(s string, p Pred) (i int) { return strings.IndexFunc(s, p) }
