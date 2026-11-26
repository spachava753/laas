// Package unseensdk stands for the SDK of another module, as the MCP SDK
// is to a server: its go.mod puts it in a module of its own, and nothing in
// it is annotated. Its methods are the methods nobody verified that
// verified code converts values to its interfaces without (F39, part A).
package unseensdk

import (
	"encoding/json"
	"io"
)

// Content is what a result holds. Its unexported method keeps every
// implementation in this package.
type Content interface {
	MarshalJSON() ([]byte, error)
	fromWire(s string)
}

// Text is textual content.
type Text struct {
	Text string
	N    int
	Data []byte
}

// MarshalJSON reads the text.
func (t *Text) MarshalJSON() ([]byte, error) { return json.Marshal(t.Text) }

func (t *Text) fromWire(s string) {
	t.Text = s
	t.N++
	if len(t.Data) > 0 {
		t.Data[0] = 'X'
	}
}

// Result is what a handler returns.
type Result struct {
	Content []Content
}

// Send encodes a result, which runs the MarshalJSON of each content.
func Send(r *Result) ([]byte, error) { return json.Marshal(r) }

// Touch runs fromWire on every content: SDK code running SDK methods.
func Touch(r *Result) {
	for _, c := range r.Content {
		c.fromWire("touched")
	}
}

// Bumper is an SDK interface whose method has no entry.
type Bumper interface {
	Bump()
}

// Bump writes the struct and the array it holds.
func (t *Text) Bump() {
	t.N++
	if len(t.Data) > 0 {
		t.Data[0]++
	}
}

// Run runs Bump.
func Run(b Bumper) { b.Bump() }

// WrapIO keeps b in a writer whose Write runs b.Bump.
func WrapIO(b Bumper) io.Writer { return bumpWriter{b} }

type bumpWriter struct{ b Bumper }

func (w bumpWriter) Write(p []byte) (int, error) { w.b.Bump(); return len(p), nil }

// KHook takes a count.
type KHook func(k int) (n int)

// KBox holds a hook and a count.
type KBox struct {
	F KHook
	K int
}

// Fire runs the hook on the count.
func (b *KBox) Fire() (n int) { return b.F(b.K + 1) }

// Plain holds only a count.
type Plain struct{ K int }

// Fire returns the count.
func (p *Plain) Fire() (n int) { return p.K }

// Firer is an SDK interface whose method has no entry.
type Firer interface{ Fire() (n int) }

// FireAll runs Fire.
func FireAll(f Firer) (n int) { return f.Fire() }

// Sink takes strings; a project may implement it too.
type Sink interface{ Put(s string) }

// Lines is a sink of the SDK.
type Lines struct{ All []string }

// Put appends s.
func (l *Lines) Put(s string) { l.All = append(l.All, s) }

// Fill puts one string.
func Fill(s Sink) { s.Put("x") }

// Box is a generic type of the SDK.
type Box[T any] struct{ V T }

// Fire returns 0.
func (b *Box[T]) Fire() (n int) { return 0 }

// Wrapper embeds nothing but holds a writer.
type Holder struct {
	W io.Writer
}

// Fire returns 1.
func (h *Holder) Fire() (n int) { return 1 }

// Shutter has a state in the trust file of the corpus.
type Shutter interface{ Shut() }

// Door is a shutter.
type Door struct{ open bool }

// Shut closes the door.
func (d *Door) Shut() { d.open = false }
