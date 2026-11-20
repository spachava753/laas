// Package keepslib stands for code that is not verified and keeps what it
// is given: a registry that keeps handlers in itself, and a constructor that
// keeps a reader in what it returns. Its functions have entries in the
// trust file of the tests.
package keepslib

import (
	"errors"
	"io"
)

// Handler is called with a number that is not negative.
//
// @Requires n >= 0
// @Ensures True
type Handler func(n int)

// Registry keeps handlers and calls them when it fires.
type Registry struct {
	handlers []Handler
}

// NewRegistry returns an empty registry.
func NewRegistry() *Registry { return &Registry{} }

// Add keeps h in r, which Fire calls.
func (r *Registry) Add(h Handler) { r.handlers = append(r.handlers, h) }

// Fire calls every handler kept in r with n.
func (r *Registry) Fire(n int) {
	for _, h := range r.handlers {
		h(n)
	}
}

// AddRaw keeps a function of a type that has no contract.
func (r *Registry) AddRaw(f func(int)) {}

// Box keeps a reader.
type Box struct {
	r io.Reader
}

// Wrap returns a box that reads from r.
func Wrap(r io.Reader) *Box { return &Box{r: r} }

// Fill reads from the reader in b into p.
func (b *Box) Fill(p []byte) int {
	n, _ := b.r.Read(p)
	return n
}

var kept []Handler

// Keep keeps h in a package-level variable, and Flush calls it later: no
// entry for Keep can say where it keeps h.
func Keep(h Handler) { kept = append(kept, h) }

// Flush calls what Keep kept.
func Flush() {
	for _, h := range kept {
		h(1)
	}
}

// KeepsCount keeps nothing that can hold code.
func KeepsCount(n int) *Box { return nil }

// KeepsInCount keeps r in a number.
func KeepsInCount(r io.Reader) int { return 0 }

// KeepsInSelf keeps r in r.
func KeepsInSelf(r io.Reader) {}

// KeepsInUnlisted keeps h in reg, which its entry does not list under
// modifies.
func KeepsInUnlisted(reg *Registry, h Handler) {}

// KeepsInError keeps a handler in an error, which stratification does not
// count.
func KeepsInError(h Handler) error { return errors.New("x") }

// KeepsInNothing names a destination that does not exist.
func KeepsInNothing(h Handler) {}

// KeepsUnknown names a parameter that does not exist.
func KeepsUnknown(h Handler) {}

// KeepsCalled keeps a function it is said to call only while the call
// lasts.
func KeepsCalled(f func(int) bool) *Registry { return nil }

// KeepsFormatted keeps what it formats.
func KeepsFormatted(v ...any) *Registry { return nil }

// KeepsTwice names one destination twice.
func KeepsTwice(h Handler) *Registry { return nil }

// Closing keeps r in a closer whose Close does nothing, as io.NopCloser
// does.
func Closing(r io.Reader) io.ReadCloser { return io.NopCloser(r) }

// Consume reads from rc until it fails.
func Consume(rc io.ReadCloser) {}
