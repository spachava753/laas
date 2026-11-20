// Package p hands a reader to another package. With an entry that claims
// what that code finds on the reader, the call reaches only methods named
// Read; without one, every exported function and method of p.
package p

import (
	"io"

	"cycles/claim/q"
)

// Source reads zeros.
type Source struct{}

// Close is exported, and calls Narrow and Wide back.
func (Source) Close() error {
	Narrow(Source{})
	Wide(Source{})
	return nil
}

func (Source) Read(b []byte) (int, error) { return len(b), nil }

// Narrow verifies: q.Use runs only Read, which calls nothing back.
//
// @Requires r != nil
// @Ensures True
func Narrow(r io.Reader) (n int) {
	return q.Use(r)
}

// Wide is refused: q.UseWide may find Close on r, which calls Wide back.
//
// @Requires r != nil
// @Ensures True
func Wide(r io.Reader) (n int) {
	return q.UseWide(r) // want `this call may not end: Wide hands r to q.UseWide\(r\) at p.go:\d+:\d+, which may run`
}
