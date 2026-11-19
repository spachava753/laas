// Package ifacestate closes interface values whose states come from code
// that is not verified, and gives an interface of its own a state.
package ifacestate

import "io"

// Drain reads once and closes the reader.
//
// @Requires rc != nil And ~closed(rc) And |buf| > 0
// @Modifies rc, buf
// @Ensures closed(rc') And 0 <= n <= |buf|
func Drain(rc io.ReadCloser, buf []byte) (n int, err error) {
	defer rc.Close()
	return rc.Read(buf)
}

// ReadThenClose reads and closes in order; Read keeps the state.
//
// @Requires rc != nil And ~closed(rc) And |buf| > 0
// @Modifies rc, buf
// @Ensures closed(rc')
func ReadThenClose(rc io.ReadCloser, buf []byte) (err error) {
	if _, err := rc.Read(buf); err != nil {
		rc.Close()
		return err
	}
	return rc.Close()
}

// Both closes two values, which a caller has shown share no state.
//
// @Requires a != nil And b != nil And ~closed(a) And ~closed(b)
// @Modifies a, b
// @Ensures closed(a') And closed(b')
func Both(a io.Closer, b io.ReadCloser) {
	a.Close()
	b.Close()
}

// Same converts a value to the interface it embeds; the two share the state.
//
// @Requires rc != nil And ~closed(rc)
// @Modifies rc
// @Ensures closed(rc')
func Same(rc io.ReadCloser) {
	var c io.Closer = rc
	c.Close()
}

// Held keeps a value in an any; its state stays with it.
//
// @Requires rc != nil And ~closed(rc)
// @Modifies rc
// @Ensures closed(rc')
func Held(rc io.ReadCloser) (kept any) {
	kept = rc
	rc.Close()
	return kept
}

// CallsBoth hands two values that are its own separate parameters on.
//
// @Requires a != nil And b != nil And ~closed(a) And ~closed(b)
// @Modifies a, b
// @Ensures closed(a') And closed(b')
func CallsBoth(a io.Closer, b io.ReadCloser) {
	Both(a, b)
}

// CloseOne closes the first and only reads the state of the second.
//
// @Requires a != nil And b != nil And ~closed(a)
// @Modifies a
// @Ensures closed(a')
func CloseOne(a io.Closer, b io.ReadCloser) {
	a.Close()
}

// Response holds a body as net/http does.
type Response struct {
	Status int
	Body   io.ReadCloser
}

// Done closes the body of a response.
//
// @Requires resp != nil And resp.Body != nil And ~closed(resp.Body)
// @Modifies resp.Body
// @Ensures closed(resp.Body') And c = resp.Status
func Done(resp *Response) (c int) {
	defer resp.Body.Close()
	return resp.Status
}

// InLoop closes each value of a slice once, the loop forgetting each.
//
// @Requires Forall i in [0, |rs|) : rs[i] != nil
// @Ensures True
func InLoop(rs []io.Closer, c io.Closer) {
	for range rs {
	}
}

// KeepOther closes a in a loop that runs once at most, and b keeps its
// state.
//
// @Requires a != nil And b != nil And ~closed(a) And ~closed(b)
// @Modifies a, b
// @Ensures closed(b')
func KeepOther(a, b io.Closer, n int) {
	closed := false
	// @Invariant ~closed(b)
	// @Invariant ~closed -> ~closed(a)
	// @Variant n - i
	for i := 0; i < n && !closed; i++ {
		a.Close()
		closed = true
	}
	b.Close()
}
