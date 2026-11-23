package handlers

import (
	"io"
	"net/http"
)

// What a response's body writes leaves the rest of the response alone
// (the notWrittenBy declaration of Response.Body), so a function that
// lists resp.Body keeps what resp reaches across a read or a close.

// Drain reads from the body once and closes it, and keeps the status.
//
// @Requires resp != nil And resp.Body != nil And ~closed(resp.Body) And |buf| > 0
// @Modifies resp.Body, buf
// @Ensures closed(resp.Body') And code = resp.StatusCode
func Drain(resp *http.Response, buf []byte) (code int) {
	defer resp.Body.Close()
	resp.Body.Read(buf)
	return resp.StatusCode
}

// DrainOwn hands its own response on.
//
// @Requires resp != nil And resp.Body != nil And ~closed(resp.Body) And |buf| > 0
// @Modifies resp.Body, buf
// @Ensures True
func DrainOwn(resp *http.Response, buf []byte) {
	Drain(resp, buf)
}

// DrainListed lists the response, not its body.
//
// @Requires resp != nil And resp.Body != nil And ~closed(resp.Body) And |buf| > 0
// @Modifies resp, buf
// @Ensures True
func DrainListed(resp *http.Response, buf []byte) {
	Drain(resp, buf) // want `the footprint of what is passed to Drain as resp.Body may hold memory that the arguments reach, and Drain relies on it not doing so: resp.Body is not a field of a parameter whose Body DrainListed's own Modifies lists as resp.Body` `Drain may modify the footprint of what it calls resp.Body, which DrainListed may not modify`
}

// get is trusted to make a request.
func get(url string) (resp *http.Response) { return nil }

// DrainFetched hands on a response that a trusted call returned.
//
// @Requires |buf| > 0
// @Modifies buf
// @Ensures True
func DrainFetched(buf []byte) {
	resp := get("x")
	if resp == nil || resp.Body == nil {
		return
	}
	Drain(resp, buf) // want `resp.Body is not a field of a parameter whose Body DrainFetched's own Modifies lists as resp.Body` `precondition of Drain may not hold: ~closed\(resp.Body\)` `Drain may modify the footprint of what it calls resp.Body, which DrainFetched may not modify`
}

// Holder holds a response.
type Holder struct{ R *http.Response }

// DrainHeld hands on a response read from memory.
//
// @Requires h != nil And h.R != nil And h.R.Body != nil And ~closed(h.R.Body) And |buf| > 0
// @Modifies h.R.Body, buf
// @Ensures True
func DrainHeld(h *Holder, buf []byte) {
	Drain(h.R, buf) // want `h.R.Body is not a field of a parameter whose Body DrainHeld's own Modifies lists as h.R.Body`
}

// DrainCopy hands on a copy of its response, whose body is its own.
//
// @Requires resp != nil And resp.Body != nil And ~closed(resp.Body) And |buf| > 0
// @Modifies resp.Body, buf
// @Ensures True
func DrainCopy(resp *http.Response, buf []byte) {
	r2 := *resp
	Drain(&r2, buf) // want `\(&r2\).Body is not a field of a parameter whose Body DrainCopy's own Modifies lists as \(&r2\).Body`
}

// StoreBody puts a closer it was handed into the response.
//
// @Requires resp != nil
// @Modifies resp
// @Ensures True
func StoreBody(resp *http.Response, c io.ReadCloser) {
	resp.Body = c // want `cannot verify StoreBody: resp.Body is stored into, and what the field Body of a net/http.Response holds writes nothing else the Response reaches`
}

// none is a body of the project.
type none struct{}

// @Ensures n = 0 And (|p| = 0 -> err = nil)
func (none) Read(p []byte) (n int, err error) {
	if len(p) == 0 {
		return 0, nil
	}
	return 0, io.EOF
}

// @Ensures err = nil
func (none) Close() (err error) { return nil }

// ReplaceNew puts a body it makes into the response.
//
// @Requires resp != nil
// @Modifies resp
// @Ensures True
func ReplaceNew(resp *http.Response) {
	resp.Body = &none{}
}

// MakeWith builds a response with a body it was handed.
//
// @Ensures r != nil
func MakeWith(c io.ReadCloser) (r *http.Response) {
	return &http.Response{StatusCode: 200, Body: c} // want `cannot verify MakeWith: the field Body of the net/http.Response made at response.go:\d+:\d+ is set`
}

// MakeEmpty builds one as a test helper would.
//
// @Ensures r != nil
func MakeEmpty() (r *http.Response) {
	return &http.Response{StatusCode: 200, Body: &none{}}
}

// Overwrite stores a whole response into another.
//
// @Requires resp != nil And other != nil
// @Modifies resp
// @Ensures True
func Overwrite(resp, other *http.Response) {
	*resp = *other // want `cannot verify Overwrite: a net/http.Response is stored into memory at \*resp`
}

// LocalCopy copies a response into a local.
//
// @Requires resp != nil
// @Ensures code = resp.StatusCode
func LocalCopy(resp *http.Response) (code int) {
	r2 := *resp
	return r2.StatusCode
}
