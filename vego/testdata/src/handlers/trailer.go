package handlers

import "net/http"

// The server writes Request.Trailer while a handler runs, so verified code
// cannot name it, and nothing about it survives a write.

// Drained reads a trailer before and after a write that may drain the body
// into it.
//
// @Requires w != nil And req != nil
// @Modifies w
// @Ensures n = 0
func Drained(w http.ResponseWriter, req *http.Request) (n int) {
	before := len(req.Trailer["X-Sum"]) // want `cannot verify Drained: Trailer of net/http.Request cannot be read or written by verified code: code that is not verified writes it behind calls whose entries do not list it, as the hidden declaration of net/http.Request in the shipped files says`
	w.Write(make([]byte, 4096))
	return len(req.Trailer["X-Sum"]) - before
}

// Assigned assigns the field.
//
// @Requires w != nil And req != nil
// @Modifies w, req
// @Ensures True
func Assigned(w http.ResponseWriter, req *http.Request) {
	req.Trailer = http.Header{} // want `cannot verify Assigned: Trailer of net/http.Request cannot be read or written`
	w.Write(nil)
}

// Wrapped embeds a request, through which Trailer is promoted.
type Wrapped struct {
	*http.Request
	n int
}

// Promoted reads it through the embedding.
//
// @Requires r != nil And r.Request != nil
// @Ensures True
func Promoted(r *Wrapped) (b bool) {
	return r.Trailer == nil // want `cannot verify Promoted: Trailer of net/http.Request cannot be read or written`
}

// Literal sets it in a composite literal.
//
// @Ensures True
func Literal() (r *http.Request) {
	return &http.Request{Trailer: http.Header{}} // want `cannot verify Literal: Trailer of net/http.Request cannot be read or written`
}

// InFormula names it in a contract.
//
// @Requires req != nil And req.Trailer != nil // want `req.Trailer: Trailer of net/http.Request cannot be read or written`
// @Ensures True
func InFormula(req *http.Request) {
}

// PathKept reads the path across the same write, which it keeps.
//
// @Requires w != nil And req != nil And req.URL != nil
// @Modifies w
// @Ensures n = 0
func PathKept(w http.ResponseWriter, req *http.Request) (n int) {
	before := len(req.URL.Path)
	w.Write(make([]byte, 4096))
	return len(req.URL.Path) - before
}

// trailerOf is trusted to return the trailer of a request, which verified
// code reaches without naming it.
func trailerOf(r *http.Request) (t http.Header) { return r.Trailer }

// Unnamed reads the trailer through a trusted function, before and after
// a write: nothing is known of it after the write.
//
// @Requires w != nil And req != nil
// @Modifies w
// @Ensures n = 0
func Unnamed(w http.ResponseWriter, req *http.Request) (n int) {
	t := trailerOf(req)
	before := len(t["X-Sum"])
	w.Write(make([]byte, 4096))
	return len(t["X-Sum"]) - before // want `postcondition may not hold: n = 0`
}
