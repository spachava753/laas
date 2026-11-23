package handlers

import "net/http"

// Page is what a handler renders.
type Page struct {
	Title string
	Rows  []string
}

// render writes a page through w, which it lists beside the page.
//
// @Requires w != nil And p != nil
// @Modifies w
// @Ensures True
func render(w http.ResponseWriter, p *Page) {
	w.Write([]byte(p.Title))
}

// render2 writes through w beside the request.
//
// @Requires w != nil And req != nil
// @Modifies w
// @Ensures True
func render2(w http.ResponseWriter, req *http.Request) {
	w.WriteHeader(http.StatusOK)
}

// SetThenRender sets a header and then hands w to a helper beside data,
// which a header's Set and Del allow since they store only what they make.
//
// @Requires w != nil And p != nil
// @Modifies w
// @Ensures True
func SetThenRender(w http.ResponseWriter, p *Page) {
	w.Header().Set("Content-Type", "text/html")
	w.Header().Del("Content-Length")
	render(w, p)
}

// RequestThenRender sets a header of the request and hands it on beside w.
//
// @Requires w != nil And req != nil And req.Header != nil
// @Modifies w, req.Header
// @Ensures True
func RequestThenRender(w http.ResponseWriter, req *http.Request) {
	req.Header.Set("X-Seen", "1")
	render2(w, req)
}

// fillPage is trusted to set a header of h, which it lists under stores,
// and to write p, which it does not list there.
func fillPage(h http.Header, p *Page) {}

// FillThenRender calls an entry whose other target can hold a reference,
// which stores does not cover, so the call may store memory of any origin.
//
// @Requires w != nil And p != nil And req != nil And req.Header != nil
// @Modifies w, req.Header, p
// @Ensures True
func FillThenRender(w http.ResponseWriter, req *http.Request, p *Page) {
	fillPage(req.Header, p)
	render2(w, req) // want `the footprint of what is passed to render2 as w may hold memory that what is passed as req reaches, and render2 relies on it not doing so: the call of fillPage at render.go:\d+:\d+ may store into memory it may modify a reference to memory of any origin`
}

// Sink writes behind its receiver.
type Sink interface {
	// @Receiver s
	// @Modifies s
	// @Ensures True
	Put()
}

// grownBeside is trusted to set a header of h, write s, and return a map it
// placed in the footprint of s.
func grownBeside(h http.Header, s Sink) (m map[int]int) { return map[int]int{} }

// GrownBeside writes into the map, which lies in s's footprint since the
// call grew it: the growth layer of the target that stores does not list.
//
// @Requires h != nil And s != nil
// @Modifies h, s
// @Ensures True
func GrownBeside(h http.Header, s Sink) {
	m := grownBeside(h, s)
	m[1] = 2
}
