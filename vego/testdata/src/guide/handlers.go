package guide

import (
	"bufio"
	"errors"
	"fmt"
	"mime"
	"net/http"
	"strconv"
	"strings"
)

// The programs of the section on writing a response.

// Tasks counts what a handler serves.
type Tasks struct{ Served int }

// GetTask answers a request for a task by its id.
//
// @Requires w != nil And req != nil And req.URL != nil And t != nil
// @Modifies w
// @Ensures t.Served' = t.Served
func GetTask(w http.ResponseWriter, req *http.Request, t *Tasks) {
	id, err := strconv.Atoi(req.PathValue("id"))
	if err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}
	if id < 0 {
		http.NotFound(w, req)
		return
	}
	w.Header().Set("Content-Type", "text/plain")
	w.WriteHeader(http.StatusOK)
	fmt.Fprintf(w, "task %d\n", id)
}

// @Requires w != nil And req != nil And req.URL != nil And |req.URL.RawQuery| <= 1000000
// @Modifies w
// @Ensures True
func ByTag(w http.ResponseWriter, req *http.Request) {
	tag := req.URL.Query().Get("tag")
	if tag == "" {
		http.Error(w, http.StatusText(http.StatusBadRequest), http.StatusBadRequest)
		return
	}
	w.Write([]byte(tag))
}

// @Requires w != nil
// @Ensures True
func Unlisted(w http.ResponseWriter) {
	w.Header().Set("Content-Type", "text/plain") // want `w.Header may modify the footprint of w, which Unlisted may not modify; list it in a // @Modifies clause` `Set may modify w.Header\(\), which Unlisted may not modify; it is memory that ResponseWriter.Header returned, which its contract places within w; list w in a // @Modifies clause`
}

// Server remembers the writer of the last request.
type Server struct {
	last http.ResponseWriter
}

// @Requires s != nil And w != nil
// @Modifies s
// @Ensures True
func (s *Server) Remember(w http.ResponseWriter, req *http.Request) {
	s.last = w // want `w is or holds a net/http.ResponseWriter, which must not be used after the call that received it returns, and here it is stored into memory at handlers.go:\d+:\d+, where a later call could use it; pass it on only to calls that keep nothing of it`
}

// @Requires w != nil And req != nil
// @Modifies w
// @Ensures True
func Trailers(w http.ResponseWriter, req *http.Request) {
	if req.Trailer != nil { // want `cannot verify Trailers: Trailer of net/http.Request cannot be read or written by verified code`
		w.WriteHeader(http.StatusOK)
	}
}

// @Requires w != nil And err != nil
// @Modifies w
// @Ensures True
func Prefixed(w http.ResponseWriter, err error) {
	if err = lookupTask(-1); err != nil {
		http.Error(w, "lookup: "+err.Error(), http.StatusNotFound)
	}
}

// @Requires w != nil And err != nil
// @Modifies w
// @Ensures True
func TwoTexts(w http.ResponseWriter, err error) {
	if err = lookupTask(-1); err != nil {
		s := err.Error()
		http.Error(w, s+"; "+s, http.StatusNotFound) // want `precondition of Error may not hold: 2 \* \(\|error\| \+ 1\) \+ 65536 <= MaxAlloc; it holds when \|s \+ "; " \+ s\| <= 100000000000000`
	}
}

// lookupTask fails for an id that is negative.
//
// @Ensures id >= 0 -> err = nil
func lookupTask(id int) (err error) {
	if id < 0 {
		return fmt.Errorf("no task %d", id)
	}
	return nil
}

// @Requires w != nil
// @Modifies w
// @Ensures True
func Buffered(w http.ResponseWriter) {
	bw := bufio.NewWriter(w) // want `w is or holds a net/http.ResponseWriter, which must not be used after the call that received it returns, and here it is handed to bufio.NewWriter as w \(its entry keeps w in result\), where a later call could use it; pass it on only to calls that keep nothing of it`
	bw.Write([]byte("hello"))
	bw.Flush()
}

// StatusWriter remembers the status a handler writes.
type StatusWriter struct {
	w    http.ResponseWriter
	code int
}

// @Requires w != nil
// @Ensures r != nil
func Wrap(w http.ResponseWriter) (r *StatusWriter) {
	return &StatusWriter{w: w} // want `w is or holds a net/http.ResponseWriter, which must not be used after the call that received it returns, and here it is stored into what the literal at handlers.go:\d+:\d+ makes` `&StatusWriter\{…\} is or holds a net/http.ResponseWriter, which must not be used after the call that received it returns, and here it is returned by Wrap`
}

// @Ensures ok -> err = nil
func Invalid(ok bool, reason string) (err error) {
	if ok {
		return nil
	}
	return errors.New(reason) // want `precondition of errors.New may not hold: 2 \* \(\|text\| \+ 4096\) \+ 65536 <= MaxAlloc, so that the text of the error can be printed; it holds when \|reason\| <= 140737488318464`
}

// @Requires |reason| <= 1000
// @Ensures ok -> err = nil
func InvalidShort(ok bool, reason string) (err error) {
	if ok {
		return nil
	}
	return errors.New(reason)
}

// @Requires w != nil And 0 <= n <= 1000
// @Modifies w
// @Ensures True
func BuildThenWrite(w http.ResponseWriter, n int) {
	var b strings.Builder
	// @Invariant 0 <= i <= n And |b| <= 400 * i
	// @Variant n - i
	for i := 0; i < n; i++ {
		fmt.Fprintf(&b, "%d\n", i%10)
	}
	w.Write([]byte(b.String()))
}

// JSONOnly refuses a request whose Content-Type is not JSON, bounding the
// header first, as the entry of mime.ParseMediaType requires.
//
// @Requires w != nil And req != nil And req.Header != nil
// @Modifies w
// @Ensures True
func JSONOnly(w http.ResponseWriter, req *http.Request) {
	contentType := req.Header.Get("Content-Type")
	if len(contentType) > 1000 {
		http.Error(w, "Content-Type too long", http.StatusBadRequest)
		return
	}
	mediatype, _, err := mime.ParseMediaType(contentType)
	if err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}
	if mediatype != "application/json" {
		http.Error(w, "expect application/json Content-Type", http.StatusUnsupportedMediaType)
	}
}

// JSONUnbounded is JSONOnly without the test of the header's length.
//
// @Requires w != nil And req != nil And req.Header != nil
// @Modifies w
// @Ensures True
func JSONUnbounded(w http.ResponseWriter, req *http.Request) {
	contentType := req.Header.Get("Content-Type")
	mediatype, _, err := mime.ParseMediaType(contentType) // want `vego: precondition of ParseMediaType may not hold: 32 \* \(\|v\| \+ 1\) \+ 65536 <= MaxAlloc; it holds when \|contentType\| <= 1000000000000`
	if err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}
	if mediatype != "application/json" {
		http.Error(w, "expect application/json Content-Type", http.StatusUnsupportedMediaType)
	}
}
