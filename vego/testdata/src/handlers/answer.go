// Package handlers holds handlers of net/http written against the shipped
// entries of the writer, http.Error, and the header (F28).
package handlers

import (
	"net/http"
	"strconv"
)

// Store is data a handler keeps beside its writer.
type Store struct{ N int }

// Answer writes a whole response, and keeps what the request and s reach.
//
// @Requires w != nil And req != nil And req.URL != nil And s != nil
// @Modifies w
// @Ensures s.N' = s.N
func Answer(w http.ResponseWriter, req *http.Request, s *Store) {
	p := req.URL.Path
	w.Header().Set("Content-Type", "application/json")
	w.Header().Del("Content-Length")
	w.WriteHeader(http.StatusNotFound)
	w.Write([]byte("{}"))
	if req.URL.Path != p {
		panic("the writer changed the request")
	}
	_ = req.Method
}

// Unlisted writes the header without listing w.
//
// @Requires w != nil
// @Ensures True
func Unlisted(w http.ResponseWriter) {
	w.Header().Set("a", "b") // want `w.Header may modify the footprint of w, which Unlisted may not modify; list it in a // @Modifies clause` `Set may modify w.Header\(\), which Unlisted may not modify; it is memory that ResponseWriter.Header returned, which its contract places within w, and Unlisted passed w as w; list w in a // @Modifies clause`
}

// Fail answers with errors that http.Error and http.NotFound write.
//
// @Requires w != nil And req != nil And s != nil
// @Modifies w
// @Ensures s.N' = s.N
func Fail(w http.ResponseWriter, req *http.Request, s *Store) {
	if _, err := strconv.Atoi(req.PathValue("id")); err != nil {
		http.Error(w, "invalid id", http.StatusBadRequest)
		return
	}
	http.NotFound(w, req)
}

// Status writes a status code it is given, which may be no code at all.
//
// @Requires w != nil
// @Modifies w
// @Ensures True
func Status(w http.ResponseWriter, code int) {
	w.WriteHeader(code) // want `precondition of w.WriteHeader may not hold: 100 <= statusCode <= 999`
}

// StatusOf writes the text of a code with http.Error.
//
// @Requires w != nil And 100 <= code <= 599
// @Modifies w
// @Ensures True
func StatusOf(w http.ResponseWriter, code int) {
	http.Error(w, http.StatusText(code), code)
}

// Echo writes a message whose length nothing bounds.
//
// @Requires w != nil
// @Modifies w
// @Ensures True
func Echo(w http.ResponseWriter, msg string) {
	http.Error(w, msg, http.StatusBadRequest) // want `precondition of Error may not hold: 2 \* \(\|error\| \+ 1\) \+ 65536 <= MaxAlloc`
}

// EchoShort writes a message of a bounded length.
//
// @Requires w != nil And |msg| <= 1000
// @Modifies w
// @Ensures True
func EchoShort(w http.ResponseWriter, msg string) {
	http.Error(w, msg, http.StatusBadRequest)
}

// Bad is a handler whose literal, bound to a variable that is only
// called, writes the error, as the trial's dueHandler does.
//
// @Requires w != nil And req != nil And req.URL != nil And |req.URL.Path| <= 1000
// @Modifies w
// @Ensures True
func Bad(w http.ResponseWriter, req *http.Request) {
	bad := func() {
		http.Error(w, "bad path "+req.URL.Path, http.StatusBadRequest)
	}
	if req.Method != "GET" {
		bad()
		return
	}
	w.WriteHeader(http.StatusNoContent)
}
