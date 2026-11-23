package guide

import (
	"fmt"
	"net/http"
	"strconv"
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
