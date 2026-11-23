package handlers

import "net/http"

// Tagged reads what an ordinary handler reads of its request, and answers.
//
// @Requires w != nil And req != nil And req.URL != nil And |req.URL.RawQuery| <= 1000000
// @Modifies w
// @Ensures True
func Tagged(w http.ResponseWriter, req *http.Request) {
	if req.Method != http.MethodGet {
		http.Error(w, http.StatusText(http.StatusMethodNotAllowed), http.StatusMethodNotAllowed)
		return
	}
	tag := req.URL.Query().Get("tag")
	if tag == "" {
		http.NotFound(w, req)
		return
	}
	w.Header().Set("Content-Type", req.Header.Get("Accept"))
	w.Write([]byte(tag))
}

// Unbounded reads the query of a request whose length nothing bounds.
//
// @Requires w != nil And req != nil And req.URL != nil
// @Modifies w
// @Ensures True
func Unbounded(w http.ResponseWriter, req *http.Request) {
	_ = req.URL.Query() // want `precondition of Query may not hold: 32 \* \(\|u.RawQuery\| \+ 1\) \+ 65536 <= MaxAlloc; it holds when`
}
