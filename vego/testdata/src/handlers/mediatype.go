package handlers

import (
	"mime"
	"net/http"
)

// The shipped entry of mime.ParseMediaType (F30, step 5).

// JSONOnly refuses a request whose Content-Type is not JSON: the header is
// bounded first, as the entry requires, and the error of ParseMediaType,
// which the entry vouches for, is written to the client.
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

// UnboundedMediaType parses a header of any length, which the entry's bound on what
// ParseMediaType allocates does not allow.
//
// @Requires w != nil And req != nil And req.Header != nil
// @Modifies w
// @Ensures True
func UnboundedMediaType(w http.ResponseWriter, req *http.Request) {
	_, _, err := mime.ParseMediaType(req.Header.Get("Content-Type")) // want `vego: precondition of ParseMediaType may not hold: 256 \* \(\|v\| \+ 1\) \+ 65536 <= MaxAlloc`
	if err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
	}
}
