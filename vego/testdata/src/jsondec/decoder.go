package jsondec

import (
	"encoding/json"
	"io"
	"net/http"
)

// json.NewDecoder(io.LimitReader(r, n)).Decode(&x), written as one
// expression (F29, D3): r's own Read, then the decoding of Unmarshal from at
// most n bytes. Its error may be the reader's own, so it is not vouched
// for: a handler answers with a message of its own.

// Create decodes the body of a request, at most 1 MB of it.
//
// @Requires w != nil And req != nil And req.Body != nil
// @Modifies w, req.Body
// @Ensures True
func Create(w http.ResponseWriter, req *http.Request) {
	var rt Req
	if err := json.NewDecoder(io.LimitReader(req.Body, 1<<20)).Decode(&rt); err != nil {
		http.Error(w, "bad request", http.StatusBadRequest)
		return
	}
	w.WriteHeader(http.StatusCreated)
}

// ErrText answers with the text of the error, which may be the reader's.
//
// @Requires w != nil And req != nil And req.Body != nil
// @Modifies w, req.Body
// @Ensures True
func ErrText(w http.ResponseWriter, req *http.Request) {
	var rt Req
	if err := json.NewDecoder(io.LimitReader(req.Body, 1<<20)).Decode(&rt); err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest) // want `cannot verify ErrText: calling Error on err would run the methods of an error whose origin is not known; only an error made by errors\.New or fmt\.Errorf, here or in a verified function, or one that a c`
	}
}

// NoLimit reads the body without a limit.
//
// @Requires req != nil And req.Body != nil
// @Modifies req.Body
// @Ensures True
func NoLimit(req *http.Request) (err error) {
	var rt Req
	return json.NewDecoder(req.Body).Decode(&rt) // want `cannot verify NoLimit: json\.NewDecoder\(r\)\.Decode reads from r without a limit, until the first value is whole, however long it is; write json\.NewDecoder\(io\.LimitReader\(r, n\)\)\.Decode\(&x\), with n the mo`
}

// HeldDecoder keeps the decoder in a variable.
//
// @Requires req != nil And req.Body != nil
// @Modifies req.Body
// @Ensures True
func HeldDecoder(req *http.Request) (err error) {
	var rt Req
	dec := json.NewDecoder(io.LimitReader(req.Body, 1<<20)) // want `cannot verify HeldDecoder: json\.NewDecoder keeps r in the decoder it returns; write json\.NewDecoder\(io\.LimitReader\(r, n\)\)\.Decode\(&x\) in one expression, since a decoder held in a variable is not suppor`
	dec.DisallowUnknownFields()
	return dec.Decode(&rt)
}

// GivenDecoder is handed a decoder that may hold what it read before.
//
// @Requires dec != nil
// @Ensures True
func GivenDecoder(dec *json.Decoder) (err error) {
	var rt Req
	return dec.Decode(&rt) // want `cannot verify GivenDecoder: Decode is verified only on a new decoder over a limited reader, written as json\.NewDecoder\(io\.LimitReader\(r, n\)\)\.Decode\(&x\) in one expression: a Decoder made elsewhere may `
}

// AnyLimit reads as much as it is told to.
//
// @Requires r != nil
// @Modifies r
// @Ensures True
func AnyLimit(r io.Reader, n int64) (err error) {
	var rt Req
	return json.NewDecoder(io.LimitReader(r, n)).Decode(&rt) // want `the decoder may read n bytes, more than can be decoded; it holds when n <= 17592186040319`
}

// Unlisted does not list the reader it reads.
//
// @Requires r != nil
// @Ensures True
func UnlistedReader(r io.Reader) (err error) {
	var rt Req
	return json.NewDecoder(io.LimitReader(r, 1000)).Decode(&rt) // want `r\.Read may modify the footprint of r, which UnlistedReader may not modify; list it in a // @Modifies clause`
}
