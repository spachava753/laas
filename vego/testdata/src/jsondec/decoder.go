package jsondec

import (
	"encoding/json"
	"io"
	"net/http"
)

// json.NewDecoder(io.LimitReader(r, n)).Decode(&x), written as one
// expression (F29, D3): r's own Read, then the decoding of Unmarshal from at
// most n bytes. Its error may be the reader's own, so it is not vouched
// for. The decoder calls Read until it returns bytes or an error, so a Read
// whose contract allows neither is refused: in v1 it would loop for ever.
// The contract of io.Reader's Read allows it; the body of a request, which
// the server makes, returns bytes or an error, as the progresses
// declaration in the shipped files says.

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
	return json.NewDecoder(io.LimitReader(r, n)).Decode(&rt) // want `the decoder may read n bytes, more than can be decoded; it holds when n <= 17592186040319` `the decoder calls r\.Read until it returns bytes or an error, and the contract of Read allows it to return neither, so the decoder may never return; read the body into a buffer with a bounded loop and `
}

// Unlisted does not list the reader it reads.
//
// @Requires r != nil
// @Ensures True
func UnlistedReader(r io.Reader) (err error) {
	var rt Req
	return json.NewDecoder(io.LimitReader(r, 1000)).Decode(&rt) // want `r\.Read may modify the footprint of r, which UnlistedReader may not modify; list it in a // @Modifies clause` `the decoder calls r\.Read until it returns bytes or an error, and the contract of Read allows it to return neither, so the decoder may never return; read the body into a buffer with a bounded loop and `
}

// The reader's Read is chosen as a conversion to io.Reader chooses it
// (F24 of the review of step 2).

// VR has Read on its value.
type VR struct{ N int }

// Read reads a space each time, so the decoder makes progress.
//
// @Requires |p| > 0
// @Modifies p
// @Ensures n = 1 And err = nil
func (v VR) Read(p []byte) (n int, err error) {
	p[0] = ' '
	return 1, nil
}

// ValueRecvNilReader hands a pointer that may be nil.
//
// @Ensures True
func ValueRecvNilReader(p *VR) (err error) {
	var rt Req
	return json.NewDecoder(io.LimitReader(p, 100)).Decode(&rt) // want `VR\.Read has a value receiver, and the pointer p handed to io\.LimitReader may be nil`
}

// ValueRecvReader hands a pointer that is not nil.
//
// @Requires p != nil
// @Ensures True
func ValueRecvReader(p *VR) (err error) {
	var rt Req
	return json.NewDecoder(io.LimitReader(p, 100)).Decode(&rt)
}

// SwapBody replaces the body of a request, which is refused: what the
// decoder reads must be the server's.
//
// @Requires req != nil
// @Modifies req
// @Ensures True
func SwapBody(req *http.Request, r io.ReadCloser) {
	req.Body = r // want `cannot verify SwapBody: req\.Body is stored into, and the progresses declaration of net/http\.Request in the shipped files says that what it holds is a reader that the server made, whose Read makes prog`
}

// MakeRequest makes a request with a body of its own, refused the same way.
//
// @Requires r != nil
// @Ensures True
func MakeRequest(r io.ReadCloser) (req *http.Request) {
	return &http.Request{Body: r} // want `cannot verify MakeRequest: the field Body of the net/http\.Request made at decoder\.go:142:10 is set, and the progresses declaration of net/http\.Request in the shipped files says that what it holds is a`
}
