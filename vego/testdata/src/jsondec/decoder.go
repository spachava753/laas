package jsondec

import (
	"encoding/json"
	"io"
	"net/http"
	"os"
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
	return &http.Request{Body: r} // want `cannot verify MakeRequest: the field Body of the net/http\.Request made at decoder\.go:143:10 is set, and the progresses declaration of net/http\.Request in the shipped files says that what it holds is a`
}

// The decoder calls Read as many times as it needs (F28 of the review of
// step 3): a contract of Read that reads its receiver is refused.

// Counting counts its reads.
type Counting struct{ Calls int }

// Read reads a space and counts the call.
//
// @Requires c != nil And |p| > 0 And c.Calls < 1000000
// @Modifies c, p
// @Ensures c.Calls' = c.Calls + 1 And n = 1 And err = nil
func (c *Counting) Read(p []byte) (n int, err error) {
	p[0] = ' '
	c.Calls = c.Calls + 1
	return 1, nil
}

// OnceDecoded would rely on one call of Read.
//
// @Requires c != nil And c.Calls = 0
// @Modifies c
// @Ensures c.Calls' <= 1
func OnceDecoded(c *Counting) {
	var rt Req
	_ = json.NewDecoder(io.LimitReader(c, 1000)).Decode(&rt) // want `cannot verify OnceDecoded: the decoder calls c\.Read as many times as it needs, and "c\.Calls < 1000000" in the contract of Read reads memory that Read modifies, which each call may change; give Read a `
}

// Spaces reads spaces, whatever it was called before.
type Spaces struct{ N int }

// Read reads a space.
//
// @Requires s != nil And |p| > 0
// @Modifies p
// @Ensures n = 1 And err = nil
func (s *Spaces) Read(p []byte) (n int, err error) {
	p[0] = ' '
	return 1, nil
}

// FromSpaces decodes from a reader whose contract is the same at every
// call.
//
// @Requires s != nil
// @Ensures True
func FromSpaces(s *Spaces) {
	var rt Req
	_ = json.NewDecoder(io.LimitReader(s, 1000)).Decode(&rt)
}

// Cycle reads what it holds over and over, keeping its place (F30 of the
// review of the decoder): its Read modifies it and requires only that it is
// not nil, and its contract reads nothing of what Read modifies, so it means
// the same at every call.
//
// @Invariant 0 <= pos And pos < |data|
type Cycle struct {
	data []byte
	pos  int
}

// Read reads the next byte.
//
// @Requires r != nil And |p| > 0
// @Modifies r, p
// @Ensures n = 1 And err = nil
func (r *Cycle) Read(p []byte) (n int, err error) {
	p[0] = r.data[r.pos]
	r.pos = r.pos + 1
	if r.pos == len(r.data) {
		r.pos = 0
	}
	return 1, nil
}

// FromCycle decodes from it.
//
// @Requires r != nil
// @Modifies r
// @Ensures True
func FromCycle(r *Cycle) {
	var rt Req
	_ = json.NewDecoder(io.LimitReader(r, 1000)).Decode(&rt)
}

// Flip serves its Data a byte at a time, then spaces, and flips Odd at
// every read. Its Read relates Odd before and after a call, which holds of
// one call and not of the many the decoder makes (F32 of the review): after
// the eight reads of {"ID":1}, Odd is 0.
//
// @Invariant 0 <= Pos And Pos <= |Data| And 0 <= Odd And Odd <= 1
type Flip struct {
	Data []byte
	Pos  int
	Odd  int
}

// Read reads the next byte.
//
// @Requires f != nil And |p| > 0
// @Modifies f, p
// @Ensures f.Odd' != f.Odd And n = 1 And err = nil
func (f *Flip) Read(p []byte) (n int, err error) {
	f.Odd = 1 - f.Odd
	if f.Pos == len(f.Data) {
		p[0] = ' '
		return 1, nil
	}
	p[0] = f.Data[f.Pos]
	f.Pos = f.Pos + 1
	return 1, nil
}

// FromFlip decodes from it and claims what one read would leave.
//
// @Requires f != nil And f.Odd = 0
// @Modifies f
// @Ensures f.Odd' = 1
func FromFlip(f *Flip) (rt Req) {
	_ = json.NewDecoder(io.LimitReader(f, 1000)).Decode(&rt) // want `cannot verify FromFlip: the decoder calls f\.Read as many times as it needs, and "f\.Odd' != f\.Odd" in the contract of Read reads memory that Read modifies, which each call may change; give Read a contr`
	return rt
}

// Marker notes that it was read. Its Read says so of the state after one
// call, which holds after the last of many calls but not after none, as
// when the limit is 0 and the decoder never calls Read.
type Marker struct {
	Seen int
}

// Read reads a space.
//
// @Requires m != nil And |p| > 0
// @Modifies m, p
// @Ensures m.Seen' = 1 And n = 1 And err = nil
func (m *Marker) Read(p []byte) (n int, err error) {
	m.Seen = 1
	p[0] = ' '
	return 1, nil
}

// FromMarker decodes at most n bytes from it and claims it was read.
//
// @Requires m != nil And 0 <= n And n <= 1000
// @Modifies m
// @Ensures m.Seen' = 1
func FromMarker(m *Marker, n int64) (rt Req) {
	_ = json.NewDecoder(io.LimitReader(m, n)).Decode(&rt) // want `cannot verify FromMarker: the decoder calls m\.Read as many times as it needs, and "m\.Seen' = 1" in the contract of Read reads memory that Read modifies, which each call may change; give Read a contrac`
	return rt
}

// FromFile decodes from a file, whose Read returns bytes or an error.
//
// @Requires f != nil
// @Ensures True
func FromFile(f *os.File) (err error) {
	var rt Req
	return json.NewDecoder(io.LimitReader(f, 1<<20)).Decode(&rt)
}
