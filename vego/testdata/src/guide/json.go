package guide

import (
	"bytes"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"net/http"
	"time"
)

// Row is a row of a report, whose lengths its invariant bounds.
//
// @Invariant |Name| <= 100 And |Tags| <= 10 And (Forall j in [0, |Tags|) : |Tags[j]| <= 100)
type Row struct {
	ID   int       `json:"id"`
	Name string    `json:"name"`
	Tags []string  `json:"tags,omitempty"`
	At   time.Time `json:"at"`
}

// RowJSON encodes one row.
//
// @Ensures True
func RowJSON(r Row) (js []byte, err error) {
	return json.Marshal(r)
}

// ReportJSON encodes rows whose invariants hold, at most a thousand.
//
// @Requires |rows| <= 1000 And (Forall i in [0, |rows|) : valid(rows[i]))
// @Ensures True
func ReportJSON(rows []Row) (js []byte, err error) {
	return json.MarshalIndent(rows, "", "  ")
}

// Memo has no invariant.
type Memo struct {
	Text string
	Tags []string
}

// MemoJSON encodes a note nothing bounds.
//
// @Ensures True
func MemoJSON(n Memo) (js []byte, err error) {
	return json.Marshal(n) // want `what Marshal builds from n may be more than can be allocated; bound what it encodes, as in // @Requires \|n\.Text\| <= 1000000 And \|n\.Tags\| <= 1000000 And \(Forall i in \[0, \|n\.Tags\|\) : \|n\.Tags\[i\]\| <= 1000`
}

// Entry is a line of a log.
//
// @Invariant |Text| <= 100
type Entry struct {
	ID   int    `json:"id"`
	Text string `json:"text"`
}

// EntryJSON encodes one entry, which is at most 700 bytes.
//
// @Ensures err = nil -> |js| <= 700
func EntryJSON(e Entry) (js []byte, err error) {
	return json.Marshal(e)
}

// WriteEntries writes the JSON of each entry into a buffer.
//
// @Requires b != nil And |b| = 0 And |rows| <= 1000 And (Forall i in [0, |rows|) : valid(rows[i]))
// @Modifies b
// @Ensures True
func WriteEntries(b *bytes.Buffer, rows []Entry) {
	// @Invariant 0 <= i <= |rows| And |b| <= 1000 * i
	// @Variant |rows| - i
	for i := 0; i < len(rows); i++ {
		js, err := json.Marshal(rows[i])
		if err != nil {
			return
		}
		b.Write(js)
	}
}

// Level has a method that encoding/json would call.
type Level int

// MarshalJSON encodes the status as a word.
func (s Level) MarshalJSON() ([]byte, error) { return []byte(`"ok"`), nil }

// LevelJSON encodes a Level.
//
// @Ensures True
func LevelJSON(s Level) (js []byte, err error) {
	return json.Marshal(s) // want `cannot verify LevelJSON: Marshal encodes s, and s is of type Level, which has the method MarshalJSON, and encoding/json would call it; no method of a value runs under the contract of encoding/json in `
}

// ServeRow writes a row as the response.
//
// @Requires w != nil
// @Modifies w
// @Ensures True
func ServeRow(w http.ResponseWriter, r Row) {
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(r)
}

// HeldEncoder keeps the encoder in a variable.
//
// @Requires w != nil
// @Modifies w
// @Ensures True
func HeldEncoder(w io.Writer, r Row) (err error) {
	enc := json.NewEncoder(w) // want `cannot verify HeldEncoder: json\.NewEncoder keeps w in the encoder it returns; write json\.NewEncoder\(w\)\.Encode\(v\) in one expression, since an encoder held in a variable is not supported yet`
	enc.SetIndent("", "  ")
	return enc.Encode(r)
}

// LoadRows decodes rows from data of a bounded length.
//
// @Requires |data| <= 1000000
// @Ensures True
func LoadRows(data []byte) (n int, err error) {
	var rows []Row
	if err := json.Unmarshal(data, &rows); err != nil {
		return 0, fmt.Errorf("loading rows: %w", err)
	}
	return len(rows), nil
}

// LoadAll decodes rows from data of any length.
//
// @Ensures True
func LoadAll(data []byte) (n int, err error) {
	var rows []Row
	if err := json.Unmarshal(data, &rows); err != nil { // want `precondition of Unmarshal may not hold: 72 \* \(\|data\| \+ 1\) \+ 65536 <= MaxAlloc; it holds when \|data\| <= 1000000000000`
		return 0, err
	}
	return len(rows), nil
}

// Profile is decoded from a file and checked.
//
// @Invariant |Name| <= 100
type Profile struct {
	Name  string   `json:"name"`
	Hosts []string `json:"hosts"`
}

// ParseProfile decodes settings, and checks them before it returns them:
// nothing is known of what was decoded but its type.
//
// @Requires |data| <= 100000
// @Ensures True
func ParseProfile(data []byte) (s Profile, err error) {
	var got Profile
	if err = json.Unmarshal(data, &got); err != nil {
		return Profile{}, err
	}
	if len(got.Name) > 100 {
		return Profile{}, errors.New("name too long")
	}
	return got, nil
}

// ParseProfileUnchecked returns what it decoded unchecked.
//
// @Requires |data| <= 100000
// @Ensures True
func ParseProfileUnchecked(data []byte) (s Profile, err error) {
	var got Profile
	if err = json.Unmarshal(data, &got); err != nil {
		return Profile{}, err
	}
	return got, nil // want `invariant of Profile may not hold for the result s: \|Name\| <= 100`
}

// RefillMemo decodes into a memo that may already hold tags.
//
// @Requires p != nil And |data| <= 100000
// @Modifies p
// @Ensures True
func RefillMemo(data []byte, p *Memo) (err error) {
	return json.Unmarshal(data, p) // want `Unmarshal may decode into memory that p\.Tags refers to, which the caller may hold: it appends into a slice's array, keeps a map's entries, and decodes through a pointer it finds; decode into a value w`
}

// CreateRow decodes the body of a request, at most 1 MB of it.
//
// @Requires w != nil And req != nil And req.Body != nil
// @Modifies w, req.Body
// @Ensures True
func CreateRow(w http.ResponseWriter, req *http.Request) {
	var r Row
	if err := json.NewDecoder(io.LimitReader(req.Body, 1<<20)).Decode(&r); err != nil {
		http.Error(w, "bad request", http.StatusBadRequest)
		return
	}
	w.WriteHeader(http.StatusCreated)
}

// CreateRowErr answers with the text of the error.
//
// @Requires w != nil And req != nil And req.Body != nil
// @Modifies w, req.Body
// @Ensures True
func CreateRowErr(w http.ResponseWriter, req *http.Request) {
	var r Row
	if err := json.NewDecoder(io.LimitReader(req.Body, 1<<20)).Decode(&r); err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest) // want `cannot verify CreateRowErr: calling Error on err would run the methods of an error whose origin is not known; only an error made by errors\.New or fmt\.Errorf, here or in a verified function, one tha`
	}
}

// CreateRowText reads at most 1 MB of the body into a buffer, decodes
// it, and answers with the text of the error.
//
// @Requires w != nil And req != nil And req.Body != nil
// @Modifies w, req.Body
// @Ensures True
func CreateRowText(w http.ResponseWriter, req *http.Request) {
	body := req.Body
	buf := make([]byte, 1<<20)
	n := 0
	// @Invariant 0 <= n And n <= 1048576 And |buf| = 1048576 And fresh(buf)
	// @Variant 1048576 - n
	for n < len(buf) {
		m, rerr := body.Read(buf[n:])
		n += m
		if rerr != nil || m == 0 {
			break
		}
	}
	var r Row
	if err := json.Unmarshal(buf[:n], &r); err != nil {
		http.Error(w, "bad row: "+err.Error(), http.StatusBadRequest)
		return
	}
	w.WriteHeader(http.StatusCreated)
}

// Cache remembers the hosts it has seen, in a field json does not decode.
type Cache struct {
	Name string
	seen []string
}

// LoadCache decodes into a Cache.
//
// @Requires c != nil And |data| <= 100000
// @Modifies c
// @Ensures True
func LoadCache(data []byte, c *Cache) (err error) {
	return json.Unmarshal(data, c) // want `cannot verify LoadCache: Unmarshal decodes into c, and its field seen is a slice that Unmarshal leaves as it was, which vego cannot yet state; decode into a type without the field, and copy from it wh`
}

// FromReader decodes from any reader.
//
// @Requires r != nil
// @Modifies r
// @Ensures True
func FromReader(r io.Reader) (err error) {
	var row Row
	return json.NewDecoder(io.LimitReader(r, 1<<20)).Decode(&row) // want `the decoder calls r\.Read until it returns bytes or an error, and the contract of Read allows it to return neither, so the decoder may never return; read the body into a buffer with a bounded loop and `
}

// CreateRowNoLimit reads the body without a limit.
//
// @Requires req != nil And req.Body != nil
// @Modifies req.Body
// @Ensures True
func CreateRowNoLimit(req *http.Request) (err error) {
	var r Row
	return json.NewDecoder(req.Body).Decode(&r) // want `cannot verify CreateRowNoLimit: json\.NewDecoder\(r\)\.Decode reads from r without a limit, until the first value is whole, however long it is; write json\.NewDecoder\(io\.LimitReader\(r, n\)\)\.Decode\(&x\), with`
}
