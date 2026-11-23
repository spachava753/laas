package jsonenc

import (
	"bytes"
	"encoding/json"
)

// How each length's bound is asked (F20 of the review of the fixes to
// step 1), how tight what is known of the result is (F21), and maps with
// integer keys (F22).

// Many holds many strings.
type Many struct {
	Xs []string
}

// Edge has up to 10^12 strings of up to 10^6 bytes: up to 6 * 10^18 bytes
// printed, more than can be allocated. A bound used without its proof, as
// one lowered without asking, would let it through.
//
// @Requires |m.Xs| <= 1000000000000 And (Forall i in [0, |m.Xs|) : |m.Xs[i]| <= 1000000)
// @Ensures True
func Edge(m Many) {
	js, _ := json.Marshal(m) // want `what Marshal builds from m may be more than can be allocated; bound what it encodes, as in // @Requires \|m\.Xs\| <= 10000000`
	_ = js
}

// ManyShort has more strings than the uniform bound allows and short
// ones: the number is raised past it and the strings' bound is lowered,
// one length at a time, so that what is built fits.
//
// @Requires |m.Xs| <= 1000000000 And (Forall i in [0, |m.Xs|) : |m.Xs[i]| <= 10)
// @Ensures True
func ManyShort(m Many) {
	js, _ := json.Marshal(m)
	_ = js
}

// T is a small value.
type T struct {
	N int
	S string
}

// TooTight states a bound on what Marshal returns below what it can build:
// ten bytes of S can print as sixty, so the JSON can take 93 bytes, more
// than the 34 that everything but S takes.
//
// @Requires |t.S| <= 10
// @Ensures err = nil -> |js| <= 40
func TooTight(t T) (js []byte, err error) {
	return json.Marshal(t) // want `postcondition may not hold: err = nil -> \|js\| <= 40`
}

// Row is a row of a table.
type Row struct {
	ID   int
	Name string
}

// Lines writes each row's JSON into a buffer, under a bound on each row
// that the length of what Marshal returns gives.
//
// @Requires b != nil And |b| = 0 And |rows| <= 1000 And (Forall i in [0, |rows|) : |rows[i].Name| <= 100)
// @Modifies b
// @Ensures True
func Lines(b *bytes.Buffer, rows []Row) {
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

// Concat appends three results.
//
// @Requires |a.Name| <= 100 And |c.Name| <= 100
// @Ensures True
func Concat(a, c Row) (out []byte) {
	j1, _ := json.Marshal(a)
	j2, _ := json.Marshal(c)
	j3, _ := json.Marshal(a)
	out = append(j1, j2...)
	out = append(out, j3...)
	return out
}

// IntKeys encodes a map with integer keys whose values hold strings: no
// bound on a key's length is in the facts, and it proves.
//
// @Requires |m| <= 1000 And (Forall k in m : |m[k]| <= 1000 And (Forall j in [0, |m[k]|) : |m[k][j]| <= 1000))
// @Ensures True
func IntKeys(m map[int][]string) (n int) {
	js, _ := json.Marshal(m)
	return len(js)
}
