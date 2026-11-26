// Package guidesizes holds the programs of the guide's section "Bounding
// what grows" under a declared memory of 256GB.
package guidesizes

import (
	"bytes"
	"encoding/json"
	"io"
	"strings"
)

// @Ensures |out| = |xs|
func Upper(xs []string) (out []string) {
	// @Invariant 0 <= i <= |xs| And |out| = i
	// @Variant |xs| - i
	for i := 0; i < len(xs); i++ {
		out = append(out, strings.ToUpper(xs[i]))
	}
	return out
}

// @Requires n >= 0
// @Ensures |r| = n
func Zeros(n int) (r []byte) {
	r = make([]byte, n) // want `vego: the slice made may reserve more than the declared memory allows a value to: at most 1280000065536 bytes, five times the 256GB declared, and a page; a size that a number gives is not bounded by what the machines hold, so bound it`
	return r
}

// @Ensures True
func Lines(xs []string) (r string) {
	r = strings.Join(xs, "\n") // want `vego: precondition of Join may not hold: Forall i in \[0, \|elems\|\) : \|elems\| \* \(\|elems\[i\]\| \+ \|sep\| \+ 1\) <= MaxInt` `vego: precondition of Join may not hold: Forall i in \[0, \|elems\|\) : \|elems\| \* \(\|elems\[i\]\| \+ \|sep\| \+ 1\) <= MaxAlloc; the declared memory does not cover this`
	return r
}

// Doubles verifies, and on any input that is not empty it runs out of
// memory: under the declaration, growth that the program makes itself is
// bounded by the machine, not checked.
// @Modifies s
// @Ensures True
func Doubles(s []byte) (r []byte) {
	r = s
	// @Invariant 0 <= i <= 64
	// @Variant 64 - i
	for i := 0; i < 64; i++ {
		r = append(r, r...)
	}
	return r
}

// @Ensures True
func Forever() (r []byte) {
	// @Variant MaxAlloc - |r|
	for { // want `vego: loop variant may be negative: MaxAlloc - \|r\|; it holds only because a map cannot have more keys, and a string or the array of a slice cannot be longer, than memory can hold, which does not show that a loop or a recursion ends: one that grows a value until memory runs out does not end`
		r = append(r, 1)
	}
}

// @Requires w != nil
// @Modifies w
// @Ensures True
func emit(w io.Writer, s string) (err error) {
	_, err = io.WriteString(w, s)
	return err
}

// @Ensures True
func Emitted(s string) (r string, err error) {
	var b bytes.Buffer
	err = emit(&b, s)
	r = b.String()
	return r, err
}

// @Ensures True
func LengthAfter() (r int) {
	var b bytes.Buffer
	_ = emit(&b, "x")
	// @Assert |b| = 1 // want `vego: assertion may not hold: \|b\| = 1`
	r = b.Len()
	return r
}

// Memo is the guide's MemoJSON's type.
type Memo struct {
	Text string
	Tags []string
}

// @Ensures True
func MemoJSON(n Memo) (js []byte, err error) {
	return json.Marshal(n)
}

// @Ensures True
func Params(values map[string][]string) (js []byte, err error) {
	return json.Marshal(values)
}
