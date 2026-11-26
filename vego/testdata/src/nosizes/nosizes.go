// Package nosizes holds the programs of sizes with no declared memory:
// each place that grows what exists is reported as at the base, since
// nothing bounds the lengths (F38).
package nosizes

import (
	"bytes"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"path/filepath"
	"slices"
	"strconv"
	"strings"
)

// @Modifies s
// @Ensures |r| = |s| + 1
func Push(s []int, x int) (r []int) {
	r = append(s, x) // want `vego: the slice that append grows may be more than can be allocated`
	return r
}

// @Ensures |out| = |xs|
func Collect(xs []string) (out []string) {
	// @Invariant 0 <= i <= |xs| And |out| = i
	// @Variant |xs| - i
	for i := 0; i < len(xs); i++ {
		out = append(out, xs[i]) // want `vego: the slice that append grows may be more than can be allocated`
	}
	return out
}

// @Ensures |r| = |a| + |b|
func Cat(a, b string) (r string) {
	r = a + b // want `vego: the joined string may be more than can be allocated`
	return r
}

// @Ensures |r| = |a| + 1 + |b|
func Pair(a, b string) (r string) {
	r = a + "=" + b // want `vego: the joined string may be more than can be allocated` `vego: the joined string may be more than can be allocated`
	return r
}

var errMissing = errors.New("missing")

// @Ensures found -> err = nil
func Wrap(name string, found bool) (err error) {
	if !found {
		return fmt.Errorf("reading %s: %w", name, errMissing) // want `vego: what fmt.Errorf builds from what it formats may be more than can be allocated`
	}
	return nil
}

// @Ensures ok -> err = nil
func NewError(text string, ok bool) (err error) {
	if !ok {
		return errors.New(text) // want `vego: precondition of errors.New may not hold: 2 \* \(\|text\| \+ 4096\) \+ 65536 <= MaxAlloc`
	}
	return nil
}

// @Ensures True
func Lower(s string) (r string) {
	r = strings.ToLower(s) // want `vego: precondition of ToLower may not hold: 6 \* \|s\| \+ 65544 <= MaxAlloc`
	return r
}

// @Ensures True
func Words(s string) (r []string) {
	r = strings.Split(s, ",") // want `vego: precondition of Split may not hold: 16 \* \(\|s\| \+ 1\) <= MaxAlloc`
	return r
}

// @Ensures True
func Label(n int) (r string) {
	r = strconv.Itoa(n) + "x" // want `vego: the joined string may be more than can be allocated`
	return r
}

// @Ensures True
func Setting(name string, n int) (r string) {
	r = fmt.Sprintf("%s=%d", name, n) // want `vego: what Sprintf builds from what it formats may be more than can be allocated`
	return r
}

// @Ensures True
func Path(dir, name string) (r string) {
	r = filepath.Join(dir, name) // want `vego: precondition of Join may not hold: Forall i in \[0, \|elem\|\) : 2 \* \|elem\| \* \(\|elem\[i\]\| \+ 2\) \+ 65536 <= MaxAlloc`
	return r
}

// @Ensures |r| = |xs|
func Copies(xs []string) (r []string) {
	r = make([]string, len(xs))
	return r
}

// @Ensures True
func Lines(xs []string) (r string) {
	var b strings.Builder
	// @Invariant 0 <= i <= |xs|
	// @Variant |xs| - i
	for i := 0; i < len(xs); i++ {
		b.WriteString(xs[i]) // want `vego: precondition of WriteString may not hold: 2 \* \(\|b\| \+ \|s\|\) \+ 65536 <= MaxAlloc`
		b.WriteByte('\n') // want `vego: precondition of WriteByte may not hold: 2 \* \(\|b\| \+ 1\) \+ 65536 <= MaxAlloc`
	}
	r = b.String()
	return r
}

// @Ensures True
func Table(names []string, n int) (r []byte) {
	var b bytes.Buffer
	// @Invariant 0 <= i <= |names|
	// @Variant |names| - i
	for i := 0; i < len(names); i++ {
		fmt.Fprintf(&b, "%s\t%d\n", names[i], n) // want `vego: what Fprintf builds from what it formats may be more than can be allocated` `vego: precondition of Write may not hold: 3 \* \(\|b\| \+ \|p\|\) \+ 65536 <= MaxAlloc`
	}
	r = b.Bytes()
	return r
}

// Each calls the others with nothing to meet at the call.
// @Ensures True
func Report(xs []string, name string) (r string) {
	r = Pair(Lines(Collect(xs)), Lower(name))
	return r
}

// Doubling a slice 64 times verifies here, and on any input that is not
// empty it runs out of memory, which no proof covers: under the declared
// memory, growth that the program makes itself is no longer checked, only
// what is reserved by a number (F4 of the design review of F38).
// @Modifies s
// @Ensures True
func Doubles(s []byte) (r []byte) {
	r = s
	// @Invariant 0 <= i <= 64
	// @Variant 64 - i
	for i := 0; i < 64; i++ {
		r = append(r, r...) // want `vego: the slice that append grows may be more than can be allocated`
	}
	return r
}

// A reservation in an initialiser is reported where it stands (F12 of the
// review of F38), as in a function; before, a failure there only kept the
// variable from being known.
var reserved = make([]byte, 1<<49) // want `vego: the slice made may be more than can be allocated`

var grown = slices.Grow([]byte(nil), 1<<48) // want `vego: precondition of Grow may not hold: 2 \* \(\|s\| \+ n\) \* elemsize\(s\) \+ 65536 <= MaxAlloc`

// Task is encoded as JSON.
type Task struct {
	ID   int      `json:"id"`
	Text string   `json:"text"`
	Tags []string `json:"tags"`
}

// Encoding grows its output step by step from what exists, so under the
// declared memory it fits whatever the total (step 3 of F38).
// @Ensures True
func Encoded(tasks []Task) (r []byte, err error) {
	r, err = json.Marshal(tasks) // want `vego: what Marshal builds from tasks may be more than can be allocated`
	return r, err
}

// @Ensures True
func Indented(tasks []Task) (r []byte, err error) {
	r, err = json.MarshalIndent(tasks, "", "  ") // want `vego: what MarshalIndent builds from tasks may be more than can be allocated`
	return r, err
}

// @Ensures True
func Counted(counts map[string]int) (r []byte, err error) {
	r, err = json.Marshal(counts) // want `vego: what Marshal builds from counts may be more than can be allocated`
	return r, err
}

// @Requires w != nil
// @Modifies w
// @Ensures True
func Sent(w io.Writer, t Task) (err error) {
	err = json.NewEncoder(w).Encode(t) // want `vego: what Encode builds from t may be more than can be allocated`
	return err
}

// @Ensures True
func Params(values map[string][]string) (r []byte, err error) {
	r, err = json.Marshal(values) // want `vego: cannot verify Params: Marshal encodes values, and values\[k\] holds elements inside the value of values, a map with string keys`
	return r, err
}

// @Ensures True
func Nested(byOwner map[string][]Task) (r []byte, err error) {
	r, err = json.MarshalIndent(byOwner, "", "  ") // want `vego: cannot verify Nested: MarshalIndent encodes byOwner, and byOwner\[k\] holds elements inside the value of byOwner, a map with string keys`
	return r, err
}
