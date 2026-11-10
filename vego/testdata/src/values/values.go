// Package values exercises errors, floats, and strings: values the verifier
// follows without knowing much, or anything, about their contents.
package values

import (
	"errors"
	"fmt"
	"os"
)

var errOutOfRange = errors.New("index out of range")

// ErrReassigned is not a reliable sentinel: reset assigns to it.
var ErrReassigned = errors.New("reassigned")

func reset() { ErrReassigned = nil }

// At returns the element at i, or an error when there is none.
func At(A []int, i int) (value int, err error) {
	if i < 0 || i >= len(A) {
		return 0, errOutOfRange
	}
	return A[i], nil
}

//@ Ensures err = nil <-> (0 <= i And i < |A|)
//@ Ensures err = nil -> value = A[i]

// First proves that the error cannot happen, so the panic is unreachable.
//
// @ Requires |A| > 0
func First(A []int) (value int) {
	value, err := At(A, 0)
	if err != nil {
		panic(err)
	}
	return value
}

//@ Ensures value = A[0]

// Unchecked panics on an error that can happen.
func Unchecked(A []int, i int) (value int) {
	value, err := At(A, i)
	if err != nil {
		panic(err) // want `vego:\ panic\ may\ be\ reachable`
	}
	return value
}

//@ Ensures value = A[i]

// Propagates hands the callee's error on.
func Propagates(A []int, i int) (double int, err error) {
	value, err := At(A, i)
	if err != nil {
		return 0, err
	}
	if value > 1000 || value < -1000 {
		return 0, fmt.Errorf("value %d is too large", value)
	}
	return 2 * value, nil
}

//@ Ensures err = nil -> (0 <= i And i < |A| And double = 2 * A[i])
//@ Ensures (0 <= i And i < |A| And -1000 <= A[i] And A[i] <= 1000) -> err = nil

// OnlySaysWhatSuccessMeans never says that it succeeds, so an implementation
// that always fails would meet its contract.
func OnlySaysWhatSuccessMeans(A []int, i int) (value int, err error) { // want `vego:\ the\ contract\ of\ OnlySaysWhatSuccessMeans\ would\ also\ be\ met\ by\ a\ function\ that\ always\ returns\ an\ error;\ state\ when\ it\ succeeds,\ for\ example\ with\ "condition\ \->\ err\ =\ nil"`
	if i < 0 || i >= len(A) {
		return 0, errOutOfRange
	}
	return A[i], nil
}

//@ Ensures err = nil -> value = A[i]

// NoPostcondition has the same problem with no postcondition at all.
//
// @ Requires i >= 0
func NoPostcondition(A []int, i int) (int, error) { // want `vego:\ the\ contract\ of\ NoPostcondition\ would\ also\ be\ met\ by\ a\ function\ that\ always\ returns\ an\ error;\ state\ when\ it\ succeeds,\ for\ example\ with\ "condition\ \->\ err\ =\ nil"`
	if i >= len(A) {
		return 0, errOutOfRange
	}
	return A[i], nil
}

// UnreliableSentinel cannot show that its error is non-nil.
func UnreliableSentinel(ok bool) (err error) {
	if !ok {
		return ErrReassigned // want `vego:\ cannot\ verify\ UnreliableSentinel:\ ErrReassigned\ is\ not\ a\ local\ variable\ of\ a\ supported\ type`
	}
	return nil
}

//@ Ensures err = nil <-> ok = True

// Size cannot say when it succeeds: that depends on the file system. It calls
// a function without a contract that returns an error, so it is excused.
func Size(path string) (size int, err error) {
	info, err := stat(path)
	if err != nil {
		return 0, err
	}
	if info < 0 {
		return 0, errOutOfRange
	}
	return info, nil
}

//@ Ensures err = nil -> size >= 0

func stat(path string) (int, error) {
	info, err := os.Stat(path)
	if err != nil {
		return 0, err
	}
	return int(info.Size()), nil
}

// DoubleSize is excused through Size.
func DoubleSize(path string) (size int, err error) {
	size, err = Size(path)
	if err != nil || size > 1000000 {
		return 0, errOutOfRange
	}
	return 2 * size, nil
}

//@ Ensures err = nil -> size >= 0

// Average shows opaque floats: the indexing and the integer arithmetic are
// proved, and nothing is known or claimed about the result.
//
// @ Requires |A| <= 1000 And Forall k in [0, |A|) : (0 <= A[k] And A[k] <= 1000)
func Average(A []int) float64 {
	sum := 0
	//@ Invariant 0 <= sum <= 1000 * i
	for i := range A {
		sum += A[i]
	}
	return float64(sum) / float64(len(A))
}

// Bucket indexes with a number computed from a float, which could be anything.
//
// @ Requires |counts| > 0
func Bucket(counts []int, ratio float64) int {
	bucket := int(ratio * float64(len(counts)))
	return counts[bucket] // want `vego:\ index\ may\ be\ negative` `vego:\ index\ may\ be\ out\ of\ range`
}

// CheckedBucket range-checks the number first.
//
// @ Requires |counts| > 0
func CheckedBucket(counts []int, ratio float64) int {
	bucket := int(ratio * float64(len(counts)))
	if bucket < 0 || bucket >= len(counts) {
		return 0
	}
	return counts[bucket]
}

// Scale stores floats in a slice; only its length is tracked.
func Scale(xs []float64, factor float64) {
	for i := range xs {
		xs[i] *= factor
	}
}

//@ Ensures |xs'| = |xs|

// Hot compares floats; either branch may be taken.
func Hot(celsius float64) (level int) {
	if celsius > 30.5 {
		return 2
	}
	return 1 // want `vego:\ postcondition\ may\ not\ hold:\ level\ =\ 2`
}

//@ Ensures level = 1 Or level = 2
//@ Ensures level = 2

// IsAdmin compares strings.
func IsAdmin(role string) (ok bool) {
	return role == "admin"
}

//@ Ensures ok = True <-> role = "admin"

// FirstByte reads a byte that exists.
//
// @ Requires |s| > 0
func FirstByte(s string) (b byte) {
	return s[0]
}

//@ Ensures b = s[0]

// LastByte reads past the end of an empty string.
func LastByte(s string) byte {
	//@ Assert |s| >= 0
	return s[len(s)-1] // want `vego:\ index\ may\ be\ negative`
}

// Greeting concatenates strings of bounded length.
//
// @ Requires |name| <= 100
func Greeting(name string) (text string) {
	return "hello, " + name
}

//@ Ensures |text| = |name| + 7
//@ Ensures text[0] = 104 And (|name| > 0 -> text[7] = name[0])

// Unbounded concatenates strings whose total length is not known to fit.
func Unbounded(a, b string) string {
	//@ Assert True
	return a + b // want `vego:\ string\ length\ may\ overflow\ int`
}

// Extension returns the last three bytes.
//
// @ Requires |name| >= 3
func Extension(name string) (ext string) {
	return name[len(name)-3:]
}

//@ Ensures |ext| = 3 And ext[2] = name[|name|-1]

// BadCut slices past the end.
func BadCut(name string) string {
	//@ Assert True
	return name[:3] // want `vego:\ substring\ bounds\ may\ be\ out\ of\ range`
}

// CountSpaces walks the bytes of a string.
func CountSpaces(s string) (n int) {
	//@ Invariant 0 <= n <= i <= |s|
	//@ Variant |s| - i
	for i := 0; i < len(s); i++ {
		if s[i] == ' ' {
			n++
		}
	}
	return n
}

//@ Ensures 0 <= n <= |s|

// CountChars walks the characters of a string, each one to four bytes long.
func CountChars(s string) (n int) {
	//@ Invariant 0 <= n <= i
	for i, r := range s {
		if r != ' ' && i >= 0 {
			n++
		}
	}
	return n // want `vego:\ postcondition\ may\ not\ hold:\ n\ =\ \|s\|`
}

//@ Ensures 0 <= n <= |s|
//@ Ensures n = |s|

// Reassigned may rebind a string parameter: the caller's string is its own.
func Reassigned(s string) (n int) {
	s = "ab"
	return len(s)
}

//@ Ensures n = 2

// Bytes copies a string into a slice that can then be changed freely.
//
// @ Requires |s| > 0
func Bytes(s string) (b []byte) {
	b = []byte(s)
	b[0] = 'x'
	return b
}

//@ Ensures |b| = |s| And b[0] = 120
//@ Ensures Forall k in [1, |s|) : b[k] = s[k]

// Before orders strings, which is not modelled.
func Before(a, b string) (less bool) {
	return a < b // want `vego:\ postcondition\ may\ not\ hold:\ less\ =\ True`
}

//@ Ensures less = True

// Classify switches on a string; a case matches when the strings are equal.
func Classify(role string) (level int) {
	switch role {
	case "admin":
		return 2
	case "user":
		return 1 // want `vego:\ postcondition\ may\ not\ hold:\ level\ !=\ 1`
	}
	return 0
}

//@ Ensures role = "admin" -> level = 2
//@ Ensures level = 2 -> role = "admin"
//@ Ensures level != 1

// SameFloat switches on a float. A float need not equal itself: NaN does not.
func SameFloat(f float64) (same bool) {
	switch f {
	case f:
		return true
	}
	return false // want `vego:\ postcondition\ may\ not\ hold:\ same\ =\ True`
}

//@ Ensures same = True

// Describe switches on an error.
func Describe(err error) (code int) {
	switch err {
	case nil:
		return 0
	case errOutOfRange:
		return 1 // want `vego:\ postcondition\ may\ not\ hold:\ code\ !=\ 1`
	}
	return 2
}

//@ Ensures err = nil <-> code = 0
//@ Ensures code != 1

// Lookup has two unnamed results, called result1 and result2.
func Lookup(A []int, i int) (int, error) {
	if i < 0 || i >= len(A) {
		return 0, errOutOfRange
	}
	return A[i], nil
}

//@ Ensures result2 = nil <-> (0 <= i And i < |A|)
//@ Ensures result2 = nil -> result1 = A[i]
