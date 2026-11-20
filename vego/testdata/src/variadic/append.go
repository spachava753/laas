package variadic

import "sync"

// append(s, t...) adds the elements of t, which it copies as memmove does:
// what it adds is what t held before the write, also when t shares the
// array of s.

// @Requires |xs| + |ys| <= 1000
// @Modifies xs
// @Ensures |r| = |xs| + |ys|
// @Ensures Forall i in [0, |xs|) : r[i] = xs[i]
// @Ensures Forall i in [0, |ys|) : r[|xs| + i] = ys[i]
func Concat(xs, ys []int) (r []int) {
	return append(xs, ys...)
}

// Without the leave to write xs, an append that fits writes its capacity.
//
// @Requires |xs| + |ys| <= 1000
// @Ensures |r| = |xs| + |ys|
func ConcatUnlisted(xs, ys []int) (r []int) {
	return append(xs, ys...) // want `vego:\ append\ may\ write\ into\ the\ capacity\ of\ xs,\ which\ ConcatUnlisted\ may\ not\ modify`
}

// @Requires |xs| + |ys| <= 1000
// @Modifies xs
// @Ensures |r| = |xs| + |ys| + 1
func ConcatWrong(xs, ys []int) (r []int) {
	return append(xs, ys...) // want `vego:\ postcondition\ may\ not\ hold:\ \|r\|\ =\ \|xs\|\ \+\ \|ys\|\ \+\ 1`
}

// Delete removes the element at i, moving the ones after it down.
//
// @Requires 0 <= i < |s|
// @Modifies s
// @Ensures |r| = |s| - 1
// @Ensures Forall k in [0, i) : r[k] = s[k]
// @Ensures Forall k in [i, |s| - 1) : r[k] = s[k + 1]
func Delete(s []int, i int) (r []int) {
	return append(s[:i], s[i+1:]...)
}

// The element after the gap is what was two places on, not what the gap
// held.
//
// @Requires 0 <= i < |s| - 1 And s[i] != s[i + 2]
// @Modifies s
// @Ensures r[i] = s[i]
func DeleteWrong(s []int, i int) (r []int) {
	return append(s[:i], s[i+1:]...) // want `vego:\ postcondition\ may\ not\ hold:\ r\[i\]\ =\ s\[i\]`
}

// Shift moves the first two elements up by one. The second element
// written is what the second held before, not the copy of the first that
// an element-by-element copy from the front would have put there.
//
// @Requires |s| >= 3
// @Modifies s
// @Ensures |r| = 3 And r[0] = s[0] And r[1] = s[0] And r[2] = s[1]
func Shift(s []int) (r []int) {
	return append(s[:1], s[:2]...)
}

// @Requires |s| >= 3 And s[0] != s[1]
// @Modifies s
// @Ensures r[2] = s[0]
func ShiftWrong(s []int) (r []int) {
	return append(s[:1], s[:2]...) // want `vego:\ postcondition\ may\ not\ hold:\ r\[2\]\ =\ s\[0\]`
}

// Twice appends a slice to itself.
//
// @Requires |s| <= 1000
// @Modifies s
// @Ensures |r| = 2 * |s|
// @Ensures Forall k in [0, |s|) : r[k] = s[k] And r[|s| + k] = s[k]
func Twice(s []int) (r []int) {
	return append(s, s...)
}

// Overlay writes s over its own tail from k on.
//
// @Requires 0 <= k <= |s| And |s| <= 1000
// @Modifies s
// @Ensures |r| = k + |s|
// @Ensures Forall j in [0, |s|) : r[k + j] = s[j]
func Overlay(s []int, k int) (r []int) {
	return append(s[:k], s...)
}

// @Requires 0 < k < |s| And |s| <= 1000 And s[0] != s[k]
// @Modifies s
// @Ensures r[2 * k] = s[0]
func OverlayWrong(s []int, k int) (r []int) {
	return append(s[:k], s...) // want `vego:\ postcondition\ may\ not\ hold:\ r\[2\ \*\ k\]\ =\ s\[0\]`
}

// AddText appends the bytes of a string.
//
// @Requires |b| + |text| <= 1000
// @Modifies b
// @Ensures |r| = |b| + |text|
// @Ensures Forall i in [0, |b|) : r[i] = b[i]
// @Ensures Forall i in [0, |text|) : r[|b| + i] = text[i]
func AddText(b []byte, text string) (r []byte) {
	return append(b, text...)
}

// @Requires |b| + |text| <= 1000 And |text| > 0
// @Modifies b
// @Ensures r[|b|] = 0
func AddTextWrong(b []byte, text string) (r []byte) {
	return append(b, text...) // want `vego:\ postcondition\ may\ not\ hold:\ r\[\|b\|\]\ =\ 0`
}

type Point struct{ X, Y int }

// Each field of an added struct comes along.
//
// @Requires |ps| + |qs| <= 1000
// @Modifies ps
// @Ensures |r| = |ps| + |qs|
// @Ensures Forall i in [0, |qs|) : r[|ps| + i].X = qs[i].X And r[|ps| + i].Y = qs[i].Y
func AddPoints(ps, qs []Point) (r []Point) {
	return append(ps, qs...)
}

// Appending nothing gives back the slice.
//
// @Requires |s| > 0
// @Ensures |r| = |s| And r[0] = s[0]
func AddNothing(s []int) (r []int) {
	return append(s, []int{}...)
}

// The append may write into the array that t lies in, and Go may read t[0]
// in the target before or after that.
//
// @Requires |t| > 0 And |u| > 0 And 0 <= t[0] < |u| And |w| <= 1000
// @Modifies u, t
// @Ensures True
func OrderSpread(u [][]int, t, w []int) {
	u[t[0]] = append(t[:0], w...) // want `vego:\ t\[0\]\ may\ be\ read\ before\ or\ after\ the\ write\ of\ append\ into\ the\ array\ of\ t\[:0\]`
}

type Guarded struct {
	mu sync.Mutex
	n  int
}

// Adding values that hold a mutex copies them.
//
// @Requires |gs| + |hs| <= 1000
// @Modifies gs
// @Ensures True
func AddGuarded(gs, hs []Guarded) (r []Guarded) {
	return append(gs, hs...) // want `vego:\ cannot\ verify\ AddGuarded:\ append\ to\ a\ slice\ of\ Guarded,\ which\ holds\ a\ sync\.Mutex`
}

// Nothing bounds |ys|, so the array append moves to may be more than can
// be allocated. The runtime may make it up to twice as large as it needs.
//
// @Requires |xs| < 10
// @Modifies xs
// @Ensures True
func LongTail(xs, ys []int) (r []int) {
	return append(xs, ys...) // want `vego:\ the\ slice\ that\ append\ grows\ may\ be\ more\ than\ can\ be\ allocated`
}
