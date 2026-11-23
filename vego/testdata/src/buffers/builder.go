// Package buffers writes strings.Builders and bytes.Buffers through their
// shipped entries, whose length |b| is what Len returns.
package buffers

import "strings"

// Join writes each part and a comma.
//
// @Requires |parts| <= 1000 And (Forall i in [0, |parts|) : |parts[i]| <= 1000)
// @Ensures |r| <= 1001 * |parts|
func Join(parts []string) (r string) {
	var b strings.Builder
	// @Invariant 0 <= i And i <= |parts| And |b| <= 1001 * i
	// @Variant |parts| - i
	for i := 0; i < len(parts); i++ {
		b.WriteString(parts[i])
		b.WriteByte(',')
	}
	return b.String()
}

// JoinUnbounded has no bound on the parts.
//
// @Ensures True
func JoinUnbounded(parts []string) (r string) {
	var b strings.Builder
	// @Invariant 0 <= i And i <= |parts|
	// @Variant |parts| - i
	for i := 0; i < len(parts); i++ {
		b.WriteString(parts[i]) // want `precondition of WriteString may not hold: 2 \* \(\|b\| \+ \|s\|\) \+ 65536 <= MaxAlloc; it holds when \|b\| <= [0-9]+ and \|parts\[i\]\| <= [0-9]+`
	}
	return b.String()
}

// Line appends s and a newline to b.
//
// @Requires b != nil And |b| <= 1000000 And |s| <= 1000
// @Modifies b
// @Ensures |b'| = |b| + |s| + 1
func Line(b *strings.Builder, s string) {
	b.WriteString(s)
	b.WriteByte('\n')
}

// LineUnlisted writes b without listing it.
//
// @Requires b != nil And |b| <= 1000000 And |s| <= 1000
// @Ensures True
func LineUnlisted(b *strings.Builder, s string) {
	b.WriteString(s) // want `WriteString may modify b, which LineUnlisted may not modify`
}

// CallsLine hands Line a builder whose length it knows.
//
// @Ensures |r| = 4
func CallsLine() (r string) {
	var b strings.Builder
	Line(&b, "abc")
	return b.String()
}

// CallsLineLong hands Line a string it cannot bound.
//
// @Ensures True
func CallsLineLong(s string) {
	var b strings.Builder
	Line(&b, s) // want `precondition of Line may not hold: \|s\| <= 1000`
}

// Two writes two builders, each of which keeps its length while the other
// is written.
//
// @Ensures |r| = 2 And |q| = 3
func Two() (r, q string) {
	var a, b strings.Builder
	a.WriteString("x")
	b.WriteString("yyy")
	a.WriteByte('z')
	return a.String(), b.String()
}

// TwoParams writes a and keeps the length of b, which is another builder.
//
// @Requires a != nil And b != nil And a != b And |a| <= 1000
// @Modifies a
// @Ensures |b'| = |b| And |a'| = |a| + 1
func TwoParams(a, b *strings.Builder) {
	a.WriteByte('x')
}

// TwoParamsSame is TwoParams where a may be b.
//
// @Requires a != nil And b != nil And |a| <= 1000
// @Modifies a
// @Ensures |b'| = |b|
func TwoParamsSame(a, b *strings.Builder) {
	a.WriteByte('x')
} // want `postcondition may not hold: \|b'\| = \|b\|`

// Runes writes a rune, whose encoding takes one to four bytes.
//
// @Requires r >= 0
// @Ensures 1 <= n And n <= 4 And (r < 128 -> n = 1)
func Runes(r rune) (n int) {
	var b strings.Builder
	b.WriteRune(r)
	return b.Len()
}

// RunesExact claims a rune always takes one byte.
//
// @Ensures n = 1
func RunesExact(r rune) (n int) {
	var b strings.Builder
	b.WriteRune(r)
	return b.Len() // want `postcondition may not hold: n = 1`
}

// Resets writes, resets, and writes again.
//
// @Ensures n = 2
func Resets() (n int) {
	var b strings.Builder
	b.WriteString("abcdef")
	b.Reset()
	b.WriteString("gh")
	return b.Len()
}

// Grows grows the builder ahead and keeps its length.
//
// @Requires 0 <= k And k <= 1000
// @Ensures n = 1
func Grows(k int) (n int) {
	var b strings.Builder
	b.Grow(k)
	b.WriteByte('a')
	return b.Len()
}

// GrowsNegative may grow by a negative count, which panics.
//
// @Requires k <= 1000
// @Ensures True
func GrowsNegative(k int) {
	var b strings.Builder
	b.Grow(k) // want `precondition of Grow may not hold: 0 <= n`
}

// Capacity names the capacity of a builder, which no contract speaks of.
//
// @Requires b != nil
// @Ensures cap(b) >= 0 // want `cap\(b\): b is a strings.Builder, whose capacity no contract speaks of`
func Capacity(b *strings.Builder) {}

// MyB is a type defined over a Builder, which owns what a Builder owns.
type MyB strings.Builder

// CopiesMyB copies a MyB, which owns memory.
//
// @Ensures True
func CopiesMyB() {
	var x MyB
	y := x // want `copies a value of type MyB, which owns memory`
	_ = y
}

// WritesMyB writes a MyB through its conversion to a Builder, under
// Modifies p, which covers what it owns.
//
// @Requires p != nil And |p| <= 1000
// @Modifies p
// @Ensures True
func WritesMyB(p *MyB) {
	(*strings.Builder)(p).WriteByte('a')
}

// WritesMyBUnlisted is WritesMyB without the Modifies clause.
//
// @Requires p != nil And |p| <= 1000
// @Ensures True
func WritesMyBUnlisted(p *MyB) {
	(*strings.Builder)(p).WriteByte('a') // want `may modify`
}

// HoldsMyB holds a MyB inline, so it owns memory too.
type HoldsMyB struct{ b MyB }

// CopiesHoldsMyB copies a struct that holds a MyB.
//
// @Ensures True
func CopiesHoldsMyB() {
	var x HoldsMyB
	y := x // want `copies a value of type HoldsMyB, which holds a MyB`
	_ = y
}
