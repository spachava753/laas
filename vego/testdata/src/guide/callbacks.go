package guide

import (
	"math/rand"
	"sort"
	"strings"
)

// The programs of the section on functions that a trusted function calls.

// Position finds where x belongs in a sorted slice.
//
// @Requires Forall i in [0, |s|) : Forall j in [i, |s|) : s[i] <= s[j]
// @Ensures 0 <= i <= |s|
// @Ensures Forall k in [0, i) : s[k] < x
// @Ensures i < |s| -> s[i] >= x
func Position(s []int, x int) (i int) {
	return sort.Search(len(s), func(i int) bool { return s[i] >= x })
}

// isSeparator is verified.
//
// @Ensures b <-> r = 44 Or r = 59
func isSeparator(r rune) (b bool) {
	return r == ',' || r == ';'
}

// FirstField returns what comes before the first separator.
//
// @Ensures |f| <= |line|
func FirstField(line string) (f string) {
	if n := strings.IndexFunc(line, isSeparator); n >= 0 {
		return line[:n]
	}
	return line
}

// HasComma claims to know what the literal left in seen.
//
// @Ensures ~seen
func HasComma(line string) (seen bool) {
	_ = strings.IndexFunc(line, func(r rune) bool {
		if r == ',' {
			seen = true
		}
		return false
	})
	return seen // want `vego: postcondition may not hold: ~seen`
}

// FieldsOf hands FieldsFunc a variable that holds a literal.
//
// @Ensures True
func FieldsOf(line string) (n int) {
	isComma := func(r rune) bool { return r == ',' }
	return len(strings.FieldsFunc(line, isComma)) // want `vego: cannot verify FieldsOf: isComma holds a function literal and is used here other than by calling it`
}

// Hits counts calls.
type Hits struct {
	Calls int
}

func count(t *Hits, record func()) {
	record()
	t.Calls++
}

// Reset hands count a literal that writes what count writes.
//
// @Requires t != nil And t.Calls < 1000
// @Modifies t
// @Ensures True
func Reset(t *Hits) {
	count(t, func() {
		t.Calls = 0 // want `vego: t.Calls is assigned, which count may write itself while it runs the function it is handed; a function it is handed may not write what it may write, in the function literal run by count at callbacks.go:75:11`
	})
}

// Coin hands sort.Search a literal that answers at random.
//
// @Requires n >= 0
// @Ensures True
func Coin(n int) (i int) {
	return sort.Search(n, func(i int) bool { // want `vego: the function literal run by sort.Search is not proved to return the same result whenever it is called with the same argument, which the trusted contract of sort.Search relies on`
		return rand.Intn(2) == 0
	})
}
