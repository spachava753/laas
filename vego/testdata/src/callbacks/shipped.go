package callbacks

import (
	"bytes"
	"sort"
	"strings"
)

// SearchSorted hands sort.Search a literal that indexes the slice it
// captures.
//
// @Ensures 0 <= i <= |s|
func SearchSorted(s []int, x int) (i int) {
	return sort.Search(len(s), func(i int) bool { return s[i] >= x }) // want `vego: postcondition may not hold: 0 <= i <= \|s\|`
}

// SearchPast indexes one further.
//
// @Ensures True
func SearchPast(s []int, x int) (i int) {
	return sort.Search(len(s), func(i int) bool { return s[i+1] >= x }) // want `vego: index may be out of range, in the function literal run by sort.Search`
}

// FindIn hands sort.Find a comparison.
//
// @Ensures True
func FindIn(s []int, x int) (found bool) {
	_, found = sort.Find(len(s), func(k int) int { return x - s[k] }) // want `vego: subtraction may overflow int, in the function literal run by sort.Find`
	return found
}

// isSeparator is verified.
//
// @Ensures b <-> r = 44 Or r = 59
func isSeparator(r rune) (b bool) {
	return r == ',' || r == ';'
}

// FirstField cuts a line at its first separator.
//
// @Ensures |f| <= |line|
func FirstField(line string) (f string) {
	if n := strings.IndexFunc(line, isSeparator); n >= 0 {
		return line[:n]
	}
	return line
}

// FirstFieldUnchecked cuts without looking at what IndexFunc returned.
//
// @Ensures True
func FirstFieldUnchecked(line string) (f string) {
	n := strings.IndexFunc(line, func(r rune) bool { return r == ',' })
	return line[:n] // want `vego: substring bounds may be out of range`
}

// Trimmed trims a line by a literal that captures what to trim.
//
// @Ensures |t| <= |line|
func Trimmed(line string, cut rune) (t string) {
	return strings.TrimFunc(line, func(r rune) bool { return r == cut })
}

// Upper maps a line with a named function.
//
// @Ensures True
func Upper(line string) (u string) {
	return strings.Map(shout, line)
}

// shout maps lower case ASCII to upper case.
//
// @Ensures True
func shout(r rune) (s rune) {
	if 'a' <= r && r <= 'z' {
		return r - 32
	}
	return r
}

// TrimBytes trims a slice it may modify by a literal that writes it.
//
// @Modifies b
// @Ensures |t| <= |b|
func TrimBytes(b []byte) (t []byte) {
	return bytes.TrimFunc(b, func(r rune) bool {
		if len(b) > 0 {
			b[0] = 'x'
		}
		return r == ' '
	})
}

// TrimBytesOutside writes it without listing it.
//
// @Ensures True
func TrimBytesOutside(b []byte) (t []byte) {
	return bytes.TrimFunc(b, func(r rune) bool {
		if len(b) > 0 {
			b[0] = 'x' // want `vego: b\[0\] is assigned, which TrimBytesOutside may not modify`
		}
		return r == ' '
	})
}
