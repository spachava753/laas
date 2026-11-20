// Package stdentries calls the shipped entries of the standard library:
// for each group, functions that verify through them and defective ones
// that are refused.
package stdentries

import (
	"bytes"
	"strings"
)

// KeyValue splits a line around its first '='.
//
// @Ensures ok -> |key| + 1 + |value| = |line|
// @Ensures ok -> Forall k in [0, |key|) : key[k] = line[k]
// @Ensures ~ok -> key = line And |value| = 0
func KeyValue(line string) (key, value string, ok bool) {
	return strings.Cut(line, "=")
}

// Unfound claims that what Cut does not find leaves nothing before it.
//
// @Ensures ~ok -> |key| = 0
func Unfound(line string) (key, value string, ok bool) {
	key, value, ok = strings.Cut(line, "=")
	return key, value, ok // want `postcondition may not hold: ~ok -> \|key\| = 0`
}

// BeforeColon returns what comes before the first colon, or all of s.
//
// @Ensures |result| <= |s|
// @Ensures Forall k in [0, |result|) : result[k] != ':'
func BeforeColon(s string) (result string) {
	if i := strings.IndexByte(s, ':'); i >= 0 {
		return s[:i]
	}
	return s
}

// UpToColon forgets that IndexByte may find nothing.
//
// @Ensures True
func UpToColon(s string) (result string) {
	i := strings.IndexByte(s, ':')
	return s[:i] // want `substring bounds may be out of range`
}

// Ext returns the extension of a name, from its last dot.
//
// @Ensures |result| = 0 Or result[0] = '.'
// @Ensures Forall k in [1, |result|) : result[k] != '.'
func Ext(name string) (result string) {
	i := strings.LastIndexByte(name, '.')
	if i < 0 {
		return ""
	}
	return name[i:]
}

// Heading returns a line without the mark of a heading.
//
// @Requires |line| >= 2 And line[0] = '#' And line[1] = ' '
// @Ensures |result| = |line| - 2
func Heading(line string) (result string) {
	return strings.TrimPrefix(line, "# ")
}

// Parts counts the fields of a line separated by commas.
//
// @Requires |s| <= 1000
// @Ensures 1 <= n And n <= |s| + 1
func Parts(s string) (n int) {
	return len(strings.Split(s, ","))
}

// FirstPart writes the slice Split returns, which is new memory.
//
// @Requires |s| <= 1000
// @Ensures |parts| >= 1 And parts[0] = "x"
func FirstPart(s string) (parts []string) {
	parts = strings.Split(s, ",")
	parts[0] = "x"
	return parts
}

// Rejoin puts the fields of a line back together with another separator.
//
// @Requires |s| <= 1000
// @Ensures |result| <= (|s| + 1) * (|s| + 1)
func Rejoin(s string) (result string) {
	parts := strings.Split(s, ",")
	// @Assert Forall i in [0, |parts|) : |parts[i]| <= |s|
	return strings.Join(parts, ";")
}

// JoinAll joins elements of which nothing is known.
//
// @Ensures True
func JoinAll(elems []string) (result string) {
	return strings.Join(elems, ",") // want `precondition of Join may not hold: Forall i in \[0, \|elems\|\) : \|elems\| \* \(\|elems\[i\]\| \+ \|sep\| \+ 1\) <= MaxInt` `precondition of Join may not hold: Forall i in \[0, \|elems\|\) : \|elems\| \* \(\|elems\[i\]\| \+ \|sep\| \+ 1\) <= MaxAlloc`
}

// Words counts the words of a line.
//
// @Requires |s| <= 1000
// @Ensures 0 <= n And n <= |s| / 2 + 1
func Words(s string) (n int) {
	return len(strings.Fields(s))
}

// Dashes replaces the spaces of a short name.
//
// @Requires |name| <= 100
// @Ensures |result| <= 10100
func Dashes(name string) (result string) {
	return strings.ReplaceAll(name, " ", "-")
}

// Tabs replaces the spaces of a name of any length.
//
// @Ensures True
func Tabs(name string) (result string) {
	return strings.ReplaceAll(name, " ", "\t") // want `precondition of ReplaceAll may not hold: \|s\| \+ \(\|s\| \+ 1\) \* \|new\| <= MaxAlloc`
}

// Same reports whether two words are one word in any case.
//
// @Ensures a = b -> result
func Same(a, b string) (result bool) {
	return strings.EqualFold(a, b)
}

// Commas bounds the number of commas in a line.
//
// @Ensures n <= |s|
func Commas(s string) (n int) {
	return strings.Count(s, ",")
}

// HasDot uses what Contains says when it finds something.
//
// @Ensures result -> |s| >= 1
func HasDot(s string) (result bool) {
	return strings.Contains(s, ".")
}

// IndexOf uses what Index says of the place it returns.
//
// @Ensures i >= 0 -> s[i] = 'a' And s[i + 1] = 'b'
func IndexOf(s string) (i int) {
	return strings.Index(s, "ab")
}

// Trimmed trims a slice of bytes, which is a part of the same memory.
//
// @Requires |b| > 0 And b[0] = 'x'
// @Modifies b
// @Ensures |result| <= |b|
func Trimmed(b []byte) (result []byte) {
	result = bytes.TrimSpace(b)
	if len(result) > 0 {
		result[0] = 'y'
	}
	return result
}

// TrimmedQuietly writes the same part without saying so.
//
// @Ensures |result| <= |b|
func TrimmedQuietly(b []byte) (result []byte) {
	result = bytes.TrimSpace(b)
	if len(result) > 0 {
		result[0] = 'y' // want `result\[0\] is assigned, which TrimmedQuietly may not modify; it is memory that TrimSpace returned, which its contract places within s, and TrimmedQuietly passed b as s; list b in a // @Modifies clause`
	}
	return result
}

// FieldQuietly writes the part of a record before a comma without saying
// so.
//
// @Ensures True
func FieldQuietly(b []byte) (before []byte) {
	before, _, _ = bytes.Cut(b, []byte{','})
	if len(before) > 0 {
		before[0] = 'x' // want `before\[0\] is assigned, which FieldQuietly may not modify; it is memory that Cut returned, which its contract places within s, and FieldQuietly passed b as s; list b in a // @Modifies clause`
	}
	return before
}

// SameBytes compares two slices by their contents.
//
// @Ensures result <-> a = b
func SameBytes(a, b []byte) (result bool) {
	return bytes.Equal(a, b)
}

// SelfEqual hands one slice to Equal twice.
//
// @Ensures True
func SelfEqual(a []byte) (result bool) {
	return bytes.Equal(a, a) // want `the slices passed to Equal as a and b may overlap`
}

// Fields of a record, cut from the bytes it is in.
//
// @Ensures found -> |before| + 1 + |after| = |b|
func Field(b []byte) (before, after []byte, found bool) {
	return bytes.Cut(b, []byte{','})
}

// Copies makes count copies of a short slice.
//
// @Requires |b| <= 100 And 0 <= count And count <= 100
// @Ensures |result| = |b| * count
func Copies(b []byte, count int) (result []byte) {
	result = bytes.Repeat(b, count)
	if len(result) > 0 {
		result[0] = 0
	}
	return result
}
