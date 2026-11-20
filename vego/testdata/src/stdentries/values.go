package stdentries

import (
	"math"
	"sort"
	"strconv"
	"time"
	"unicode"
	"unicode/utf8"
)

// Runes counts the runes of s by decoding them one at a time.
//
// @Ensures 0 <= n And n <= |s|
func Runes(s string) (n int) {
	i := 0
	// @Invariant 0 <= i And i <= |s| And 0 <= n And n <= i
	// @Variant |s| - i
	for i < len(s) {
		_, size := utf8.DecodeRuneInString(s[i:])
		i += size
		n++
	}
	return n
}

// FirstASCII returns the first byte of s when it is ASCII.
//
// @Requires |s| > 0 And s[0] < 128
// @Ensures r = s[0]
func FirstASCII(s string) (r rune) {
	r, _ = utf8.DecodeRuneInString(s)
	return r
}

// Stuck forgets that DecodeRune of an empty slice reads nothing.
//
// @Ensures True
func Stuck(p []byte) (n int) {
	i := 0
	// @Invariant 0 <= i And i <= |p|
	// @Variant |p| - i
	for i <= len(p) { // want `loop variant may not decrease`
		_, size := utf8.DecodeRune(p[i:])
		i += size
		n = i
	}
	return n
}

// Encode appends the encoding of a rune to new memory.
//
// @Requires 0 <= r And r < 128
// @Ensures |result| = 1 And result[0] = r
func Encode(r rune) (result []byte) {
	return utf8.AppendRune(nil, r)
}

// Width is the number of bytes of a valid rune.
//
// @Requires 0 <= r And r < 55296
// @Ensures 1 <= n And n <= 3
func Width(r rune) (n int) {
	return utf8.RuneLen(r)
}

// Blank reports whether a byte of ASCII is white space.
//
// @Requires c < 128
// @Ensures result <-> (c = ' ' Or c = '\t' Or c = '\n' Or c = '\v' Or c = '\f' Or c = '\r')
func Blank(c byte) (result bool) {
	return unicode.IsSpace(rune(c))
}

// DigitValue returns the value of an ASCII digit.
//
// @Requires c < 128
// @Ensures 0 <= v And v <= 9
func DigitValue(c byte) (v int) {
	if !unicode.IsDigit(rune(c)) {
		return 0
	}
	return int(c - '0')
}

// Shout says nothing of a letter beyond ASCII.
//
// @Ensures result -> r < 128
func Shout(r rune) (result bool) {
	return unicode.IsUpper(r) // want `postcondition may not hold: result -> r < 128`
}

// Port parses a port number, which fits 16 bits.
//
// @Ensures err = nil -> 0 <= p And p <= 65535
func Port(s string) (p int, err error) {
	n, err := strconv.ParseUint(s, 10, 16)
	if err != nil {
		return 0, err
	}
	return int(n), nil
}

// Small parses a number into an int32 without a check.
//
// @Ensures True
func Small(s string) (r int32, err error) {
	n, err := strconv.ParseInt(s, 10, 32)
	if err != nil {
		return 0, err
	}
	return int32(n), nil
}

// Wide parses a number of 64 bits into an int32.
//
// @Ensures True
func Wide(s string) (r int32, err error) {
	n, err := strconv.ParseInt(s, 10, 64)
	if err != nil {
		return 0, err
	}
	return int32(n), nil // want `conversion may not fit int32`
}

// Flag parses a boolean.
//
// @Ensures s = "1" -> err = nil And on
func Flag(s string) (on bool, err error) {
	return strconv.ParseBool(s)
}

// Label builds a label from a number, short enough to join with more.
//
// @Ensures |result| <= 26
func Label(n int64) (result string) {
	return "item-" + strconv.FormatInt(n, 10)
}

// Hex writes a number in a base of its caller's choice.
//
// @Ensures True
func Hex(n int64, base int) (result string) {
	return strconv.FormatInt(n, base) // want `precondition of FormatInt may not hold: 2 <= base` `precondition of FormatInt may not hold: base <= 36`
}

// Quoted quotes a short name.
//
// @Requires |name| <= 100
// @Ensures 2 <= |result| And |result| <= 1002
func Quoted(name string) (result string) {
	return strconv.Quote(name)
}

// Literal unquotes a literal, whose error can be wrapped.
//
// @Requires |s| <= 1000
// @Ensures err = nil -> |s| >= 2
func Literal(s string) (value string, err error) {
	return strconv.Unquote(s)
}

// SortNames sorts names, which stay as short as they were.
//
// @Requires Forall i in [0, |names|) : |names[i]| <= 64
// @Modifies names
// @Ensures Forall i in [0, |names|) : |names'[i]| <= 64
func SortNames(names []string) {
	sort.Strings(names)
}

// Root takes a square root, of which nothing is known.
//
// @Ensures True
func Root(n int) (r float64) {
	return math.Sqrt(float64(n))
}

// MonthName names the month of a time.
//
// @Requires |names| = 12
// @Ensures True
func MonthName(t time.Time, names []string) (name string) {
	return names[t.Month()-1]
}

// MonthNameOff indexes past the last month.
//
// @Requires |names| = 12
// @Ensures True
func MonthNameOff(t time.Time, names []string) (name string) {
	return names[t.Month()] // want `index may be out of range`
}

// Elapsed is the time since a start, in milliseconds.
//
// @Ensures True
func Elapsed(start time.Time) (ms int64) {
	return time.Since(start).Milliseconds()
}
