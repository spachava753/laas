// Package globals reads package-level variables that nothing changes.
package globals

import "errors"

// ErrTooBig is returned for a number above the limit.
var ErrTooBig = errors.New("too big")

// Check succeeds up to a limit that a variable holds.
//
// @Ensures err = nil <-> n <= defaultTimeout
func Check(n int) (err error) {
	if n > defaultTimeout {
		return ErrTooBig
	}
	return nil
}

// CheckComputed succeeds up to a limit whose value is not known. No caller
// chooses it, but the check of a contract that may always fail counts it
// as an input.
//
// @Ensures err = nil <-> n <= computed
func CheckComputed(n int) (err error) {
	if n > computed {
		return ErrTooBig
	}
	return nil
}

var defaultTimeout = 30
var digits = "0123456789abcdef"
var enabled bool
var ratio = 1.5

type Config struct {
	Timeout int
	Name    string
	Retries int
}

var defaults = Config{Timeout: 30, Name: "svc"}

var table = []int{1, 10, 100, 1000}
var buffer = make([]byte, 64)
var limits = map[string]int{"free": 10, "pro": 1000}
var origin = &Config{Timeout: 5}
var alias = defaultTimeout
var computed = twice(4)

func twice(n int) int { return 2 * n }

// Timeout returns the default timeout.
//
// @Ensures r = 30 And r = defaultTimeout
func Timeout() (r int) { return defaultTimeout }

// Hex returns a digit.
//
// @Requires 0 <= d < 16
// @Ensures r = digits[d]
func Hex(d int) (r byte) { return digits[d] }

// Enabled is false, since nothing sets it.
//
// @Ensures ~r
func Enabled() (r bool) { return enabled }

// Defaults reads a struct.
//
// @Ensures r = 30 And n = 3 And retries = 0
func Defaults() (r int, n int, retries int) { return defaults.Timeout, len(defaults.Name), defaults.Retries }

// Length reads the length of a slice made by a literal.
//
// @Ensures r = 4 And r = |table|
func Length() (r int) { return len(table) }

// Byte reads an element of a slice made by make; what it holds is not
// known, but where it is in bounds is.
//
// @Requires 0 <= i < 64
// @Ensures True
func Byte(i int) (b byte) { return buffer[i] }

// Alias holds the value of another variable.
//
// @Ensures r = 30
func Alias() (r int) { return alias }

// Computed is some int.
//
// @Ensures r = computed
func Computed() (r int) { return computed }

// Bounded uses a variable in a contract.
//
// @Requires 0 <= n < defaultTimeout
// @Ensures r = n + 1
func Bounded(n int) (r int) { return n + 1 }

// Origin reads what a pointer that its initialiser made points to, which
// nothing writes.
//
// @Ensures r = 5 And n = 0
func Origin() (r int, n int) { return origin.Timeout, origin.Retries }

// Ratio is one value each time it is read.
//
// @Ensures True
func Ratio() (r float64) { return ratio }

// Inside reads a variable in a function literal and a loop.
//
// @Ensures r = 4
func Inside() (r int) {
	count := func() int { return len(table) }
	// @Invariant 0 <= i <= 2 And (i > 0 -> r = 4)
	// @Variant 2 - i
	for i := 0; i < 2; i++ {
		r = count()
	}
	return r
}

// Pow10 reads an element of a table that is only read.
//
// @Requires 0 <= e < |table|
// @Ensures r = table[e] And (e = 2 -> r = 100)
func Pow10(e int) (r int) { return table[e] }

// Sum adds up the table in a loop that writes another slice, which cannot
// be the table's array.
//
// @Requires |out| = 4
// @Modifies out
// @Ensures r = 1111 And out'[3] = 1000
func Sum(out []int) (r int) {
	// @Invariant 0 <= i <= 4 And |out| = 4
	// @Invariant (i = 0 -> r = 0) And (i = 1 -> r = 1) And (i = 2 -> r = 11) And (i = 3 -> r = 111) And (i = 4 -> r = 1111)
	// @Invariant i = 4 -> out[3] = 1000
	// @Variant 4 - i
	for i := 0; i < 4; i++ {
		out[i] = table[i]
		r += table[i]
	}
	return r
}

// Free reads a map that is only read, with two results.
//
// @Ensures n = 10 And ok
func Free() (n int, ok bool) {
	n, ok = limits["free"]
	return n, ok
}

// Plan reports whether a plan is known: only the keys of the literal are.
//
// @Ensures ok <-> (plan = "free" Or plan = "pro")
// @Ensures |limits| = 2
func Plan(plan string) (ok bool) {
	_, ok = limits[plan]
	return ok
}

var levels = []Config{{Timeout: 1, Name: "low"}, {Timeout: 9, Name: "high"}}

// Level reads a field of an element of a slice of structs.
//
// @Ensures r = 9 And n = 4
func Level() (r int, n int) { return levels[1].Timeout, len(levels[1].Name) }

var magic = []byte("GIF8")

// Magic reads a byte of a slice made from a constant string.
//
// @Ensures r = 70
func Magic() (r byte) { return magic[2] }

// Ranged ranges over a table that is only read.
//
// @Ensures r = 4
func Ranged() (r int) {
	// @Invariant 0 <= r <= 4
	for range table {
		if r < 4 {
			r++
		}
	}
	return 4
}

// Lookup fails for a plan the map does not know, which some input avoids.
//
// @Ensures err = nil <-> (plan = "free" Or plan = "pro")
// @Ensures err = nil -> n = limits[plan]
func Lookup(plan string) (n int, err error) {
	n, ok := limits[plan]
	if !ok {
		return 0, ErrTooBig
	}
	return n, nil
}

// Index fails outside the table.
//
// @Ensures err = nil <-> 0 <= i < |table|
// @Ensures err = nil -> r = table[i]
func Index(i int) (r int, err error) {
	if i < 0 || i >= len(table) {
		return 0, ErrTooBig
	}
	return table[i], nil
}

var runes = []rune("héllo\xff")

// Runes reads a slice of runes made from a constant string: each element
// is a code point, and an invalid byte is U+FFFD.
//
// @Ensures n = 6 And r = 233 And bad = 65533
func Runes() (n int, r rune, bad rune) { return len(runes), runes[1], runes[5] }
