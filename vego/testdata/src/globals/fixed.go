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

// Origin is not nil. What it points to is memory, of which nothing is
// known on entry.
//
// @Ensures r = 5
func Origin() (r int) {
	return origin.Timeout // want `vego: postcondition may not hold: r = 5`
}

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
