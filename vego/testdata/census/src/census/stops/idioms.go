package stops

import (
	"os"
	"unicode"

	"censusother/lib"
)

// The shapes of F23 of the review: a stub looks at what Go evaluates, as
// Go binds it, and each of these has one cause.

// Exists declares err in the init of an if whose call is refused.
func Exists(n string) bool {
	if _, err := os.Stat(n); err != nil {
		return false
	}
	return true
}

func g(x int) int { return x }

// Switch receives in the init of a switch.
func Switch(ch chan int) int {
	switch x := g(<-ch); x {
	case 1:
		return 1
	}
	return 0
}

// Loop receives in the condition of a loop.
func Loop(ch chan int) int {
	n := 0
	for i := 0; i < g(<-ch); i++ {
		n++
	}
	return n
}

func twoResults() (a int, err error) { return 1, nil }

func mustOf(a int, err error) (r int) { return a }

// MustPair hands the results of one call to another.
func MustPair() (r int) { return mustOf(twoResults()) }

// Map is a generic function of the package.
func Map[T any](xs []T, f func(T) T) []T { return xs }

func double(x int) int { return 2 * x }

// Doubles calls Map with a function of the package.
func Doubles(xs []int) []int { return Map(xs, double) }

// Upper calls a function of another module without an entry, with a
// function of the standard library.
func Upper(s string) string { return lib.Apply(unicode.ToUpper, s) }
