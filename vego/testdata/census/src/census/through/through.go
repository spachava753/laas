// Package through holds functions that the census lets through: each meets
// no refusal on the weakest contract, which is not to say it verifies.
package through

import (
	"encoding/json"
	"io"
	"log"
	"os"
	"strings"
)

func add(x, y int) int { return x + y }

// Sum calls a function of the module, which the census assumes.
func Sum(xs []int) int {
	total := 0
	for _, x := range xs {
		total = add(total, x)
	}
	return total
}

// Index calls a function of the standard library with a shipped entry.
func Index(s string) int { return strings.Index(s, "x") }

// Each calls a parameter of an unnamed function type, which a Calls
// annotation would give a contract.
func Each(xs []int, f func(int)) {
	for _, x := range xs {
		f(x)
	}
}

// Total hands a literal to Each, which the census assumes; the literal is
// walked on its own.
func Total(xs []int) {
	Each(xs, func(x int) { _ = x + 1 })
}

// Reader is an interface of the module whose methods leave their results
// unnamed and have no contract (F12 of the review).
type Reader interface {
	Next(p []byte) (int, error)
}

type file struct{ n int }

func (f *file) Next(p []byte) (int, error) { return f.n, nil }

// Drain calls a method of an interface of the module.
func Drain(r Reader) error {
	_, err := r.Next(nil)
	return err
}

// Open converts a value of the module to an interface of the module.
func Open() Reader { return &file{} }

// Unreachable holds statements no path reaches (F10 of the review), none
// of which make it partial.
func Unreachable(x int) int {
	switch {
	case x > 0:
		return 1
	default:
		return 0
	}
	panic("unreachable")
}

// AfterExit holds a statement after a call that ends the process.
func AfterExit(err error) int {
	if err != nil {
		log.Fatal("failed")
		return 1
	}
	return 0
}

// Forever holds a statement after a loop with no way out.
func Forever(x int) int {
	for {
		x++
		if x > 10 {
			return x
		}
	}
	return 0
}

// Exit ends the process, which a function may do.
func Exit() {
	os.Exit(2)
	return
}

type record struct {
	Name string
}

// Encode writes a value as JSON; the census goes on past the cut it makes
// (F9 of the review).
func Encode(w io.Writer, r record) error {
	return json.NewEncoder(w).Encode(r)
}

// Closure has a recursive closure, which the census looks at as one (F16
// of the review).
func Closure(n int) (r int) {
	var walk func(k int) (s int)
	walk = func(k int) (s int) {
		if k <= 0 {
			return 0
		}
		return k + walk(k-1)
	}
	return walk(n)
}
