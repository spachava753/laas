// Package exits has functions that end the process when they cannot go
// on, and callers that use what is known where they return.
package exits

import (
	"errors"
	"log"
	"os"
)

// ErrEmpty is returned for an empty name.
var ErrEmpty = errors.New("empty name")

// Check ends the process when err is not nil, so it returns only when err
// is nil.
//
// @Exits
// @Ensures err = nil
func Check(err error) {
	if err != nil {
		log.Fatal("failed")
	}
}

// Usage prints how to call the program and ends it.
//
// @Exits
// @Ensures False
func Usage() {
	log.Print("usage: tool name")
	os.Exit(2)
}

// Name returns the first argument after the program's name, and ends the
// process when there is none.
//
// @Exits
// @Ensures |args| >= 2 And name = args[1]
func Name(args []string) (name string) {
	if len(args) < 2 {
		Usage()
	}
	return args[1]
}

// NameExit is Name with os.Exit written out after the call of Usage.
//
// @Exits
// @Ensures |args| >= 2 And name = args[1]
func NameExit(args []string) (name string) {
	if len(args) < 2 {
		Usage()
		os.Exit(2)
	}
	return args[1]
}

// Positive returns n when it is positive and ends the process otherwise.
//
// @Exits
// @Ensures n > 0 And r = n
func Positive(n int) (r int) {
	if n <= 0 {
		log.Fatalf("%d is not positive", n)
	}
	return n
}

// Small returns n when it is at most 10 and ends the process otherwise.
//
// @Exits
// @Ensures n <= 10 And r = n
func Small(n int) (r int) {
	if n > 10 {
		log.Fatalln("too large:", n)
	}
	return n
}

// Between calls two functions that may end the process, in both orders of
// what they check.
//
// @Exits
// @Ensures 0 < r <= 10
func Between(n int) (r int) {
	p := Positive(n)
	return Small(p)
}

// BetweenSwapped checks the bound first.
//
// @Exits
// @Ensures 0 < r <= 10
func BetweenSwapped(n int) (r int) {
	s := Small(n)
	return Positive(s)
}

// Open reads a name and fails with an error for an empty one; it does not
// end the process, so it has no Exits.
//
// @Ensures err = nil <-> |name| > 0
func Open(name string) (err error) {
	if name == "" {
		return ErrEmpty
	}
	return nil
}

// Run calls Open and ends the process on its error, and knows the name is
// not empty after it.
//
// @Exits
// @Ensures r = |name| And r > 0
func Run(name string) (r int) {
	Check(Open(name))
	return len(name)
}

// Dead returns 1: the return after Usage is never reached.
//
// @Exits
// @Ensures r = 1
func Dead(n int) (r int) {
	if n > 0 {
		Usage()
		return 2
	}
	return 1
}

// InPlace ends the process inside a function literal called where it is
// written, which is part of InPlace.
//
// @Exits
// @Ensures r = n And n >= 0
func InPlace(n int) (r int) {
	func() {
		if n < 0 {
			os.Exit(1)
		}
	}()
	return n
}

// one requires its argument to be 1.
//
// @Requires x = 1
// @Ensures True
func one(x int) {
}

// Deferred puts off a call that requires what holds at every return, which
// does not hold where the process ends; no deferred call runs there.
//
// @Exits
// @Ensures r = 1
func Deferred(n int) (r int) {
	r = 1
	defer func() { one(r) }()
	if n < 0 {
		r = 0
		os.Exit(1)
	}
	return r
}

// RunFormatted formats the error it ends the process with, which Open
// made.
//
// @Exits
// @Ensures |name| > 0
func RunFormatted(name string) {
	if err := Open(name); err != nil {
		log.Fatal(err)
	}
}

// Loop ends the process from inside a loop, where its variant is not
// checked.
//
// @Requires |xs| <= 100
// @Exits
// @Ensures Forall k in [0, |xs|) : xs[k] >= 0
func Loop(xs []int) {
	// @Invariant Forall k in [0, i) : xs[k] >= 0
	for i := range xs {
		if xs[i] < 0 {
			os.Exit(1)
		}
	}
}
