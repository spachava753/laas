// Package settled initialises its variables with calls that Go's ordering
// follows, so its error variables have their values before any of its
// functions can run.
package settled

import (
	"bufio"
	"context"
	"errors"
	"fmt"
	"os"
	"slices"
	"strings"
)

func twice(s string) string { return s + s }

// Name is computed by calls that Go follows.
var Name = twice(strings.ToUpper("x"))

// Later is a function kept for later; writing it down runs nothing.
var Later = func(f func()) { f() }

// ErrWrapped is made from another error variable of the package, and
// Joined from a variable of another package that has no room for code;
// neither holds code of this package.
var ErrWrapped = fmt.Errorf("%w: wrapped", ErrY)

// Joined is the command line.
var Joined = strings.Join(os.Args, " ")

// Out is made from a variable of another package, which nothing of this
// package was put into.
var Out = bufio.NewWriter(os.Stderr)

// Names is sorted by a generic function of another package, given a type
// with no methods.
var Names = sortedNames()

func sortedNames() []string {
	out := []string{"b", "a"}
	slices.Sort(out)
	return out
}

// Limit is computed by a function written out and called on the spot.
var Limit = func() int {
	n := 3
	return n * 2
}()

// Root is what another package returned, and Sub is made from it.
var Root = context.Background()

// Sub and Stop come from Root.
var Sub, Stop = context.WithCancel(Root)

// ErrY is set before anything else of the package runs.
var ErrY = errors.New("y")

// Ok reports that it is.
func Ok() bool {
	return ErrY != nil && ErrWrapped != nil
}

//@ Ensures result
