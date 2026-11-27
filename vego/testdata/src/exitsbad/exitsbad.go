// Package exitsbad ends the process where it may not, or claims to when it
// does not.
package exitsbad

import (
	"exits"
	"exitslib"
	"log"
	"os"
	"slices"
	"sort"
)

// NoClause ends the process without saying so.
//
// @Ensures True
func NoClause(n int) {
	if n < 0 {
		os.Exit(1) // want `vego: NoClause calls os\.Exit, which may end the process; add // @Exits to the doc comment of NoClause if it may end the process, or call something that returns`
	}
}

// Calls calls a function that may end the process without saying so.
//
// @Ensures r > 0
func Calls(n int) (r int) {
	return exits.Positive(n) // want `vego: Calls calls exits\.Positive, which may end the process; add // @Exits to the doc comment of Calls if it may end the process, or call something that returns`
}

// Unneeded says it may end the process, and nothing it calls does.
//
// @Exits // want `vego: Unneeded has an Exits annotation, but nothing it calls may end the process; remove it, since an Exits annotation must say exactly whether the function may end the process`
// @Ensures True
func Unneeded() {
}

// Conditional writes a condition the clause does not take yet.
//
// @Exits n > 0 // want `vego: an Exits annotation takes nothing after the keyword: the form with a condition, as in // @Exits n > 0, is not supported yet`
// @Ensures True
func Conditional(n int) {
	os.Exit(1)
}

// Twice says it twice.
//
// @Exits
// @Exits // want `vego: function Twice already has an Exits annotation`
// @Ensures True
func Twice() {
	os.Exit(1)
}

// T has a method that would end the process.
type T struct{}

// Stop is a method with Exits.
//
// @Exits // want `vego: a method cannot have an Exits annotation yet: fmt, errors, and conversions to interfaces call methods where no call is written, and a run that ends the process there would not be seen; end the process in a function`
// @Ensures True
func (T) Stop() {
	os.Exit(1)
}

// InBody has the clause inside its body.
//
// @Ensures True
func InBody() {
	// @Exits // want `vego: Exits annotation stands inside InBody; put it in the doc comment of the function`
	os.Exit(1)
}

// OnType has the clause on a type.
//
// @Exits // want `vego: Exits annotation is not attached to a function; put it in the comment directly above the function`
type OnType struct{}

// Misspelt writes Exit.
//
// @Exit // want `vego: unknown annotation "Exit"; an annotation starts with one of Requires, Ensures, Modifies, Calls, Exits, Invariant, Owns, Variant, Visited, Assert, Snapshot, Predicate, State, Receiver, Vouches\. If another tool reads this comment, declare the word with -vego\.other-tags`
// @Ensures True
func Misspelt() {
}

// Stopper is a function type with a contract.
//
// @Ensures True
type Stopper func(code int)

// AsValue makes a value of os.Exit.
//
// @Ensures True
func AsValue() {
	var s Stopper = os.Exit // want `vego: cannot verify AsValue: it uses os\.Exit as a value, and os\.Exit may end the process; a call of a function value is assumed to return, since a function type or a method of an interface cannot have an Exits annotation yet`
	s(1)
}

// LiteralValue makes a value of a literal that ends the process.
//
// @Ensures True
func LiteralValue() (s Stopper) {
	return func(code int) { os.Exit(code) } // want `vego: cannot verify LiteralValue: it calls os\.Exit, which may end the process, in a function literal used as a value of type Stopper; a call of a function value is assumed to return, since a function type cannot have an Exits annotation yet`
}

// LiteralCalled binds a literal that ends the process to a variable that
// is only called, so the literal runs where it is called, as part of
// LiteralCalled, which says it may end the process.
//
// @Exits
// @Ensures True
func LiteralCalled() {
	var s Stopper = func(code int) { os.Exit(code) }
	s(1)
}

// Handed hands a literal that may end the process to a trusted function.
//
// @Requires |xs| <= 100
// @Exits
// @Ensures True
func Handed(xs []int) (found bool) {
	return slices.ContainsFunc(xs, func(x int) bool {
		if x < 0 {
			os.Exit(1) // want `vego: cannot verify Handed: it calls os\.Exit, which may end the process, in a function handed to slices\.ContainsFunc; a function handed to a trusted function may not end the process, since the contract of what calls it assumes that each call returns`
		}
		return x == 0
	})
}

// stopAt ends the process at 0.
//
// @Exits
// @Ensures True
func stopAt(i int) (r bool) {
	if i == 0 {
		os.Exit(1)
	}
	return false
}

// HandedNamed hands a function that may end the process to sort.Search.
//
// @Exits
// @Ensures True
func HandedNamed() (r int) {
	return sort.Search(4, stopAt) // want `vego: cannot verify HandedNamed: it hands stopAt, which may end the process, to Search; a function handed to a trusted function may not end the process, since the contract of what calls it assumes that each call returns`
}

// Deferred defers os.Exit.
//
// @Exits
// @Ensures True
func Deferred() {
	defer os.Exit(1) // want `vego: cannot verify Deferred: deferring a call of os\.Exit, which may end the process, is not supported yet`
}

// DeferredLiteral defers a literal that may end the process.
//
// @Exits
// @Ensures True
func DeferredLiteral(err error) {
	defer func() {
		if err != nil {
			log.Fatal("failed") // want `vego: cannot verify DeferredLiteral: it calls log\.Fatal, which may end the process, in a deferred call; a deferred call that may end the process is not supported yet`
		}
	}()
}

// AfterExit claims what does not hold where Positive returns.
//
// @Exits
// @Ensures r > 1
func AfterExit(n int) (r int) {
	return exits.Positive(n) // want `vego: postcondition may not hold: r > 1`
}

// NotNever claims that it never returns, but it does.
//
// @Exits
// @Ensures False
func NotNever(n int) {
	if n < 0 {
		os.Exit(1)
	}
} // want `vego: postcondition may not hold: False`

// UsesStop calls an entry that never returns.
//
// @Exits
// @Ensures r = 1
func UsesStop(n int) (r int) {
	if n < 0 {
		exitslib.Stop()
		return 2
	}
	return 1
}

// UsesMayStop calls an entry that may end the process, and knows where it
// returns that n >= 0.
//
// @Exits
// @Ensures r >= 0
func UsesMayStop(n int) (r int) {
	return exitslib.MayStop(n)
}

// UsesBoth calls an entry whose False comes with another clause.
//
// @Exits
// @Ensures True
func UsesBoth() (r int) {
	return exitslib.Both() // want `vego: the trusted contract of exitslib\.Both \(trusted\.yaml:\d+\) cannot be used: it contradicts itself, so anything could be proved from it`
}

// UsesFalseOnly calls an entry whose False has no exits.
//
// @Ensures True
func UsesFalseOnly() {
	exitslib.FalseOnly() // want `vego: the trusted contract of exitslib\.FalseOnly \(trusted\.yaml:\d+\) cannot be used: it contradicts itself, so anything could be proved from it`
}

// UsesHalt calls a method whose entry has exits.
//
// @Requires t != nil
// @Ensures True
func UsesHalt(t *exitslib.T) {
	t.Halt() // want `vego: the trusted contract of \(\*exitslib\.T\)\.Halt \(trusted\.yaml:\d+\) cannot be used: exits is allowed only in the entry of a package-level function: fmt, errors, and conversions to interfaces call methods and values of function types where no call is written, and a run that ends the process there would not be seen` `vego: the trusted contract of \(\*exitslib\.T\)\.Halt \(trusted\.yaml:\d+\) cannot be used: it contradicts itself, so anything could be proved from it`
}

// DeferredBound defers a literal that calls a bound literal that may end
// the process (A6 of the review of step 1).
//
// @Exits
// @Ensures True
func DeferredBound(stop bool) {
	f := func() {
		if stop {
			os.Exit(2) // want `vego: cannot verify DeferredBound: it calls os\.Exit, which may end the process, in a deferred call; a deferred call that may end the process is not supported yet`
		}
	}
	defer func() { f() }()
}

// UsesExitCode ends the process with a code its entry allows.
//
// @Exits
// @Ensures False
func UsesExitCode() {
	exitslib.ExitCode(2)
}

// UsesExitCodeZero ends the process with a code its entry does not allow;
// that the call never returns does not excuse its requires.
//
// @Exits
// @Ensures False
func UsesExitCodeZero() {
	exitslib.ExitCode(0) // want `vego: precondition of ExitCode may not hold: code != 0`
}

// UsesExitNever calls an entry whose requires contradict each other.
//
// @Exits
// @Ensures False
func UsesExitNever() {
	exitslib.ExitNever(1) // want `vego: the trusted contract of exitslib\.ExitNever \(trusted\.yaml:\d+\) cannot be used: it contradicts itself, so anything could be proved from it`
}

// BeforeExit indexes before it ends the process; the index is checked.
//
// @Exits
// @Ensures False
func BeforeExit(xs []int) {
	x := xs[3] // want `vego: index may be out of range`
	os.Exit(x)
}

// ReadyClaims claims what does not hold where Stop is not called: the arm
// that returns ready is a real return.
//
// @Exits
// @Ensures ~result
func ReadyClaims(ready bool) (result bool) {
	return ready || exits.Stop() // want `vego: postcondition may not hold: ~result`
}

// stopInt never returns.
//
// @Exits
// @Ensures False
func stopInt() (r int) {
	os.Exit(1)
	return 0
}

// never is never set: its initialiser ends the process.
var never = stopInt()

// GetNever reads never, of which nothing is known (F14 of the review of
// step 1).
//
// @Ensures r = 1
func GetNever() (r int) {
	return never // want `vego: postcondition may not hold: r = 1`
}

// Fail is a method that ends the process, which a method cannot do yet
// (F16 of the review of step 1).
//
// @Ensures True
func (T) Fail() {
	log.Fatal("failed") // want `vego: Fail calls log\.Fatal, which may end the process, and a method cannot end the process yet; return an error, or end the process in a function that calls Fail`
}
