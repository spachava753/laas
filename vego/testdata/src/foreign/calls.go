// Package foreign calls through values of types of another module, whose
// contracts are entries of the trust file.
package foreign

import (
	"errors"

	"foreignannotated"
	"foreignlib"
)

// @Requires s != nil And 0 <= a <= 100
// @Ensures err = nil -> 0 <= y <= 200
func PutOne(s foreignlib.Sink, a int) (y int, err error) {
	return s.Put(a)
}

// @Requires s != nil
// @Ensures True
func PutAny(s foreignlib.Sink, a int) (y int, err error) {
	return s.Put(a) // want `precondition of s.Put may not hold: 0 <= x` `precondition of s.Put may not hold: x <= 100`
}

// @Requires 0 <= a <= 100
// @Ensures True
func PutNil(s foreignlib.Sink, a int) (y int, err error) {
	return s.Put(a) // want `the interface value s may be nil`
}

// @Requires s != nil And 0 <= a <= 100
// @Ensures err = nil -> y <= 100
func PutTooMuch(s foreignlib.Sink, a int) (y int, err error) {
	return s.Put(a) // want `postcondition may not hold: err = nil -> y <= 100`
}

// A store has Put from Sink, with the contract of Sink.Put, and Size of its
// own.
//
// @Requires st != nil
// @Ensures n >= 0
// @Ensures err = nil -> 0 <= y <= 2
func PutStore(st foreignlib.Store) (n int, y int, err error) {
	y, err = st.Put(1)
	return st.Size(), y, err
}

// Box is memory that the caller holds.
type Box struct {
	N int
}

// What Put does not list is unchanged across the call: the entry claims
// that it writes nothing verified code can see.
//
// @Requires s != nil And b != nil
// @Modifies b
// @Ensures b.N' = 7
func Frame(s foreignlib.Sink, b *Box) {
	b.N = 7
	_, _ = s.Put(1)
}

// What Fill lists is forgotten.
//
// @Requires f != nil And |p| = 1
// @Modifies p
// @Ensures p'[0] = 7
func Forgets(f foreignlib.Filler, p []int) {
	p[0] = 7
	f.Fill(p)
} // want `postcondition may not hold: p'\[0\] = 7`

// A loop forgets what Fill lists, and keeps the rest.
//
// @Requires f != nil And b != nil And 0 <= n <= 10
// @Modifies p, b
// @Ensures b.N' = 3
func Loops(f foreignlib.Filler, p []int, b *Box, n int) {
	b.N = 3
	// @Invariant b.N = 3 And 0 <= i <= n
	// @Variant n - i
	for i := 0; i < n; i++ {
		f.Fill(p)
	}
}

// @Requires h != nil
// @Ensures True
func Deferred(h foreignlib.Hook) {
	defer h()
}

// @Ensures True
func DeferredNil(h foreignlib.Hook) {
	defer h() // want `the function value h may be nil`
}

// @Requires m != nil
// @Ensures y = 6
func Maps(m foreignlib.Mapper) (y int) {
	return m(3)
}

// @Requires m != nil
// @Ensures True
func MapsTooFar(m foreignlib.Mapper) (y int) {
	return m(11) // want `precondition of m may not hold: x <= 10`
}

// @Requires f != nil
// @Ensures err != nil -> err = foreignlib.ErrFull
func Fail(f foreignlib.Fails) (err error) {
	return f()
}

// @Requires f != nil
// @Ensures True
func Halves(f foreignlib.Half) (y int) {
	return f(3) // want `the trusted contract of foreignlib.Half \(trusted.yaml:\d+\) cannot be used: the Ensures clauses of Half are not proved to be satisfiable`
}

// @Requires f != nil
// @Ensures True
func Kept(f foreignlib.Keeps) {
	f(errors.New("x")) // want `the trusted contract of foreignlib.Keeps \(trusted.yaml:\d+\) cannot be used: it lists keeps, which a contract of a type cannot have`
}

// @Requires f != nil
// @Ensures True
func Ran(f foreignlib.Runs) {
	f(errors.New("x")) // want `the trusted contract of foreignlib.Runs \(trusted.yaml:\d+\) cannot be used: it lists runs`
}

// @Requires f != nil
// @Ensures True
func NoEntry(f foreignlib.Unread) (y int) {
	return f(1) // want `cannot verify NoEntry: f has type foreignlib.Unread, which has no contract; declare a named function type with a contract and use it here; for a type of another module, give it an entry foreignlib.Unread in vego-trusted.yaml`
}

// @Requires b != nil
// @Ensures True
func NoMethodEntry(b foreignlib.Bare) (n int) {
	return b.Get() // want `cannot verify NoMethodEntry: b.Get calls Bare.Get, which has no contract; .* for a type of another module, give it an entry \(foreignlib.Bare\).Get in vego-trusted.yaml`
}

// Local is a function type of this module.
type Local func()

// @Requires l != nil
// @Ensures True
func CallsLocal(l Local) {
	l() // want `the trusted contract of foreign.Local \(trusted.yaml:\d+\) cannot be used: the function type foreign.Local is declared in the module of this package`
}

// An interface literal that embeds a declared interface is not modelled.
//
// @Ensures True
func Literal(s interface{ foreignlib.Sink }) (n int) { // want `cannot verify Literal: parameter s has unsupported type interface\{foreignlib.Sink\}`
	return 0
}

// MySink has Put from Sink, and so its entry.
type MySink interface {
	foreignlib.Sink
}

// @Requires s != nil
// @Ensures err = nil -> 0 <= y <= 2
func PutMine(s MySink) (y int, err error) {
	return s.Put(1)
}

// @Requires a != nil And c != nil
// @Ensures err = nil -> 0 <= y <= 4
func PutAliasAndCopy(a foreignlib.SinkAlias, c foreignlib.SinkCopy) (y int, err error) {
	y, err = a.Put(1)
	if err != nil {
		return 0, err
	}
	z, err := c.Put(1)
	if err != nil {
		return 0, err
	}
	return y + z, nil
}

// @Requires g != nil
// @Ensures True
func GetsAnnotated(g foreignannotated.Getter) (n int) {
	return g.Get() // want `the contract of Getter.Get cannot be used: it has a contract where it is declared and also an entry \(foreignannotated.Getter\).Get in the trust file`
}
