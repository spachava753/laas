package trialfaults

import "io"

// An interface method's contract is one that some outcome meets, also when
// the result is an interface value: the outcome chooses the value, nil or a
// new one.

// Source hands out values.
type Source interface {
	// @Ensures True
	Next() (x any)
}

// Some hands out values that are there.
type Some interface {
	// @Ensures x != nil
	Next() (x any)
}

// Opener gives a source when it succeeds.
type Opener interface {
	// @Ensures err = nil -> s != nil
	// @Ensures err != nil -> s = nil
	Open() (s Source, err error)
}

// Empty hands out nothing.
type Empty interface {
	// @Ensures x = nil
	Next() (x any)
}

// Pair holds an interface value.
type Pair struct {
	Src Source
	N   int
}

// Pairer makes pairs.
type Pairer interface {
	// @Ensures p.Src != nil And p.N = 1
	Pair() (p Pair)
}

// Factory makes a closer.
//
// @Ensures c != nil
type Factory func() (c io.Closer)

// Twice gives two values that are there.
type Twice interface {
	// @Ensures a != nil And b != nil
	Two() (a, b any)
}

// None promises what no value is.
type None interface {
	// @Ensures x = nil And x != nil
	Next() (x any) // want `the contract of None.Next contradicts itself`
}

// Sometimes promises what no value is when n is positive.
type Sometimes interface {
	// @Ensures n > 0 -> (x = nil And x != nil)
	Next(n int) (x any) // want `the Ensures clauses of Sometimes.Next are not proved to be satisfiable`
}

// Shut promises a state and its opposite when n is positive.
type Shut interface {
	// @Ensures n > 0 -> (c != nil And closed(c) And ~closed(c))
	Open(n int) (c io.Closer) // want `the Ensures clauses of Shut.Open are not proved to be satisfiable`
}

// NoMaker promises an interface value and none when n is positive.
//
// @Ensures n > 0 -> (c != nil And c = nil)
type NoMaker func(n int) (c io.Closer) // want `the Ensures clauses of NoMaker are not proved to be satisfiable`

// A new interface value has a home of its own, so fresh can be met.
type Fresh interface {
	// @Ensures fresh(y)
	New() (y io.Closer)
}

// FreshThere is fresh and not nil.
type FreshThere interface {
	// @Ensures y != nil And fresh(y)
	New() (y io.Closer)
}

// FreshTwo gives two new values.
type FreshTwo interface {
	// @Ensures a != nil And b != nil And fresh(a) And fresh(b)
	Two() (a io.Closer, b io.Closer)
}

// FreshOwn gives a new value of an interface of the package.
type FreshOwn interface {
	// @Ensures y != nil And fresh(y)
	New() (y Source)
}

// FreshMaker is a function type whose result is new.
//
// @Ensures y != nil And fresh(y)
type FreshMaker func() (y Source)

// A state of a new value lies in memory the call creates, which an outcome
// does not choose, so a promise about it is not proved to be met.
type FreshClosed interface {
	// @Ensures y != nil And fresh(y) And closed(y)
	New() (y io.Closer) // want `the Ensures clauses of FreshClosed.New are not proved to be satisfiable`
}

// Passes may return the value it is given, which is open.
type Passes interface {
	// @Requires x != nil And ~closed(x)
	// @Ensures y != nil And ~closed(y)
	Pass(x io.Closer) (y io.Closer)
}

// Picks may return one of the values it is given, which are all open. That
// is true, and it is not proved: the search for an outcome tries the
// values whose homes the entry reads outside a quantifier, and a home of
// its own, whose state is not chosen.
type Picks interface {
	// @Requires |xs| > 0 And (Forall i in [0, |xs|) : xs[i] != nil And ~closed(xs[i]))
	// @Ensures y != nil And ~closed(y)
	Pick(xs []io.Closer) (y io.Closer) // want `the Ensures clauses of Picks.Pick are not proved to be satisfiable`
}

// PicksFromNone may be given none, and then only a new value is left,
// whose state is not chosen.
type PicksFromNone interface {
	// @Requires Forall i in [0, |xs|) : xs[i] != nil And ~closed(xs[i])
	// @Ensures y != nil And ~closed(y)
	Pick(xs []io.Closer) (y io.Closer) // want `the Ensures clauses of PicksFromNone.Pick are not proved to be satisfiable`
}

// KeepsOpen returns a new value and says that what it is given stays open.
type KeepsOpen interface {
	// @Requires Forall i in [0, |xs|) : xs[i] != nil And ~closed(xs[i])
	// @Ensures y != nil And fresh(y) And (Forall i in [0, |xs|) : ~closed(xs[i]))
	Pick(xs []io.Closer) (y io.Closer)
}

// Closes promises that what it is given is closed afterwards, which it may
// not change.
type Closes interface {
	// @Requires Forall i in [0, |xs|) : xs[i] != nil And ~closed(xs[i])
	// @Ensures y != nil And fresh(y) And (Forall i in [0, |xs|) : closed(xs[i]))
	Pick(xs []io.Closer) (y io.Closer) // want `the Ensures clauses of Closes.Pick are not proved to be satisfiable`
}
