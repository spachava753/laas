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
