// Package foreignlib stands for a package of another module, which vego
// does not annotate: its own go.mod puts it in a module of its own. The
// trust file of the tests gives contracts to its types.
package foreignlib

import "errors"

// ErrFull is what a full sink returns.
var ErrFull = errors.New("full")

// Sink takes numbers.
type Sink interface {
	Put(x int) (y int, err error)
}

// Store is a sink with a size.
type Store interface {
	Sink
	Size() (n int)
}

// SinkAlias is another name for Sink.
type SinkAlias = Sink

// SinkCopy is defined from Sink, and has its method.
type SinkCopy Sink

// Filler fills a slice.
type Filler interface {
	Fill(p []int)
}

// Ctx has a method with a contract in the trust file and one without.
type Ctx interface {
	Err() error
	Done() <-chan struct{}
}

// Bare has no entry.
type Bare interface {
	Get() (n int)
}

// Gen has type parameters.
type Gen[T any] interface {
	Get() T
}

// Hook is called when something ends.
type Hook func()

// Mapper maps a number.
type Mapper func(x int) (y int)

// Fails returns an error.
type Fails func() (err error)

// Half has an entry that no result meets.
type Half func(x int) (y int)

// Runs has an entry that lists runs.
type Runs func(e error)

// Keeps has an entry that lists keeps.
type Keeps func(e error)

// Unread is a type nothing gives an entry.
type Unread func(x int) (y int)

// Source gives numbers, and fails with errors its entry vouches for.
type Source interface {
	Next() (n int, err error)
}

// Opener opens a sink.
type Opener interface {
	Open() (s Sink)
}

// Done is called with nothing, and fails with an error its entry vouches
// for.
type Done func() (err error)

// Copier copies from a slice.
type Copier interface {
	Copy(p []int) (n int)
}

// Maker makes a value, which its entry says is there.
type Maker interface {
	Make() (x any)
}

// Unmakeable has an entry that no value meets when n is positive.
type Unmakeable interface {
	Make(n int) (x any)
}
