package foreign

import (
	"errors"

	"foreignlib"
)

// Doubler meets the contract of Sink.Put.
type Doubler struct{}

// @Requires 0 <= x <= 100
// @Ensures 0 <= y <= 2 * x And err = nil
func (Doubler) Put(x int) (y int, err error) {
	return 2 * x, nil
}

// @Ensures s != nil
func NewDoubler() (s foreignlib.Sink) {
	return Doubler{}
}

// Tripler does not.
type Tripler struct{}

// @Requires 0 <= x <= 100
// @Ensures y = 3 * x And err = nil
func (Tripler) Put(x int) (y int, err error) {
	return 3 * x, nil
}

// @Ensures s != nil
func NewTripler() (s foreignlib.Sink) {
	return Tripler{} // want `postcondition may not hold: err = nil -> \(0 <= y And y <= 2 \* x\), in Tripler.Put used as a method of foreignlib.Sink at conversions.go:\d+:\d+`
}

// Counter writes behind its receiver.
type Counter struct {
	n int
}

// @Requires c != nil And 0 <= x <= 100
// @Modifies c
// @Ensures y = 0 And err = nil
func (c *Counter) Put(x int) (y int, err error) {
	if c.n < 1000 {
		c.n++
	}
	return 0, nil
}

// @Requires c != nil
// @Ensures s != nil
func Counting(c *Counter) (s foreignlib.Sink) {
	return c // want `Put may modify c, which Sink.Put may not modify; Sink.Put can list only what its parameters refer to, so a method that writes what its receiver refers to cannot be used as a method of foreignlib.Sink yet, in \(\*Counter\).Put used as a method of foreignlib.Sink`
}

// Sized is a store.
type Sized struct{}

// @Requires 0 <= x <= 100
// @Ensures y = x And err = nil
func (Sized) Put(x int) (y int, err error) {
	return x, nil
}

// @Ensures n = 1
func (Sized) Size() (n int) {
	return 1
}

// @Ensures st != nil
func NewStore() (st foreignlib.Store) {
	return Sized{}
}

// @Ensures m != nil
func Doubling() (m foreignlib.Mapper) {
	return func(x int) int { return 2 * x }
}

// @Ensures m != nil
func Same() (m foreignlib.Mapper) {
	return func(x int) int { return x } // want `postcondition may not hold: y = 2 \* x, in the function literal used as a value of type Mapper at conversions.go:\d+:\d+`
}

// @Ensures h != nil
func Nothing() (h foreignlib.Hook) {
	return func() {}
}

// @Requires b != nil
// @Modifies b
// @Ensures h != nil
func Writes(b *Box) (h foreignlib.Hook) {
	return func() { b.N = 1 } // want `b.N is assigned, which Hook may not modify`
}

// ErrFull is an error of this package with the name of foreignlib's.
var ErrFull = errors.New("mine")

// The contract of Fails names ErrFull of foreignlib, where it is written.
//
// @Ensures f != nil
func FailsRight() (f foreignlib.Fails) {
	return func() error { return foreignlib.ErrFull }
}

// @Ensures f != nil
func FailsWrong() (f foreignlib.Fails) {
	return func() error { return ErrFull } // want `postcondition may not hold: err = nil Or err = ErrFull, in the function literal used as a value of type Fails at conversions.go:\d+:\d+`
}

// @Requires c != nil
// @Ensures True
func NoBareEntry(c foreignlib.Ctx) (b foreignlib.Bare) {
	return nil
}
