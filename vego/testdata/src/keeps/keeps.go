// Package keeps holds verified code that hands values to trusted functions
// that keep them, and what is refused when an entry for such a function
// cannot be true or would leave a later run unseen.
package keeps

import (
	"errors"
	"io"

	"keepslib"
)

// show takes a number that is not negative.
//
// @Requires n >= 0
// @Ensures True
func show(n int) {}

// Registers keeps a handler in a registry it is handed and fires it. What
// Fire runs was kept by Add, and Fire's runs carries the claim.
//
// @Requires reg != nil
// @Modifies reg
// @Ensures True
func Registers(reg *keepslib.Registry) {
	reg.Add(show)
	reg.Add(func(n int) { show(n) })
	reg.Fire(3)
}

// FiresNegative fires a handler with a number its contract does not allow.
//
// @Requires reg != nil
// @Ensures True
func FiresNegative(reg *keepslib.Registry) {
	reg.Fire(-1) // want `vego: precondition of Fire may not hold: n >= 0`
}

// Zeros reads zeros.
type Zeros struct{}

// Read fills one byte of p with a zero.
//
// @Requires |p| > 0
// @Modifies p
// @Ensures 0 <= n And n <= |p| And err = nil
func (Zeros) Read(p []byte) (n int, err error) {
	p[0] = 0
	return 1, nil
}

// Boxes keeps a reader that verified code made in a box and reads through
// the box.
//
// @Ensures 0 <= n And n <= 8
func Boxes() (n int) {
	b := keepslib.Wrap(Zeros{})
	buf := make([]byte, 8)
	return b.Fill(buf)
}

// BoxesGiven keeps a reader it is given.
//
// @Requires r != nil
// @Modifies r
// @Ensures 0 <= n And n <= 1
func BoxesGiven(r io.Reader) (n int) {
	b := keepslib.Wrap(r)
	return b.Fill(make([]byte, 1))
}

// FillsEmpty reads into an empty slice through the box.
//
// @Requires r != nil
// @Ensures True
func FillsEmpty(r io.Reader) {
	b := keepslib.Wrap(r)
	_ = b.Fill(nil) // want `vego: precondition of Fill may not hold: \|p\| > 0`
}

// ReadsClosing reads through a new closer, whose error nothing predicts, so
// it cannot promise success. A sample of the always-fails check gives every
// reference that is not the input's the home of one that is, which
// contradicted the fresh home of what Closing returns, so the check found
// no input that reaches the read and reported that the contract requires
// success for no input.
//
// @Requires r != nil
// @Modifies r
// @Ensures True
func ReadsClosing(r io.Reader) (err error) {
	rc := keepslib.Closing(r)
	_, err = rc.Read(make([]byte, 4))
	return err
}

// AlwaysFails reads through a new closer and fails whatever the read did,
// so its failure depends on no call, and the check reports it.
//
// @Requires r != nil
// @Modifies r
// @Ensures True
func AlwaysFails(r io.Reader) (err error) { // want `vego: the contract of AlwaysFails may also be met by a function that always returns an error`
	rc := keepslib.Closing(r)
	_, _ = rc.Read(make([]byte, 4))
	return errors.New("x")
}

// FailsAfterRead fails on both branches after the read.
//
// @Requires r != nil
// @Modifies r
// @Ensures True
func FailsAfterRead(r io.Reader) (err error) { // want `vego: the contract of FailsAfterRead may also be met by a function that always returns an error`
	rc := keepslib.Closing(r)
	if _, e := rc.Read(make([]byte, 4)); e != nil {
		return errors.New("read")
	}
	return errors.New("always")
}
