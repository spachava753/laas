// Package stdtypes calls through values of types of the standard library
// under the entries vego ships for them.
package stdtypes

import (
	"context"
	"errors"
	"fmt"
	"io"
	"time"
)

// @Requires w != nil
// @Ensures err = nil -> n = |b|
func Save(w io.Writer, b []byte) (n int, err error) {
	return w.Write(b)
}

// Without looking at the error, nothing says that all of b was written.
//
// @Requires w != nil
// @Ensures n = |b|
func SaveAll(w io.Writer, b []byte) (n int) {
	n, _ = w.Write(b)
	return n // want `postcondition may not hold: n = |b|`
}

// The shipped entry of Write does not vouch for its errors.
//
// @Requires w != nil
// @Ensures True
func SaveWrapped(w io.Writer, b []byte) (err error) {
	if _, err := w.Write(b); err != nil {
		return fmt.Errorf("save: %w", err) // want `cannot verify SaveWrapped: formatting err would run the methods of an error whose origin is not known`
	}
	return nil
}

// @Requires r != nil And |buf| > 0
// @Modifies buf
// @Ensures 0 <= |got| <= |buf|
func ReadSome(r io.Reader, buf []byte) (got []byte, err error) {
	n, err := r.Read(buf)
	return buf[:n], err
}

// @Requires r != nil And |buf| > 0
// @Modifies buf
// @Ensures 0 <= n <= |buf|
func ReadPlain(r io.Reader, buf []byte) (n int, err error) {
	return r.Read(buf)
}

// @Requires r != nil
// @Ensures True
func ReadEmpty(r io.Reader) (n int) {
	var buf []byte
	n, _ = r.Read(buf) // want `precondition of r.Read may not hold: |p| > 0`
	return n
}

// The entry of Err vouches for its errors, which are Canceled and
// DeadlineExceeded.
//
// @Requires ctx != nil
// @Ensures err = nil Or err = context.Canceled Or err = context.DeadlineExceeded
func Check(ctx context.Context) (err error) {
	return ctx.Err()
}

// @Requires ctx != nil
// @Ensures True
func CheckWrapped(ctx context.Context) (err error) {
	if err := ctx.Err(); err != nil {
		return fmt.Errorf("check: %w", err)
	}
	return nil
}

// @Requires ctx != nil
// @Ensures canceled -> err != nil
func Canceled(ctx context.Context) (canceled bool, err error) {
	err = ctx.Err()
	return errors.Is(err, context.Canceled), err
}

// @Requires ctx != nil
// @Ensures True
func CheckNil(ctx context.Context) (err error) {
	return ctx.Err()
}

// @Ensures True
func CheckMaybeNil(ctx context.Context) (err error) {
	return ctx.Err() // want `the interface value ctx may be nil`
}

// @Requires ctx != nil And cancel != nil And w != nil
// @Ensures True
func Work(ctx context.Context, cancel context.CancelFunc, w io.Writer) (err error) {
	defer cancel()
	if err := ctx.Err(); err != nil {
		return fmt.Errorf("work: %w", err)
	}
	_, err = w.Write([]byte("done"))
	return err
}

// @Ensures True
func WorkMaybeNil(cancel context.CancelFunc) {
	defer cancel() // want `the function value cancel may be nil`
}

// discard writes nothing anywhere.
type discard struct{}

// @Ensures n = |p| And err = nil
func (discard) Write(p []byte) (n int, err error) {
	return len(p), nil
}

// @Ensures w != nil
func Discard() (w io.Writer) {
	return discard{}
}

// short reports a short write without an error.
type short struct{}

// @Ensures n = 0 And err = nil
func (short) Write(p []byte) (n int, err error) {
	return 0, nil
}

// @Ensures w != nil
func Short() (w io.Writer) {
	return short{} // want `postcondition may not hold: n < |p| -> err != nil, in short.Write used as a method of io.Writer`
}

// scribble writes the slice it is given, which Write must not.
type scribble struct{}

// @Modifies p
// @Ensures n = |p| And err = nil
func (scribble) Write(p []byte) (n int, err error) {
	if len(p) > 0 {
		p[0] = 0
	}
	return len(p), nil
}

// @Ensures w != nil
func Scribble() (w io.Writer) {
	return scribble{} // want `Write may modify p, which Writer.Write may not modify; the entry \(io.Writer\).Write in the trust file does not list it, so code that writes it cannot be used there`
}

// @Ensures c != nil
func NoCancel() (c context.CancelFunc) {
	return func() {}
}

// Done, Deadline, and Value of Context have no entry, so verified code
// cannot make a Context.
type background struct{}

// @Ensures err = nil
func (background) Err() (err error) { return nil }

func (background) Done() <-chan struct{} { return nil }

func (background) Deadline() (deadline time.Time, ok bool) { return time.Time{}, false }

func (background) Value(key any) any { return nil }

// @Ensures c != nil
func Background() (c context.Context) {
	return background{} // want `cannot verify Background: converting a stdtypes.background to context.Context is not supported: its method Context.Deadline has no contract, so nothing would say what code that calls it may rely on; for a type of another module, give it an entry \(context.Context\).Deadline in vego-trusted.yaml`
}
