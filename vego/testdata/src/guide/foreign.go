package guide

import (
	"bufio"
	"context"
	"errors"
	"fmt"
	"io"
)

// The programs of the section on interfaces and function types of other
// packages. The trust file of the tests gives (io.Reader).Read the entry
// that vouches for its errors, which the section shows, and
// (*bufio.Scanner).Scan an entry.

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

// @Requires w != nil
// @Ensures True
func Save(w io.Writer, b []byte) (err error) {
	if _, err := w.Write(b); err != nil {
		return fmt.Errorf("save: %w", err) // want `cannot verify Save: formatting err would run the methods of an error whose origin is not known`
	}
	return nil
}

// @Requires r != nil And |buf| > 0
// @Modifies buf
// @Ensures err = nil -> 0 <= n <= |buf|
func Load(r io.Reader, buf []byte) (n int, err error) {
	n, err = r.Read(buf)
	if err != nil {
		return 0, fmt.Errorf("load: %w", err)
	}
	return n, nil
}

// ErrLong is what a reader returns for a slice it will not fill.
var ErrLong = errors.New("too long")

// zeros reads zeros.
type zeros struct{}

// @Requires |p| > 0
// @Modifies p
// @Ensures n = |p| And err = nil
func (zeros) Read(p []byte) (n int, err error) {
	// @Invariant 0 <= i <= |p|
	for i := range p {
		p[i] = 0
	}
	return len(p), nil
}

// @Ensures r != nil
func Zeros() (r io.Reader) {
	return zeros{}
}

// wrapping wraps the error it returns.
type wrapping struct{}

// @Requires |p| > 0
// @Ensures (err = nil <-> |p| <= 4096) And n = 0
func (wrapping) Read(p []byte) (n int, err error) {
	if len(p) > 4096 {
		return 0, fmt.Errorf("read: %w", ErrLong)
	}
	return 0, nil
}

// @Ensures r != nil
func Wrapping() (r io.Reader) {
	return wrapping{}
}

// @Requires s != nil And 0 <= n <= 1000
// @Modifies s
// @Ensures 0 <= lines <= n
func CountLines(s *bufio.Scanner, n int) (lines int) {
	// @Invariant 0 <= lines <= n
	// @Variant n - lines
	for lines < n && s.Scan() {
		lines++
	}
	return lines
}

// Record holds a writer, which verified code does not call.
type Record struct {
	N int
	W io.Writer
}

func logRecord(r Record) {}

// Sink takes a number.
//
// @Ensures True
type Sink func(x int)

// @Ensures True
func logNumber(x int) {
	var r Record
	r.N = x
	logRecord(r)
}

// @Ensures s != nil
func MakeSink() (s Sink) {
	return logNumber // want `cannot verify MakeSink: logNumber may call through a function value or an interface value, and code that a function value runs cannot do that yet: no contract of a function type or of a method of an interface has a variant, so nothing would prove that such calls end; logNumber calls logRecord, which is trusted and runs what r holds, which can be a value of io.Writer, whose methods all have contracts, so that verified code can make one. Make the value in code that is not verified, or keep that call out of what logNumber runs`
}

// fresh makes the error it returns with errors.New, which calls nothing.
type fresh struct{}

// @Requires |p| > 0
// @Ensures (err = nil <-> |p| <= 4096) And n = 0
func (fresh) Read(p []byte) (n int, err error) {
	if len(p) > 4096 {
		return 0, errors.New("too long")
	}
	return 0, nil
}

// @Ensures r != nil
func Fresh() (r io.Reader) {
	return fresh{}
}
