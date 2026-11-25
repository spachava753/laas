package optional

import (
	"fmt"
	"io"

	"optionala"
	"optionalc"
	"optionalsink"
	"optionalwc"
)

// FromSink takes a value out of a Sink of a package whose build lacks io,
// which nothing checked against io.Writer (F1 of the design review).
//
// @Ensures n >= 0
func FromSink() (n int) {
	s := optionala.Make()
	if w, ok := s.(io.Writer); ok { // want `cannot verify FromSink: using the value of s.\(io.Writer\) is not supported`
		n, _ = w.Write([]byte("x"))
	}
	return n
}

// neg is a writer whose Write breaks the entry of io.Writer.
type neg struct{}

func (neg) Write(p []byte) (int, error) { return -1, nil }

// getAny is trusted; its entry vouches for nothing, which a result of
// type any does not need.
func getAny(w io.Writer) any { return neg{} }

// FromAny takes a writer out of what a trusted function returns as an any
// (F2 of the design review): any is not O-typed, so R2 stands.
//
// @Requires w != nil
// @Modifies w
// @Ensures n >= 0
func FromAny(w io.Writer) (n int) {
	x := getAny(w)
	if v, ok := x.(io.Writer); ok { // want `cannot verify FromAny: using the value of x.\(io.Writer\) is not supported`
		n, _ = v.Write([]byte("x"))
	}
	return n
}

// negErr is an error whose Size breaks the entry of optionalc.Sizer.
type negErr struct{}

func (negErr) Error() string  { return "neg" }
func (negErr) String() string { return "neg" }
func (negErr) Size() int      { return -1 }

// getErr and getVouched are trusted.
func getErr() error     { return negErr{} }
func getVouched() error { return negErr{} }

// ErrDirect asserts the error itself (AC).
//
// @Ensures n >= 0
func ErrDirect() (n int) {
	if s, ok := getErr().(optionalc.Sizer); ok { // want `cannot verify ErrDirect: using the value of getErr\(\).\(optionalc.Sizer\) is not supported: the method Size of optionalc.Sizer has a contract`
		n = s.Size()
	}
	return n
}

// ErrThroughAny converts the error to any first (F6 of the design review).
//
// @Ensures n >= 0
func ErrThroughAny() (n int) {
	var a any = getErr()
	if s, ok := a.(optionalc.Sizer); ok { // want `cannot verify ErrThroughAny: using the value of a.\(optionalc.Sizer\) is not supported`
		n = s.Size()
	}
	return n
}

// VouchedThroughAny does it with an error its entry vouches for.
//
// @Ensures n >= 0
func VouchedThroughAny() (n int) {
	var a any = getVouched()
	if s, ok := a.(optionalc.Sizer); ok { // want `cannot verify VouchedThroughAny: using the value of a.\(optionalc.Sizer\) is not supported`
		n = s.Size()
	}
	return n
}

// ErrThroughStringer asserts the error to fmt.Stringer, which AC allows,
// and then to Sizer: fmt.Stringer is not O-typed (the orchestrator's case).
//
// @Ensures n >= 0
func ErrThroughStringer() (n int) {
	st, ok := getErr().(fmt.Stringer)
	if !ok {
		return 0
	}
	if s, ok := st.(optionalc.Sizer); ok { // want `cannot verify ErrThroughStringer: using the value of st.\(optionalc.Sizer\) is not supported`
		n = s.Size()
	}
	return n
}

// T meets io.Writer's entry in Write, and its WriteString does not meet
// io.StringWriter's.
type T struct{}

// @Ensures n = |p| And err = nil
func (T) Write(p []byte) (n int, err error) { return len(p), nil }

// @Ensures n = -1 And err = nil
func (T) WriteString(s string) (n int, err error) { return -1, nil }

// @Ensures err = nil
func (T) Close() (err error) { return nil }

// Through converts a T to a Sink of a package whose build lacks io, so it
// is not checked against io.StringWriter, and the Sink to io.Writer by
// contract (F7 of the review of the design).
//
// @Ensures w != nil
func Through() (w io.Writer) {
	var s optionalsink.Sink = T{}
	w = s // want `cannot verify Through: converting s, an optionalsink.Sink, to io.Writer is not supported: code given an io.Writer may assert it to io.Reader, whose package is not in the build of the package that declares optionalsink.Sink`
	return w
}

// SinkAsserted takes the same way by an assertion under R2's base rule.
//
// @Requires s != nil
// @Ensures True
func SinkAsserted(s optionalsink.Sink) (n int) {
	if w, ok := s.(io.Writer); ok { // want `cannot verify SinkAsserted: using the value of s.\(io.Writer\) is not supported: code given an io.Writer may assert it to io.Reader`
		n, _ = w.Write([]byte("x"))
	}
	return n
}

// badWriteErr is an error of the project whose Write breaks the entry.
type badWriteErr struct{}

// @Ensures True
func (badWriteErr) Error() (s string) { return "bad" }

// @Ensures n = -1 And err = nil
func (badWriteErr) Write(p []byte) (n int, err error) { return -1, nil }

// ErrorAsWriter converts the error to error, which is not checked, then
// to any and asserts io.Writer: R2 stands (F5 of the review of the
// design).
//
// @Ensures n >= 0
func ErrorAsWriter() (n int) {
	var e error = badWriteErr{}
	var a any = e
	if w, ok := a.(io.Writer); ok { // want `cannot verify ErrorAsWriter: using the value of a.\(io.Writer\) is not supported`
		n, _ = w.Write([]byte("x"))
	}
	return n
}

// ES has the methods of error and of io.Writer, with no contracts: AC lets
// an error be asserted to it, and it is O-shaped and not O-typed (F14 of
// the review of S1).
type ES interface {
	Error() string
	Write(p []byte) (n int, err error)
}

// W has io.Writer's method with no contract, so a trusted result of it
// needs no vouches.
type W interface {
	Write(p []byte) (n int, err error)
}

// badErr is an error of the project whose Size breaks the entry of
// optionalc.Sizer.
type badErr struct{}

// @Ensures s = "bad"
func (badErr) Error() (s string) { return "bad" }

// @Ensures n = |p| And err = nil
func (badErr) Write(p []byte) (n int, err error) { return len(p), nil }

// @Ensures n = -1
func (badErr) Size() (n int) { return -1 }

// getW and getWOver are trusted.
func getW() W                { return badErr{} }
func getWOver(x io.Writer) W { return negString{} }

// negString's WriteString breaks the entry of io.StringWriter.
type negString struct{}

func (negString) Write(p []byte) (int, error)       { return len(p), nil }
func (negString) WriteString(s string) (int, error) { return -1, nil }

// ViaError asserts an error to ES and ES to a Sizer.
//
// @Ensures n >= 0
func ViaError() (n int) {
	var e error = badErr{}
	if es, ok := e.(ES); ok {
		if s, ok := es.(optionalc.Sizer); ok { // want `cannot verify ViaError: using the value of es.\(optionalc.Sizer\) is not supported`
			n = s.Size()
		}
	}
	return n
}

// ViaTrusted asserts a trusted result of W to a Sizer.
//
// @Ensures n >= 0
func ViaTrusted() (n int) {
	if s, ok := getW().(optionalc.Sizer); ok { // want `cannot verify ViaTrusted: using the value of getW\(\).\(optionalc.Sizer\) is not supported`
		n = s.Size()
	}
	return n
}

// ViaTrustedOver asserts a trusted result of W made over x to
// io.StringWriter.
//
// @Requires x != nil
// @Modifies x
// @Ensures n >= 0
func ViaTrustedOver(x io.Writer) (n int) {
	if sw, ok := getWOver(x).(io.StringWriter); ok { // want `cannot verify ViaTrustedOver: using the value of getWOver\(x\).\(io.StringWriter\) is not supported`
		n, _ = sw.WriteString("abc")
	}
	return n
}

// WCAsWriter converts a value to a WC, which has states and so is no
// interface of O, and the WC to io.Writer, which the branch for a source
// with states took before F17.
//
// @Ensures n >= 0
func WCAsWriter() (n int) {
	var wc optionalwc.WC = T{}
	var w io.Writer = wc // want `cannot verify WCAsWriter: converting wc, an optionalwc.WC, to io.Writer is not supported`
	if sw, ok := w.(io.StringWriter); ok {
		n, _ = sw.WriteString("x")
	}
	return n
}

// LooseW has io.Writer's method under a contract of its own that says
// nothing of n, so it is O-typed by contract only if that contract implied
// the entry of (io.Writer).Write, which it does not.
type LooseW interface {
	// @Receiver w
	// @Modifies w
	// @Ensures True
	Write(p []byte) (n int, err error)
}

// LooseLift asserts a LooseW to io.StringWriter: the lift leans on LooseW
// being O-typed, which the proof of the implication refuses.
//
// @Requires lw != nil
// @Modifies lw
// @Ensures True
func LooseLift(lw LooseW) (n int) {
	if sw, ok := lw.(io.StringWriter); ok { // want `cannot verify LooseLift: lw, a LooseW, is taken to have the methods of io.Writer, which is not supported: LooseW.Write may keep what it is handed`
		n, _ = sw.WriteString("x")
	}
	return n
}
