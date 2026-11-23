package handlers

import (
	"fmt"
	"io"
	"net/http"
)

// A ResponseWriter converts to an io.Writer: the contract of its Write
// implies that of io.Writer's, and the value keeps its home (F28).

// Hello formats into the writer of a handler.
//
// @Requires w != nil And |name| <= 100
// @Modifies w
// @Ensures True
func Hello(w http.ResponseWriter, name string) {
	fmt.Fprintf(w, "hello %s\n", name)
}

// Tally is data a helper keeps beside a writer.
type Tally struct{ N int }

// logTo writes through w beside t.
//
// @Requires w != nil And t != nil
// @Modifies w
// @Ensures t.N' = t.N
func logTo(w io.Writer, t *Tally) {
	w.Write([]byte("x"))
}

// Converted writes through the converted value and hands it on beside t,
// which keeps t.
//
// @Requires w != nil And t != nil
// @Modifies w
// @Ensures t.N' = t.N
func Converted(w http.ResponseWriter, t *Tally) {
	var out io.Writer = w
	out.Write([]byte("a"))
	logTo(io.Writer(w), t)
}

// tallyOf is trusted to return a tally of no known origin.
func tallyOf() (t *Tally) { return &Tally{} }

// ConvertedBeside hands it on beside a tally of no known origin.
//
// @Requires w != nil
// @Modifies w
// @Ensures True
func ConvertedBeside(w http.ResponseWriter) {
	t := tallyOf()
	logTo(io.Writer(w), t) // want `the footprint of what is passed to logTo as io.Writer\(w\) may hold memory that what is passed as t reaches`
}

// Keeper holds a writer it should not.
type Keeper2 struct{ out io.Writer }

// KeepConverted stores the converted writer.
//
// @Requires k != nil And w != nil
// @Modifies k
// @Ensures True
func KeepConverted(k *Keeper2, w http.ResponseWriter) {
	var x io.Writer = w
	k.out = x // want `x, which holds w, is or holds a net/http.ResponseWriter, which must not be used after the call that received it returns`
}

// Drainer declares Write and Close of its own, with no state.
type Drainer interface {
	// @Receiver s
	// @Modifies s
	// @Ensures 0 <= n <= |p| And (n < |p| -> err != nil)
	Write(p []byte) (n int, err error)

	// @Ensures True
	Close() (err error)
}

// SinkAsWriteCloser converts it to an interface with the state closed,
// which Drainer does not declare.
//
// @Requires s != nil
// @Ensures True
func SinkAsWriteCloser(s Drainer) {
	var wc io.WriteCloser = s // want `converting s, a Drainer, to io.WriteCloser is not supported: io.WriteCloser has the state closed, which Drainer does not declare`
	_ = wc
}

// SinkAsWriter converts it to io.Writer: a method of an interface of the
// project may keep what it is handed, and io.Writer's Write keeps nothing.
//
// @Requires s != nil
// @Ensures True
func SinkAsWriter(s Drainer) {
	var w io.Writer = s // want `converting s, a Drainer, to io.Writer is not supported: Drainer.Write may keep what it is handed as its parameter 1, and Writer.Write keeps nothing there`
	_ = w
}

// Loose says less than io.Writer's Write.
type Loose interface {
	// @Receiver l
	// @Modifies l
	// @Ensures True
	Write(p []byte) (n int, err error)
}

// LooseAsWriter converts a value whose Write says nothing of the count to
// io.Writer.
//
// @Requires l != nil
// @Ensures True
func LooseAsWriter(l Loose) {
	var w io.Writer = l // want `cannot verify LooseAsWriter: converting l, a Loose, to io.Writer is not supported: Loose.Write may keep what it is handed`
	_ = w
}

// Vouching vouches for the errors of its Load, and Plain does not.
type Vouching interface {
	// @Ensures True
	// @Vouches err
	Load() (err error)
}

type Plain interface {
	// @Ensures True
	Load() (err error)
}

// PlainAsVouching converts a value that vouches for nothing to one that
// vouches.
//
// @Requires p != nil
// @Ensures True
func PlainAsVouching(p Plain) {
	var v Vouching = p // want `converting p, a Plain, to Vouching is not supported: Vouching.Load vouches for the errors of its result 1, and Plain.Load does not`
	_ = v
}

// Putter writes behind its receiver, and Peeker does not.
type Putter interface {
	// @Receiver p
	// @Modifies p
	// @Ensures True
	Put()
}

type Peeker interface {
	// @Ensures True
	Put()
}

// PutterAsPeeker converts a value whose Put writes behind it to one whose
// Put writes nothing.
//
// @Requires p != nil
// @Ensures True
func PutterAsPeeker(p Putter) {
	var q Peeker = p // want `converting p to the interface of Peeker.Put is not supported: the contract of Putter.Put names its receiver, and that of Peeker.Put does not`
	_ = q
}

// Wide asks more than Narrow of its argument.
type Wide interface {
	// @Requires n > 0
	// @Ensures r = n
	Get(n int) (r int)
}

type Narrow interface {
	// @Ensures r = n
	Get(n int) (r int)
}

// Weak says less than Narrow of its result.
type Weak interface {
	// @Ensures r >= 0
	Get(n int) (r int)
}

// WideAsNarrow converts a value with a stronger requires.
//
// @Requires x != nil
// @Ensures True
func WideAsNarrow(x Wide) {
	var y Narrow = x // want `precondition of x.Get may not hold: n > 0, in Wide.Get used as Narrow.Get at convert.go:\d+:\d+`
	_ = y
}

// WeakAsNarrow converts a value with a weaker ensures.
//
// @Requires x != nil
// @Ensures True
func WeakAsNarrow(x Weak) {
	var y Narrow = x // want `postcondition may not hold: r = n, in Weak.Get used as Narrow.Get at convert.go:\d+:\d+`
	_ = y
}

// NarrowAsWeak converts a value with a stronger ensures, which implies the
// weaker one when n is not negative: it is refused, since n may be.
//
// @Requires x != nil
// @Ensures True
func NarrowAsWeak(x Narrow) {
	var y Weak = x // want `postcondition may not hold: r >= 0, in Narrow.Get used as Weak.Get at convert.go:\d+:\d+`
	_ = y
}

// Exact says r = n for every n, which implies Weak's for n >= 0 only.
type Exact interface {
	// @Requires n >= 0
	// @Ensures r = n
	Get(n int) (r int)
}

// Natural asks n >= 0 too, and says r >= 0.
type Natural interface {
	// @Requires n >= 0
	// @Ensures r >= 0
	Get(n int) (r int)
}

// ExactAsNatural converts a value whose contract implies the target's.
//
// @Requires x != nil
// @Ensures True
func ExactAsNatural(x Exact) {
	var y Natural = x
	_ = y
}

// Gate has a state, and its Use changes it only.
//
// @State used
type Gate interface {
	// @Receiver g
	// @Modifies g
	// @Ensures used(g')
	Use()
}

// User has no state, and its Use writes behind its receiver.
type User interface {
	// @Receiver u
	// @Modifies u
	// @Ensures True
	Use()
}

// GateAsUser converts a value whose Use changes a state to one whose Use
// writes its footprint and keeps the states: calls through User would
// change the state unseen.
//
// @Requires g != nil
// @Ensures True
func GateAsUser(g Gate) {
	var u User = g // want `g.Use may modify the states of g, which User.Use may not modify; the contract of User.Use does not list it, so code that writes it cannot be used there, in Gate.Use used as User.Use at convert.go:\d+:\d+`
	_ = u
}

// ThroughUnlisted writes through a local that holds the converted writer.
//
// @Requires w != nil
// @Ensures True
func ThroughUnlisted(w http.ResponseWriter) {
	out := io.Writer(w)
	out.Write([]byte("x")) // want `out.Write may modify the footprint of out, which ThroughUnlisted may not modify; out holds w, converted at convert.go:\d+:\d+; list w in a // @Modifies clause`
}

// HeaderBeside hands the header beside the converted writer.
//
// @Requires w != nil
// @Modifies w
// @Ensures True
func HeaderBeside(w http.ResponseWriter) {
	h := w.Header()
	headerTo(io.Writer(w), h) // want `it comes from the call of w.Header at convert.go:\d+:\d+, whose contract places it within w, which may hold memory a writer writes`
}

// headerTo writes through w beside a header.
//
// @Requires w != nil
// @Modifies w
// @Ensures True
func headerTo(w io.Writer, h http.Header) {
	w.Write([]byte("h"))
}

// RC is a closer whose own Read lists r only, which on an interface with
// states covers the states.
type RC interface {
	io.Closer

	// @Receiver r
	// @Requires |p| > 0
	// @Modifies r, p
	// @Ensures 0 <= n <= |p|
	Read(p []byte) (n int, err error)
}

// AsRC converts a reader whose Read writes behind it to RC.
//
// @Requires rc != nil
// @Ensures True
func AsRC(rc io.ReadCloser) {
	var r RC = rc // want `the contract of RC.Read lists r, which on an interface with states covers its states only; list behind\(r\) too to let the method write behind its receiver`
	_ = r
}
