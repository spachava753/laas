package globals

import (
	"io"
	_ "unsafe"
)

// requests is assigned, so it is not a value fixed for the life of the
// program.
var requests int

// Handle counts requests and is not verified.
func Handle() { requests++ }

// Requests reads a variable that code which is not verified changes, of
// which nothing is known.
//
// @Ensures True
func Requests() (r int) {
	return requests
}

type counter struct{ N int }

func (c *counter) Inc() { c.N++ }

// counted has its address taken by a method value, with no call and no &.
var counted counter

var inc = counted.Inc

// Count would be 0 if nothing changed counted, but the method value inc
// may have.
//
// @Ensures r = 0
func Count() (r int) {
	return counted.N // want `vego: postcondition may not hold: r = 0`
}

// settings has a field assigned.
var settings Config

func configure() { settings.Retries = 3 }

// Settings reads it.
//
// @Ensures True
func Settings() (r int) {
	return settings.Retries
}

// written is written below, so what it refers to is ordinary memory.
var written = []int{1, 2}

// WriteTable writes what a fixed variable refers to, and does not list it.
//
// @Ensures True
func WriteTable() {
	written[0] = 5 // want `^vego: written\[0\] is assigned, which WriteTable may not modify; it is memory that the package-level variable written refers to; list written in a // @Modifies clause$`
}

// WrittenFirst would be 1 if nothing wrote the array.
//
// @Ensures r = 1
func WrittenFirst() (r int) {
	return written[0] // want `vego: postcondition may not hold: r = 1`
}

// removed has a key deleted below.
var removed = map[string]int{"free": 10}

// RemoveLimit deletes a key of a fixed map, and does not list it.
//
// @Ensures True
func RemoveLimit() {
	delete(removed, "free") // want `^vego: removed is modified, which RemoveLimit may not modify; it is memory that the package-level variable removed refers to; list removed in a // @Modifies clause$`
}

// AssignField assigns a part of a variable, and does not list it.
//
// @Ensures True
func AssignField() {
	settings.Timeout = 1 // want `^vego: settings.Timeout is assigned, which AssignField may not modify; list it in a // @Modifies clause$`
}

// hook can hold code.
var hook func()

// Hooked reads it.
//
// @Ensures True
func Hooked() (r bool) {
	return hook == nil // want `vego: cannot verify Hooked: hook has type func\(\), which can hold a function value, an interface value, an error, a channel, or an unsafe.Pointer; package-level variables of such types are not supported yet`
}

// sink holds an interface value behind a pointer.
var sink = &struct{ W io.Writer }{}

// Sink reads it.
//
// @Ensures True
func Sink() (r bool) {
	return sink != nil // want `vego: cannot verify Sink: sink has type \*struct\{W io.Writer\}, which can hold a function value`
}

// buf is an array, which is not modelled.
var buf [4]byte

// Buf reads it.
//
// @Ensures True
func Buf() (r byte) {
	return buf[0] // want `vego: cannot verify Buf: indexing a \[4\]byte is not supported`
}

// linked has no initialiser and nothing assigns it, but a directive gives
// it the storage of another variable.
//
//go:linkname linked globalslib.Limit
var linked int

// Linked would be 0.
//
// @Ensures r = 0
func Linked() (r int) {
	return linked // want `vego: cannot verify Linked: linked is named by a go:linkname directive at defects.go:\d+; a variable that a directive or assembly names is another symbol's storage, which code writes under the other name, so it cannot be verified`
}

// Primed primes a variable that nothing changes.
//
// @Ensures r = defaultTimeout' // want `vego: in Ensures annotation: defaultTimeout is a package-level variable that nothing changes, so it holds the same value on return; drop the prime`
func Primed() (r int) { return defaultTimeout }

// Old puts one in old().
//
// @Ensures True
func Old() (r int) {
	// @Assert old(defaultTimeout) = 30 // want `vego: in Assert annotation: old\(defaultTimeout\): defaultTimeout is not a parameter`
	return 0
}

// TooHigh asks for more than the declaration gives.
//
// @Requires defaultTimeout = 20
// @Ensures True
func TooHigh() (r int) { return 0 } // want `vego: nothing can satisfy the Requires clauses of TooHigh together with what the types of its parameters guarantee, so verifying it would prove nothing`

// pageSize is some number, which nothing checks to be positive.
var pageSize = twice(-1)

// Pages divides by a variable that a Requires assumes positive.
//
// @Requires pageSize > 0 // want `vego: the Requires clause pageSize > 0 reads only package-level variables, and their declarations do not show that it holds; test the value in the body instead`
// @Requires n >= 0
// @Ensures True
func Pages(n int) (r int) { return n / pageSize }

// Mixed relates a parameter to a variable, which callers can meet.
//
// @Requires 0 <= e And e < pageSize
// @Ensures r = e
func Mixed(e int) (r int) { return e }

// first and second point to values of no size, which may share an
// address; nothing is assumed of where they point.
type none struct{}

var first = &none{}
var second = new(none)

// Apart would hold for allocations with a size.
//
// @Ensures r
func Apart() (r bool) {
	return first != second // want `vego: cannot verify Apart: pointers to values of size zero may or may not be equal, so comparing them is not supported`
}

var one = &Config{}
var other = &Config{}

// ApartSized holds: two allocations with a size are apart.
//
// @Ensures r
func ApartSized() (r bool) { return one != other }

// keep and table2 share memory through an initialiser that names keep.
var keep = make([]int, 4)
var table2 = keep

// Probe reads table2 twice around a write through A, which may be the
// same array.
//
// @Requires |A| > 0 And |table2| > 0
// @Modifies A
// @Ensures r
func Probe(A []int) (r bool) {
	s := table2[0]
	A[0] = 7
	return table2[0] == s // want `vego: postcondition may not hold: r`
}

// Run passes the other reference to Probe.
func Run() bool { return Probe(keep) }

// firstEntry has a contract that reads memory through a package-level
// variable, so a call of it cannot be moved across a write. That the table
// is only read does not change this.
//
// @Ensures r = table[0]
func firstEntry() (r int) { return table[0] }

// Beside calls it in the target of an assignment beside an append that
// may write into the array of its slice.
//
// @Requires |u| = 2 And |t| = 1
// @Modifies u, t
func Beside(u [][]int, t []int) {
	u[firstEntry()&1] = append(t[:0], 5) // want `vego: cannot verify Beside: firstEntry is called in the target of this assignment, and Go may call it before or after append writes into the array of t\[:0\]; assign the result of firstEntry to a variable in a statement of its own first`
}

// Weak promises nothing about success.
//
// @Ensures err = nil -> n <= defaultTimeout
func Weak(n int) (err error) { // want `vego: the contract of Weak may also be met by a function that always returns an error: it requires success for no input`
	if n > defaultTimeout {
		return ErrTooBig
	}
	return nil
}

// mutable is changed, and snapshot holds the value it had when snapshot
// was initialised, of which nothing is known.
var mutable = 3

func bumpMutable() { mutable++ }

var snapshot = mutable

// Snapshot would be 3 if mutable kept its value.
//
// @Ensures r = 3
func Snapshot() (r int) {
	return snapshot // want `vego: postcondition may not hold: r = 3`
}

// Scaler has a contract that names a package-level variable.
//
// @Ensures r = defaultTimeout // want `vego: in Ensures annotation: a contract of a function type or of a method of an interface cannot name the package-level variable defaultTimeout yet`
type Scaler func(n int) (r int)

// Window has an invariant that names one.
//
// @Invariant Size <= defaultTimeout // want `an invariant cannot name the package-level variable defaultTimeout yet`
type Window struct {
	Size int
}

// spare has room for more elements than it holds.
var spare = make([]int, 2, 10)

// Twice appends twice into the room of a variable, which is memory that
// existed on entry.
//
// @Ensures r = 9
func Twice() (r int) {
	x := append(spare, 9) // want `vego: append may write into the capacity of spare, which Twice may not modify; it is memory that the package-level variable spare refers to; list spare in a // @Modifies clause`
	y := append(spare, 8)
	_ = y
	return x[2]
}

// fill writes its slice.
//
// @Requires |s| > 0
// @Modifies s
func fill(s []int) { s[0] = 0 }

var filled = []int{1}

// Pass hands what a variable refers to to a function that writes it.
//
// @Ensures True
func Pass() {
	fill(filled) // want `vego: fill may modify filled, which Pass may not modify; it is memory that the package-level variable filled refers to; list filled in a // @Modifies clause`
}

// ListsVariable names a variable in Modifies that it never writes.
//
// @Modifies filled // want `^vego: Modifies lists filled, but ListsVariable never needs to modify it; a Modifies clause must list exactly what the function may write$`
func ListsVariable() {}

// Assigns assigns a variable, and does not list it.
//
// @Ensures True
func Assigns() {
	local = 4 // want `^vego: local is assigned, which Assigns may not modify; list it in a // @Modifies clause$`
}

var local int

var accented = []rune("héllo")

// RunesAsBytes would hold if the conversion gave bytes.
//
// @Ensures n = 6
func RunesAsBytes() (n int) {
	return len(accented) // want `vego: postcondition may not hold: n = 6`
}

// SecondAsByte would hold if the conversion gave bytes.
//
// @Ensures r = 195
func SecondAsByte() (r rune) {
	return accented[1] // want `vego: postcondition may not hold: r = 195`
}
