package sourcecalls

import "io"

// Writes writes, in a run, the array of the slice each is handed beside f
// (D).
//
// @Requires |xs| > 0 And Forall i in [0, |xs|) : 0 <= xs[i] < 100
// @Modifies xs
// @Ensures True
func Writes(xs []int) {
	each(xs, func(x int) { xs[0] = x }) // want `xs\[0\] is assigned, which may be what an argument of each refers to directly`
}

// peek keeps the capacity of its slice across f.
//
// @Calls f()
// @Requires |xs| = 1 And cap(xs) >= 2
// @Ensures True
func peek(xs []int, f func()) (r int) {
	ys := xs[:cap(xs)]
	a := ys[1]
	f()
	return a - ys[1]
}

// Capacity writes, in a run, the capacity of the slice peek is handed (F1).
//
// @Ensures True
func Capacity() {
	big := make([]int, 2)
	_ = peek(big[:1], func() { big[1] = 9 }) // want `big\[1\] is assigned, which may be what an argument of peek refers to directly`
}

type pile struct{ items []int }

// @Requires p != nil And 0 <= x < 100 And |p.items| < 1000
// @Modifies p, p.items
// @Ensures True
func (p *pile) push(x int) {
	p.items = append(p.items, x)
}

// SelfAppend hands each a method value whose receiver holds the slice each
// is handed, and whose append may write its capacity (F1).
//
// @Requires p != nil And |p.items| < 10 And Forall i in [0, |p.items|) : 0 <= p.items[i] < 100
// @Modifies p
// @Ensures True
func SelfAppend(p *pile) {
	each(p.items, p.push) // want `precondition of push may not hold: \|p.items\| < 1000` `push may modify what it calls p.items, which may be what an argument of each refers to directly` `push may modify what it calls p.items, which SelfAppend may not modify`
}

var global int

// SetGlobal assigns global, which makes it an assigned variable.
func SetGlobal(n int) { global = n }

// readsGlobal reads a variable of the package after f, which may write it.
//
// @Calls f()
// @Requires 0 <= n
// @Ensures True
func readsGlobal(n int, f func()) (r int) {
	if global != 1 {
		return 0
	}
	f()
	// @Assert global = 1 // want `assertion may not hold: global = 1`
	return global
}

// ranges calls f while it ranges over a map it made, to which f may add
// keys (F5).
//
// @Calls f()
// @Ensures True
func ranges(f func()) {
	m := map[int]bool{1: true}
	for k := range m {
		_ = k
		f() // want `f may modify m while the loop at defects.go:\d+:\d+ ranges over it`
	}
}

// stillOpen relies on a state f may change (F5).
//
// @Requires c != nil And ~closed(c)
// @Calls f()
// @Ensures True
func stillOpen(c io.Closer, f func()) {
	f()
	// @Assert ~closed(c) // want `assertion may not hold: ~closed\(c\)`
}

// outer hands inner a literal that calls f, which may write the new array
// inner is handed and relies on (F2).
//
// @Calls f()
// @Ensures True
func outer(f func()) {
	ys := make([]int, 3)
	_ = inner(ys, func(y int) { f() }) // want `f may write what an argument of inner refers to directly`
}

// @Calls g(y)
// @Requires |ys| = 3
// @Ensures r = ys[0]
func inner(ys []int, g func(int)) (r int) {
	a := ys[0]
	g(0)
	return a
}

// @Requires e != nil
type report func(e error)

// @Calls f(x) When x != nil
// @Requires e != nil
// @Ensures True
func eachErr(e error, f func(error)) {
	f(e)
}

// Tell hands eachErr a value of a type with a contract, which may come
// from code nobody has seen, and eachErr hands it an error (F4).
//
// @Requires r != nil And e != nil
// @Ensures True
func Tell(r report, e error) {
	eachErr(e, r) // want `cannot verify Tell: r is handed to eachErr as f, which eachErr calls with a value of type error`
}

// Stored stores the function it is given (D2).
//
// @Calls f()
// @Ensures True
func Stored(f func()) (g func()) {
	f()
	return f // want `cannot verify Stored: the Calls annotation of Stored gives f a contract that holds only while Stored calls it`
}

// Compared compares the function it is given with nil.
//
// @Calls f()
// @Ensures True
func Compared(f func()) {
	if f != nil { // want `cannot verify Compared: the Calls annotation of Compared gives f a contract that holds only while Compared calls it`
		f()
	}
}

// Unmet calls f outside its When.
//
// @Calls f(x) When 0 <= x
// @Ensures True
func Unmet(f func(int)) {
	f(-1) // want `the When of the Calls annotation of f may not hold at this call: 0 <= x`
}

// HandsNil hands each nil, an uncontracted value, and a variable bound to
// a literal.
//
// @Requires Forall i in [0, |xs|) : 0 <= xs[i] < 100
// @Ensures True
func HandsNil(xs []int, g func(int)) {
	each(xs, g) // want `cannot verify HandsNil: g is passed to each as f, which each calls, and its type func\(int\) has no contract`
}

// Walker walks a slice.
//
// @Ensures True
type Walker func(xs []int, f func(int))

// AsValue makes each into a value of a type with a contract.
//
// @Ensures w != nil
func AsValue() (w Walker) {
	return each // want `cannot verify AsValue: each calls a function it is given, and cannot be used as`
}

type item struct{ n int }

// eachItem calls f with every element of xs.
//
// @Calls f(p) When p != nil
// @Requires Forall i in [0, |xs|) : xs[i] != nil
// @Ensures True
func eachItem(xs []*item, f func(*item)) {
	for _, p := range xs {
		f(p)
	}
}

// keepsPointee relies, after f, on what an element of its slice points
// to, which is not what it is handed directly: f may write it.
//
// @Calls f(p) When p != nil
// @Requires |xs| = 1 And xs[0] != nil And xs[0].n = 1
// @Ensures True
func keepsPointee(xs []*item, f func(*item)) {
	f(xs[0])
	// @Assert xs[0].n = 1 // want `assertion may not hold: xs\[0\].n = 1`
}

// twoLevels keeps a slice that a pointer argument refers to, two levels
// down, across f, which may write it.
//
// @Calls f()
// @Requires p != nil And |p.items| = 2 And p.items[1] = 4
// @Ensures True
func twoLevels(p *pile, f func()) {
	ys := p.items[1:]
	f()
	// @Assert ys[0] = 4 // want `assertion may not hold: ys\[0\] = 4`
	_ = ys
}

type value struct{ n int }

// @Requires 0 <= x < 100
// @Ensures True
func (v value) at(x int) {}

// NilReceiver hands each a method value of a nil pointer whose method has
// a value receiver, which Go dereferences where the method value is made.
//
// @Requires Forall i in [0, |xs|) : 0 <= xs[i] < 100
// @Ensures True
func NilReceiver(xs []int) {
	var v *value
	each(xs, v.at) // want `pointer may be nil`
}

// @Invariant 0 < stride
var stride = 1

// SetStride keeps the invariant.
//
// @Requires 0 < n
// @Modifies stride
// @Ensures True
func SetStride(n int) { stride = n }

// divides relies, after f, on an invariant of a variable that f may write
// and leave broken in the middle of a function of its own (F5).
//
// @Calls f()
// @Ensures True
func divides(f func()) (r int) {
	f()
	return 10 / stride // want `possible division by zero`
}

// sameStatement reads a variable of the package and calls f in one
// statement, which Go may order either way (F5).
//
// @Calls f()
// @Ensures True
func sameStatement(f func() (k int)) (same bool) {
	return global == f() // want `global may be read before or after the call to f`
}

// Cycle hands each a value of a type with a contract whose code, by its
// type, may call back into Cycle: each calls f with integers only, which
// carry no code, and the value may be any function of the package of its
// type (F3).
//
// @Requires 0 <= x < 100
// @Ensures True
type step func(x int)

// @Requires s != nil And Forall i in [0, |xs|) : 0 <= xs[i] < 100
// @Ensures True
func Cycle(xs []int, s step) {
	each(xs, s) // want `this call may not end: Cycle calls each\(xs, s\)` `this call may not end: Cycle calls s\(x\)` `s may modify global, which Cycle may not modify`
}

// Back is a function of the package of the type step, which a value of
// step may be, and it calls Cycle.
//
// @Requires 0 <= x < 100
// @Ensures True
func Back(x int) {
	Cycle([]int{x}, Back) // want `cannot verify Back: Back may call through a function value or an interface value`
}

// setWith is trusted; see testdata/trusted.yaml.
func setWith(m map[int]int, k, v int, f func()) {
	m[k] = v
	f()
}

var shared map[int]int

// SetShared makes shared an assigned variable.
func SetShared(m map[int]int) { shared = m }

// entryWritten hands setWith, which writes one entry of a map it made, a
// literal that calls f, which may write that map: the entry is no cell
// that f keeps (F22 of the review of step 2).
//
// @Calls f()
// @Modifies shared
// @Ensures True
func entryWritten(f func()) {
	m := make(map[int]int)
	shared = m
	setWith(m, 1, 7, func() { f() }) // want `f may write what setWith may write itself`
}

// entryKept is entryWritten with the map in what the function may write,
// which f may not write.
//
// @Calls f()
// @Requires m != nil
// @Modifies m
// @Ensures True
func entryKept(m map[int]int, f func()) {
	setWith(m, 1, 7, func() { f() })
}

type cell struct{ n int }
type cells struct{ items []cell }

// Peek2 keeps across f what a pointer argument reaches through a field: the
// array of another slice, which f may write, even when the slice argument
// lies at its start (F23 of the review of step 2).
//
// @Calls f()
// @Requires p != nil And |p.items| = 4 And |xs| = 1 And cap(xs) = 1 And &xs[0] = &p.items[0]
// @Ensures same
func Peek2(xs []cell, p *cells, f func()) (same bool) {
	a := p.items[3].n
	f()
	return a == p.items[3].n // want `postcondition may not hold: same`
}

// PeekPointer keeps across f an element of the array a pointer argument
// points into, beside the one it points to (F23).
//
// @Calls f()
// @Requires p != nil And |p.items| = 4 And q != nil And &p.items[1] = q
// @Ensures same
func PeekPointer(q *cell, p *cells, f func()) (same bool) {
	a := p.items[0].n
	f()
	return a == p.items[0].n // want `postcondition may not hold: same`
}

// eachOther calls f with what is not one of the elements its When names.
//
// @Calls f(p) When Exists k in [0, |xs|) : p = old(xs[k])
// @Ensures True
func eachOther(xs []*elem, f func(*elem)) {
	f(&elem{}) // want `the When of the Calls annotation of f may not hold at this call: Exists k in \[0, \|xs\|\) : p = old\(xs\[k\]\)`
}

// ElemsMaybeNil reads what eachElem hands with no nil test, of a slice
// whose elements may be nil.
//
// @Ensures True
func ElemsMaybeNil(xs []*elem) {
	eachElem(xs, func(p *elem) {
		_ = p.n // want `pointer may be nil, in the function literal run by eachElem`
	})
}

// eachCleared writes an element and then hands it to f: what its When
// names is what xs held on entry, which was not nil.
//
// @Calls f(p) When Exists k in [0, |xs|) : p = old(xs[k])
// @Requires |xs| > 0 And Forall i in [0, |xs|) : xs[i] != nil
// @Modifies xs
// @Ensures True
func eachCleared(xs []*elem, f func(*elem)) {
	xs[0] = nil
	f(xs[0]) // want `the When of the Calls annotation of f may not hold at this call: Exists k in \[0, \|xs\|\) : p = old\(xs\[k\]\)`
}
