package trialfaults

// A call of a function whose contract cannot be read in full is reported
// at the call, so the caller fails there, and the caller is verified on
// with what can be read, so that its own faults are reported too.

// R holds a value of any type.
type R struct {
	next  *R
	Value any
}

// touch has an Ensures that cannot be read.
//
// @Requires r != nil
// @Ensures r.Value' = r.Value // want `in Ensures annotation: an interface value can only be compared with nil`
func (r *R) touch() (result *R) {
	return r
}

// The trial's program: the index and the Ensures are wrong too.
//
// @Requires r != nil
// @Ensures n = 1
func (r *R) Caller(a []int) (n int) {
	r.touch() // want `the contract of touch cannot be used: its Ensures annotation at badcallee.go:\d+:\d+ cannot be read \(an interface value can only be compared with nil\), so this call is verified without it`
	return a[5] // want `index may be out of range` `postcondition may not hold: n = 1`
}

// A call on the right of && is made only when the left holds, and is
// reported where it is.
//
// @Requires r != nil
// @Ensures n = 1
func (r *R) Guarded(a []int, ok bool) (n int) {
	if ok && r.touch() != nil { // want `the contract of touch cannot be used`
		n = 2
	}
	return a[5] // want `index may be out of range` `postcondition may not hold: n = 1`
}

// A call in a loop is reported in the loop.
//
// @Requires r != nil And 0 <= k <= 10
// @Ensures n = 1
func (r *R) Looped(a []int, k int) (n int) {
	// @Variant k - i
	for i := 0; i < k; i++ {
		r.touch() // want `the contract of touch cannot be used`
	}
	return a[5] // want `index may be out of range` `postcondition may not hold: n = 1`
}

// A call in a literal called in place is reported at the call in the
// literal.
//
// @Requires r != nil
// @Ensures n = 1
func (r *R) InLiteral(a []int) (n int) {
	f := func() {
		r.touch() // want `the contract of touch cannot be used`
	}
	f()
	return a[5] // want `index may be out of range` `postcondition may not hold: n = 1`
}

// A deferred call is reported where it is deferred.
//
// @Requires r != nil
// @Ensures n = 1
func (r *R) Deferred(a []int) (n int) {
	defer r.touch() // want `the contract of touch cannot be used`
	return a[5] // want `index may be out of range` `postcondition may not hold: n = 1`
}

// A literal with two ends is joined after the call; the report stays.
//
// @Requires r != nil
// @Ensures n = 1
func (r *R) Joined(a []int, ok bool) (n int) {
	func() {
		if ok {
			r.touch() // want `the contract of touch cannot be used`
			return
		}
		n = 3
	}()
	return a[5] // want `index may be out of range` `postcondition may not hold: n = 1`
}

// gate has a Requires that cannot be read, so nothing it ensures is
// assumed: its Ensures would rest on a precondition that was not checked.
//
// @Requires x.Value = x.Value // want `in Requires annotation: an interface value can only be compared with nil`
// @Ensures n = 7
func gate(x *R) (n int) {
	return 7
}

// @Requires r != nil
// @Ensures n = 7
func (r *R) Gated() (n int) {
	n = gate(r) // want `the contract of gate cannot be used: its Requires annotation at badcallee.go:\d+:\d+ cannot be read \(an interface value can only be compared with nil\), so this call is verified with none of its Requires and Ensures`
	return n // want `postcondition may not hold: n = 7`
}

// writes lists what it modifies in a way that cannot be read, so the path
// ends at a call of it.
//
// @Requires r != nil
// @Modifies r.missing // want `in Modifies annotation: r.missing: trialfaults.R has no field missing`
// @Ensures True
func writes(r *R) {
}

// @Requires r != nil
// @Ensures n = 1
func (r *R) Writes(a []int) (n int) {
	if len(a) <= 3 {
		writes(r) // want `the contract of writes cannot be used: its Modifies annotation at badcallee.go:\d+:\d+ cannot be read \(.*\), so nothing after this call is verified on this path`
		return a[5]
	}
	return a[5] // want `index may be out of range` `postcondition may not hold: n = 1`
}

// Shape has an invariant that cannot be read: it is neither assumed nor
// proved where it is used, and the rest is still verified.
//
// @Invariant s.v = s.v // want `in Invariant annotation: s is neither a field of the type nor a constant`
type Shape struct {
	v any
	n int
}

// @Ensures n = 1
func UsesShape(s Shape, a []int) (n int) { // want `the invariants of Shape cannot be used`
	return a[5] // want `index may be out of range` `postcondition may not hold: n = 1`
}

// Op is a function type with an Ensures that cannot be read; a call
// through a value of it checks what it requires, forgets what it modifies,
// and assumes nothing more.
//
// @Requires x >= 0
// @Ensures r = q // want `in Ensures annotation: unknown name q`
type Op func(x int) (r int)

// @Requires f != nil
// @Ensures n = 1
func CallsOp(f Op, a []int) (n int) {
	f(1) // want `the contract of Op cannot be used: its Ensures annotation at badcallee.go:\d+:\d+ cannot be read \(.*\), so this call is verified with none of its Ensures`
	return a[5] // want `index may be out of range` `postcondition may not hold: n = 1`
}

// Meter has a method whose Ensures cannot be read.
type Meter interface {
	// @Ensures n = q // want `in Ensures annotation: unknown name q`
	Read(v int) (n int)
}

// @Requires m != nil
// @Ensures n = 1
func Reads(m Meter, a []int) (n int) {
	m.Read(1) // want `the contract of Meter.Read cannot be used: its Ensures annotation at badcallee.go:\d+:\d+ cannot be read`
	return a[5] // want `index may be out of range` `postcondition may not hold: n = 1`
}

// A call whose Modifies cannot be read ends its path in a loop too, and
// what the loop forgets needs nothing of it: in the body, in the condition,
// and in a literal the loop calls.
//
// @Requires r != nil And 0 <= k <= 10
// @Ensures n = 1
func (r *R) LoopedWrites(a []int, k int) (n int) {
	// @Variant k - i
	for i := 0; i < k; i++ {
		writes(r) // want `the contract of writes cannot be used`
	}
	return a[5] // want `index may be out of range` `postcondition may not hold: n = 1`
}

// writesOK has a Modifies that cannot be read and a result.
//
// @Requires r != nil
// @Modifies r.missing // want `in Modifies annotation: r.missing: trialfaults.R has no field missing`
// @Ensures True
func writesOK(r *R) (ok bool) {
	return true
}

// @Requires r != nil And 0 <= k <= 10
// @Ensures n = 1
func (r *R) LoopedCondition(a []int, k int) (n int) {
	i := 0
	// @Variant k - i
	for i < k && writesOK(r) { // want `the contract of writesOK cannot be used`
		i++
	}
	return a[5] // want `index may be out of range` `postcondition may not hold: n = 1`
}

// @Requires r != nil And 0 <= k <= 10
// @Ensures n = 1
func (r *R) LoopedLiteral(a []int, k int) (n int) {
	f := func() {
		writes(r) // want `the contract of writes cannot be used`
	}
	// @Variant k - i
	for i := 0; i < k; i++ {
		f()
	}
	return a[5] // want `index may be out of range` `postcondition may not hold: n = 1`
}
