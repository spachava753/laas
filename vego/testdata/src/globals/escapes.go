package globals

// Each variable below is made by its initialiser, and code that is not
// verified lets a reference to what it refers to out of it, in one way
// each. What it refers to is then ordinary memory, and a contract that
// relies on the literal is not proved.

var passed = []int{1}

func takes(s []int) { s[0] = 2 }

func pass() { takes(passed) }

// Passed would be 1 if passed were only read.
//
// @Ensures r = 1
func Passed() (r int) {
	return passed[0] // want `vego: postcondition may not hold: r = 1`
}

type ints []int

func (s ints) Set() { s[0] = 2 }

var received = ints{1}

func receive() { received.Set() }

// Received is passed as a receiver.
//
// @Ensures r = 1
func Received() (r int) {
	return received[0] // want `vego: postcondition may not hold: r = 1`
}

var sliced = []int{1, 2}

// view is initialised with a slice of sliced.
var view = sliced[1:]

// Sliced is reached through another variable.
//
// @Ensures r = 2
func Sliced() (r int) {
	return sliced[1] // want `vego: postcondition may not hold: r = 2`
}

var appended = make([]int, 1, 4)

func grow() { _ = append(appended, 3) }

// Appended is written by an append in place.
//
// @Requires |appended| = 1
// @Ensures r = 0
func Appended() (r int) {
	return appended[0] // want `vego: postcondition may not hold: r = 0`
}

type cell struct{ N int }

func (c *cell) Inc() { c.N++ }

var cells = []cell{{N: 1}, {N: 2}}

func bump() { cells[0].Inc() }

// FirstCell has a pointer-receiver method selected on an element.
//
// @Ensures r = 1
func FirstCell() (r int) {
	return cells[0].N // want `vego: postcondition may not hold: r = 1`
}

var addressed = []cell{{N: 1}}

func address() { p := &addressed[0]; p.N = 2 }

// Addressed has the address of an element taken.
//
// @Ensures r = 1
func Addressed() (r int) {
	return addressed[0].N // want `vego: postcondition may not hold: r = 1`
}

var assignedTo = []cell{{N: 1}}

func assignElement() { assignedTo[0].N = 2 }

// AssignedTo has a field of an element assigned.
//
// @Ensures r = 1
func AssignedTo() (r int) {
	return assignedTo[0].N // want `vego: postcondition may not hold: r = 1`
}

var copied = []int{1}

func copyOut() { t := copied; t[0] = 2 }

// Copied is assigned to a variable.
//
// @Ensures r = 1
func Copied() (r int) {
	return copied[0] // want `vego: postcondition may not hold: r = 1`
}

var nested = [][]int{{1}}

func rangeNested() {
	for _, r := range nested {
		r[0] = 2
	}
}

// Nested ranges over slices that it writes through. Its elements are not
// flat, so its contents could not be read only in any case.
//
// @Ensures True
func Nested() (r int) { return len(nested) }

var deferred = []cell{{N: 1}}

func deferBump() { defer deferred[0].Inc() }

// Deferred has a method deferred on an element.
//
// @Ensures r = 1
func Deferred() (r int) {
	return deferred[0].N // want `vego: postcondition may not hold: r = 1`
}

var pointed = &cell{N: 1}

func incPointed() { pointed.Inc() }

// Pointed has a method called on what it points to.
//
// @Ensures r = 1
func Pointed() (r int) {
	return pointed.N // want `vego: postcondition may not hold: r = 1`
}

var plans = map[string]int{"free": 10}

func setPlan() { plans["free"] = 20 }

// Plans has a key written.
//
// @Ensures r = 10
func Plans() (r int) {
	return plans["free"] // want `vego: postcondition may not hold: r = 10`
}

var compared = []int{1}

func compare() bool { return compared == nil }

// Compared is compared with nil, which is a read.
//
// @Ensures r = 1
func Compared() (r int) { return compared[0] }

var literal = []int{1}

var holder = struct{ s []int }{s: literal}

// Literal is put into a composite literal.
//
// @Ensures r = 1
func Literal() (r int) {
	return literal[0] // want `vego: postcondition may not hold: r = 1`
}

var captured = []int{1}

var later = func() { captured[0] = 2 }

// Captured is written in a function literal.
//
// @Ensures r = 1
func Captured() (r int) {
	return captured[0] // want `vego: postcondition may not hold: r = 1`
}

// The three programs of F1 of the design review: memory that the
// initialiser did not make may be reachable through something else.

type plain struct{ Timeout int }

var defaults2 = plain{Timeout: 30}

// cfg2 is initialised with the address of another variable.
var cfg2 = &defaults2

var kept []int

func mk() []int { kept = make([]int, 2); return kept }

// made2 is initialised by a call that keeps a copy.
var made2 = mk()

// ProbeCfg reads cfg2.Timeout twice around a write through p.
//
// @Requires p != nil
// @Modifies p
// @Ensures r
func ProbeCfg(p *plain) (r bool) {
	if cfg2 == nil {
		return true
	}
	s := cfg2.Timeout
	p.Timeout = 7
	return cfg2.Timeout == s // want `vego: postcondition may not hold: r`
}

// ProbeMade reads made2 twice around a write through A.
//
// @Requires |A| > 0
// @Modifies A
// @Ensures r
func ProbeMade(A []int) (r bool) {
	if len(made2) == 0 {
		return true
	}
	s := made2[0]
	A[0] = 7
	return made2[0] == s // want `vego: postcondition may not hold: r`
}

// RunProbes is not verified; it passes the other references.
func RunProbes() (bool, bool) { return ProbeCfg(&defaults2), ProbeMade(kept) }
