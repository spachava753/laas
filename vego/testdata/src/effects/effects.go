// Package effects holds programs in which a call that modifies a slice, or an
// assignment that replaces one, interacts with the evaluation of its
// surroundings. Each was once verified although it is wrong.
package effects

// @Requires |a| > 0 And a[0] < 1000
// @Modifies a
// @Ensures a'[0] = a[0] + 1 And (result <-> i < 2)
func step(a []int, i int) (result bool) {
	a[0]++
	return i < 2
}

// ConditionMutation runs step three times, so a[0] ends at 3.
//
// @Requires |a| > 0 And a[0] = 0
// @Ensures a'[0] = 1
func ConditionMutation(a []int) {
	i := 0
	// @Invariant 0 <= i <= 2
	// @Variant 2-i
	for step(a, i) { // want `vego: cannot verify ConditionMutation: step may modify a, and a call that may modify memory is not supported yet in the condition of a for loop`
		i++
	}
}

// @Requires |a| = 1 And a[0] < 1000
// @Modifies a
// @Ensures a'[0] = a[0] + 1 And result = True
func again(a []int) (result bool) {
	a[0]++
	return true
}

// Forever never terminates: the condition undoes what the body does.
//
// @Requires |a| = 1 And a[0] >= 0
// @Ensures False
func Forever(a []int) {
	// @Invariant a[0] >= 0
	// @Variant a[0]
	for again(a) { // want `vego: precondition of again may not hold: a\[0\] < 1000` `vego: cannot verify Forever: again may modify a, and a call that may modify memory is not supported yet in the condition of a for loop`
		a[0]--
	}
}

// @Ensures |a| = 1 And |b| = 1 And a[0] = 0 And b[0] = 0
func duplicated() (a, b []int) {
	a = make([]int, 1)
	return a, a
}

// LHSStorage returns 1: the element is written to the old backing array.
//
// @Ensures result = 2
func LHSStorage() (result int) {
	a := []int{0}
	a, a[0] = []int{1}, 2
	return a[0] // want `vego: postcondition may not hold: result = 2`
}

// @Requires |a| = 1
// @Modifies a
// @Ensures a'[0] = 1 And result = 0
func reset(a []int) (result int) {
	a[0] = 1
	return 0
}

// @Requires |a| = 1 And a[0] = 0
// @Ensures result = 0
func read(a []int, ignored int) (result int) { return a[0] }

// ArgumentMutation returns 1: reset runs before read starts, so read is
// called with a[0] = 1.
//
// @Ensures result = 0
func ArgumentMutation() (result int) {
	a := []int{0}
	return read(a, reset(a)) // want `vego: precondition of read may not hold: a\[0\] = 0`
}

// @Requires |a| = 2 And a[1] < 1000
// @Modifies a
// @Ensures a'[0] = a[0] And a'[1] = a[1]+1 And result = 0
func tick(a []int) (result int) {
	a[1]++
	return 0
}

// IndexTwice returns 1: the index expression is evaluated once.
//
// @Requires |a| = 2 And a[0] = 0 And a[1] = 0
// @Modifies a
// @Ensures result = 2
func IndexTwice(a []int) (result int) {
	a[tick(a)]++
	return a[1] // want `vego: postcondition may not hold: result = 2`
}

func unknown() int { return 0 }

// IndexOnce reads and writes the same element even though nothing is known
// about the index.
//
// @Requires |a| = 1 And a[0] < 1000
// @Modifies a
// @Ensures a'[0] = a[0] Or a'[0] = a[0] + 3
func IndexOnce(a []int) {
	i := unknown()
	if i == 0 {
		a[i] += 2
		a[i]++
	}
}

// StatementCalls shows the supported placements of a modifying call.
//
// @Requires |a| = 2 And a[1] = 0
// @Modifies a
// @Ensures n = 3
func StatementCalls(a []int) (n int) {
	tick(a)
	n = tick(a)
	m := tick(a)
	return n + m + a[1]
}

func indirectWrite(a []int) {
	p := &a[0]
	*p = 1
}

func rangeWrite(a []int) {
	for a[0] = range 1 {
	}
}

// HiddenPointerWrite returns 1: the helper writes through a pointer.
//
// @Ensures result = 0
func HiddenPointerWrite() (result int) {
	a := []int{0}
	indirectWrite(a)
	return a[0] // want `vego:\ postcondition\ may\ not\ hold:\ result\ =\ 0`
}

// HiddenRangeWrite returns 0: the helper assigns in its range clause.
//
// @Ensures result = 1
func HiddenRangeWrite() (result int) {
	a := []int{1}
	rangeWrite(a)
	return a[0] // want `vego:\ postcondition\ may\ not\ hold:\ result\ =\ 1`
}

// @Requires |a| > 0
// @Ensures True
func viaPointer(a []int) {
	p := &a[0] // want `vego: cannot verify viaPointer: p has unsupported type \*int`
	*p = 1
}

// @Requires |a| > 0
// @Ensures True
func viaRange(a []int) {
	for a[0] = range 1 { // want `vego: cannot verify viaRange: range loops must declare their variables with :=`
	}
}

// AnnotatedHelpers calls helpers that verification gave up on. Their
// contracts, which list nothing as modified, were not established; that is
// reported where each helper is declared, and makes this proof worthless.
//
// @Ensures result = 0
func AnnotatedHelpers() (result int) {
	a := []int{0}
	viaPointer(a)
	viaRange(a)
	return a[0]
}

// @Requires |a| = 1
// @Modifies a
// @Ensures a'[0] = 1 And result = 1
func change(a []int) (result int) {
	a[0] = 1
	return 1
}

// TemporaryLiteral returns 1: the callee changes the temporary slice.
//
// @Ensures result = 0
func TemporaryLiteral() (result int) {
	return change([]int{0}) // want `vego:\ postcondition\ may\ not\ hold:\ result\ =\ 0`
}

// TemporaryMake returns 1 for the same reason.
//
// @Ensures result = 0
func TemporaryMake() (result int) {
	return change(make([]int, 1)) // want `vego:\ postcondition\ may\ not\ hold:\ result\ =\ 0`
}

// TemporaryOperand hides a modifying call inside an operand.
//
// @Ensures result = 42
func TemporaryOperand() (result int) {
	return change([]int{0}) + 1 // want `vego: postcondition may not hold: result = 42`
}

// TemporaryAccepted passes a temporary where that is sound.
//
// @Ensures result = 1
func TemporaryAccepted() (result int) {
	return change([]int{0})
}

// @Requires |a| = 1
// @Modifies a
// @Ensures a'[0] = 1 And result = 0
func setIndex(a []int) (result int) {
	a[0] = 1
	return 0
}

// AssignmentPanics indexes with a[0], which Go may read after the call has
// changed it.
//
// @Requires |a| = 1 And a[0] = 0
// @Modifies a
func AssignmentPanics(a []int) {
	a[a[0]] = setIndex(a) // want `vego: a\[0\] may be read before or after the call to setIndex, which may change it`
}

// SavedIndex states the intended order explicitly.
//
// @Requires |a| = 1 And a[0] = 0
// @Modifies a
// @Ensures a'[0] = 0
func SavedIndex(a []int) {
	i := a[0]
	v := setIndex(a)
	a[i] = v
}
