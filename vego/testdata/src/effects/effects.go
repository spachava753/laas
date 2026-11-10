// Package effects holds programs in which a call that modifies a slice, or an
// assignment that replaces one, interacts with the evaluation of its
// surroundings. Each was once verified although it is wrong.
package effects

// @ Requires |a| > 0 And a[0] < 1000
func step(a []int, i int) bool {
	a[0]++
	return i < 2
}

//@ Ensures a'[0] = a[0] + 1 And (result <-> i < 2)

// ConditionMutation runs step three times, so a[0] ends at 3.
//
// @ Requires |a| > 0 And a[0] = 0
func ConditionMutation(a []int) {
	i := 0
	//@ Invariant 0 <= i <= 2
	//@ Variant 2-i
	for step(a, i) { // want `vego:\ cannot\ verify\ ConditionMutation:\ step\ may\ modify\ the\ slice\ passed\ as\ a,\ so\ the\ call\ must\ be\ a\ statement\ of\ its\ own\ or\ the\ whole\ right\-hand\ side\ of\ an\ assignment\ to\ variables`
		i++
	}
}

//@ Ensures a'[0] = 1

// @ Requires |a| = 1 And a[0] < 1000
func again(a []int) bool {
	a[0]++
	return true
}

//@ Ensures a'[0] = a[0] + 1 And result = True

// Forever never terminates: the condition undoes what the body does.
//
// @ Requires |a| = 1 And a[0] >= 0
func Forever(a []int) {
	//@ Invariant a[0] >= 0
	//@ Variant a[0]
	for again(a) { // want `vego:\ cannot\ verify\ Forever:\ again\ may\ modify\ the\ slice\ passed\ as\ a,\ so\ the\ call\ must\ be\ a\ statement\ of\ its\ own\ or\ the\ whole\ right\-hand\ side\ of\ an\ assignment\ to\ variables`
		a[0]--
	}
}

//@ Ensures False

func duplicated() (a, b []int) {
	a = make([]int, 1)
	return a, a // want `vego:\ cannot\ verify\ duplicated:\ slice\ a\ is\ returned\ twice,\ which\ would\ give\ the\ caller\ two\ names\ for\ one\ backing\ array`
}

//@ Ensures |a| = 1 And |b| = 1 And a[0] = 0 And b[0] = 0

// LHSStorage returns 1: the element is written to the old backing array.
func LHSStorage() int {
	a := []int{0}
	a, a[0] = []int{1}, 2 // want `vego:\ cannot\ verify\ LHSStorage:\ a\ is\ replaced\ and\ indexed\ in\ one\ assignment;\ the\ element\ would\ be\ written\ to\ the\ old\ backing\ array`
	return a[0]
}

//@ Ensures result = 2

// @ Requires |a| = 1
func reset(a []int) int {
	a[0] = 1
	return 0
}

//@ Ensures a'[0] = 1 And result = 0

// @ Requires |a| = 1 And a[0] = 0
func read(a []int, ignored int) int { return a[0] }

//@ Ensures result = 0

// ArgumentMutation returns 1: reset runs before read starts.
func ArgumentMutation() int {
	a := []int{0}
	return read(a, reset(a)) // want `vego:\ cannot\ verify\ ArgumentMutation:\ reset\ may\ modify\ the\ slice\ passed\ as\ a,\ so\ the\ call\ must\ be\ a\ statement\ of\ its\ own\ or\ the\ whole\ right\-hand\ side\ of\ an\ assignment\ to\ variables`
}

//@ Ensures result = 0

// @ Requires |a| = 2 And a[1] < 1000
func tick(a []int) int {
	a[1]++
	return 0
}

//@ Ensures a'[0] = a[0] And a'[1] = a[1]+1 And result = 0

// IndexTwice returns 1: the index expression is evaluated once.
//
// @ Requires |a| = 2 And a[0] = 0 And a[1] = 0
func IndexTwice(a []int) int {
	a[tick(a)]++ // want `vego:\ cannot\ verify\ IndexTwice:\ tick\ may\ modify\ the\ slice\ passed\ as\ a,\ so\ the\ call\ must\ be\ a\ statement\ of\ its\ own\ or\ the\ whole\ right\-hand\ side\ of\ an\ assignment\ to\ variables`
	return a[1]
}

//@ Ensures result = 2

func unknown() int { return 0 }

// IndexOnce reads and writes the same element even though nothing is known
// about the index.
//
// @ Requires |a| = 1 And a[0] < 1000
func IndexOnce(a []int) {
	i := unknown()
	if i == 0 {
		a[i] += 2
		a[i]++
	}
}

//@ Ensures a'[0] = a[0] Or a'[0] = a[0] + 3

// StatementCalls shows the supported placements of a modifying call.
//
// @ Requires |a| = 2 And a[1] = 0
func StatementCalls(a []int) (n int) {
	tick(a)
	n = tick(a)
	m := tick(a)
	return n + m + a[1]
}

//@ Ensures n = 3

func indirectWrite(a []int) {
	p := &a[0]
	*p = 1
}

func rangeWrite(a []int) {
	for a[0] = range 1 {
	}
}

// HiddenPointerWrite returns 1: the helper writes through a pointer.
func HiddenPointerWrite() int {
	a := []int{0}
	indirectWrite(a)
	return a[0] // want `vego:\ postcondition\ may\ not\ hold:\ result\ =\ 0`
}

//@ Ensures result = 0

// HiddenRangeWrite returns 0: the helper assigns in its range clause.
func HiddenRangeWrite() int {
	a := []int{1}
	rangeWrite(a)
	return a[0] // want `vego:\ postcondition\ may\ not\ hold:\ result\ =\ 1`
}

//@ Ensures result = 1

// @ Requires |a| > 0
func viaPointer(a []int) {
	p := &a[0] // want `vego:\ cannot\ verify\ viaPointer:\ expressions\ of\ type\ \*int\ are\ not\ supported`
	*p = 1
}

//@ Ensures True

// @ Requires |a| > 0
func viaRange(a []int) {
	for a[0] = range 1 { // want `vego:\ cannot\ verify\ viaRange:\ range\ loops\ must\ declare\ their\ variables\ with\ :=\ and\ must\ not\ reassign\ the\ ranged\ slice`
	}
}

//@ Ensures True

// AnnotatedHelpers must not trust helpers that verification gave up on.
func AnnotatedHelpers() int {
	a := []int{0}
	viaPointer(a)
	viaRange(a)
	return a[0] // want `vego:\ postcondition\ may\ not\ hold:\ result\ =\ 0`
}

//@ Ensures result = 0

// @ Requires |a| = 1
func change(a []int) int {
	a[0] = 1
	return 1
}

//@ Ensures a'[0] = 1 And result = 1

// TemporaryLiteral returns 1: the callee changes the temporary slice.
func TemporaryLiteral() int {
	return change([]int{0}) // want `vego:\ postcondition\ may\ not\ hold:\ result\ =\ 0`
}

//@ Ensures result = 0

// TemporaryMake returns 1 for the same reason.
func TemporaryMake() int {
	return change(make([]int, 1)) // want `vego:\ postcondition\ may\ not\ hold:\ result\ =\ 0`
}

//@ Ensures result = 0

// TemporaryOperand hides a modifying call inside an operand.
func TemporaryOperand() int {
	return change([]int{0}) + 1 // want `vego:\ cannot\ verify\ TemporaryOperand:\ change\ may\ modify\ the\ slice\ passed\ as\ a,\ so\ the\ call\ must\ be\ a\ statement\ of\ its\ own\ or\ the\ whole\ right\-hand\ side\ of\ an\ assignment\ to\ variables`
}

//@ Ensures result = 42

// TemporaryAccepted passes a temporary where that is sound.
func TemporaryAccepted() int {
	return change([]int{0})
}

//@ Ensures result = 1

// @ Requires |a| = 1
func setIndex(a []int) int {
	a[0] = 1
	return 0
}

//@ Ensures a'[0] = 1 And result = 0

// AssignmentPanics indexes with a[0] after the call has changed it.
//
// @ Requires |a| = 1 And a[0] = 0
func AssignmentPanics(a []int) {
	a[a[0]] = setIndex(a) // want `vego:\ cannot\ verify\ AssignmentPanics:\ setIndex\ may\ modify\ the\ slice\ passed\ as\ a,\ so\ the\ call\ must\ be\ a\ statement\ of\ its\ own\ or\ the\ whole\ right\-hand\ side\ of\ an\ assignment\ to\ variables`
}

// SavedIndex states the intended order explicitly.
//
// @ Requires |a| = 1 And a[0] = 0
func SavedIndex(a []int) {
	i := a[0]
	v := setIndex(a)
	a[i] = v
}

//@ Ensures a'[0] = 0
