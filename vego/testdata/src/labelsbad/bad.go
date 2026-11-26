// Package labelsbad has labelled jumps and fallthroughs whose contracts
// are false, and annotations that stand where no step reads them.
package labelsbad

// SkipsTail goes on to the next iteration before the step that decreases
// the variant.
//
// @Requires 0 <= n <= 100
// @Ensures True
func SkipsTail(n int) {
	// @Invariant 0 <= i <= n
	// @Variant n - i
outer:
	for i := 0; i < n; { // want `vego: loop variant may not decrease: n - i`
		for j := range 2 {
			if j == 1 {
				continue outer
			}
		}
		i++
	}
}

// BreaksInvariant goes on to the next iteration where the outer invariant
// does not hold.
//
// @Requires |a| <= 100
// @Ensures True
func BreaksInvariant(a [][]int) (n int) {
	// @Invariant n = 0
outer:
	for i := range a { // want `vego: loop invariant may not be preserved: n = 0`
		// @Invariant n = 0
		for j := range a[i] {
			if a[i][j] < 0 {
				n = 1
				continue outer
			}
		}
	}
	return n
}

// LeavesEarly claims that it saw every row, but breaks out of both loops.
//
// @Requires |a| <= 100
// @Ensures r = |a|
func LeavesEarly(a [][]int) (r int) {
	// @Invariant r = i
outer:
	for i := range a {
		for j := range a[i] {
			if a[i][j] < 0 {
				break outer
			}
		}
		r++
	}
	return r // want `vego: postcondition may not hold: r = \|a\|`
}

// BreakFromSwitch claims that the loop runs to its end, but a break with
// the loop's label inside a switch leaves it.
//
// @Ensures r = |xs|
func BreakFromSwitch(xs []int) (r int) {
	// @Invariant r = i
loop:
	for i := range xs {
		switch {
		case xs[i] == 0:
			break loop
		}
		r++
	}
	return r // want `vego: postcondition may not hold: r = \|xs\|`
}

// Between has a loop annotation between the label and the loop.
//
// @Ensures True
func Between(xs []int) {
outer:
	// @Invariant 0 <= i // want `vego: Invariant annotation must stand between statements, on a line of its own`
	for i := range xs {
		if i > 3 {
			break outer
		}
	}
}

// AssertBetween has an assertion between the label and the loop.
//
// @Ensures True
func AssertBetween(xs []int) {
outer:
	// @Assert False // want `vego: Assert annotation must stand between statements, on a line of its own`
	for i := range xs {
		if i > 3 {
			break outer
		}
	}
}

// OnSwitch has a loop annotation above a labelled switch.
//
// @Ensures True
func OnSwitch(n int) (r int) {
	// @Invariant r = 0 // want `vego: Invariant annotation must be directly above a for loop`
sw:
	switch n {
	case 0:
		break sw
	}
	return r
}

// FallTested claims that the clause fallen into was tested.
//
// @Ensures n = 0 -> r = 1
func FallTested(n int) (r int) {
	switch n {
	case 0:
		fallthrough
	case 1:
		r = 2
	}
	return r // want `vego: postcondition may not hold: n = 0 -> r = 1`
}

// calls counts the calls of next.
var calls int

// next counts its calls and returns 0.
//
// @Requires calls < 100
// @Modifies calls
// @Ensures calls' = calls + 1 And r = 0
func next() (r int) {
	calls++
	return 0
}

// tagOnce evaluates the tag once, also when a clause falls into the next,
// and claims that it was evaluated twice.
//
// @Requires calls < 50
// @Modifies calls
// @Ensures calls' = calls + 2
func tagOnce() {
	switch next() {
	case 0:
		fallthrough
	case 1:
	}
} // want `vego: postcondition may not hold: calls' = calls \+ 2`

// Goto is refused.
//
// @Ensures True
func Goto(n int) {
	if n > 0 {
		goto done // want `vego: cannot verify Goto: goto is not supported`
	}
done:
}

// SharedIteration claims what would hold if the iterations shared their
// variable, as before Go 1.22.
//
// @Ensures r = 1
func SharedIteration() (r int) {
	var first *int
	// @Invariant 0 <= i <= 2
	// @Invariant i >= 1 -> first != nil
	// @Variant 2 - i
outer:
	for i := 0; i < 2; i++ {
		if i == 0 {
			first = &i
		}
		// @Invariant 0 <= i < 2 And first != nil
		// @Variant 1 - j
		for j := 0; j < 1; j++ {
			continue outer
		}
	}
	if first == nil {
		return -1
	}
	return *first // want `vego: postcondition may not hold: r = 1`
}
