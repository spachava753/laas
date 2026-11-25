package copies

// Each function here claims something false of copy, or uses copy where it
// is not supported, and is refused.

// The shorter length is copied, not the destination's.
//
// @Modifies dst
// @Ensures n = |dst|
func CountWrong(dst, src []int) (n int) {
	return copy(dst, src) // want `postcondition may not hold: n = \|dst\|`
}

// @Modifies dst
// @Ensures n = |src|
func CountSourceWrong(dst, src []int) (n int) {
	return copy(dst, src) // want `postcondition may not hold: n = \|src\|`
}

// What lies after the copied elements is not written.
//
// @Requires |dst| = 4 And |src| = 2
// @Modifies dst
// @Ensures dst'[2] = src[0]
func ShorterWrong(dst, src []int) {
	copy(dst, src)
} // want `postcondition may not hold: dst'\[2\] = src\[0\]`

// A copy down over itself reads the elements before it writes them.
//
// @Requires 0 <= n And n + 2 <= |buf|
// @Modifies buf
// @Ensures buf'[0] = buf[n + 1]
func ShiftWrong(buf []byte, n int) (r int) {
	return copy(buf, buf[n:]) // want `postcondition may not hold: buf'\[0\] = buf\[n \+ 1\]`
}

// A copy up over itself is not a loop that copies forward: the last
// element is what the one before held, not what the first held.
//
// @Requires |buf| = 4
// @Modifies buf
// @Ensures buf'[3] = buf[0]
func ShiftUpWrong(buf []byte) {
	copy(buf[1:], buf)
} // want `postcondition may not hold: buf'\[3\] = buf\[0\]`

// The destination in the source's array is written from the old elements.
//
// @Ensures r = 3
func SameArrayWrong() (r int) {
	a := [4]int{1, 2, 3, 4}
	copy(a[2:], a[:])
	return a[2] // want `postcondition may not hold: r = 3`
}

// A nil destination receives nothing.
//
// @Requires |src| > 0
// @Ensures n = 1
func NilWrong(src []int) (n int) {
	var none []int
	return copy(none, src) // want `postcondition may not hold: n = 1`
}

// The destination must be listed.
//
// @Requires |dst| > 0
// @Ensures True
func Unlisted(dst, src []int) {
	copy(dst, src) // want `copy writes the elements of dst, which Unlisted may not modify; list it in a // @Modifies clause, as dst`
}

// The two slices of one element type are separate unless the caller says
// otherwise, and a call with one slice twice is refused.
//
// @Requires |a| > 0
// @Modifies a
// @Ensures True
func Twice(a []int) {
	Copy(a, a) // want `the slices passed to Copy as dst and src may overlap`
}

// copy is not supported inside a larger expression.
//
// @Modifies dst
// @Ensures True
func Inside(dst, src []int) (n int) {
	return 1 + copy(dst, src) // want `cannot verify Inside: the built-in function copy is not supported yet here; copy is supported as a statement, as the whole right-hand side of an assignment, or as a returned value`
}

// Nor beside a call in the target.
//
// @Ensures r = 0
func zero() (r int) { return 0 }

// @Requires |dst| > 0 And |out| > 0
// @Modifies dst, out
// @Ensures True
func BesideCall(dst, src, out []int) {
	out[zero()] = copy(dst, src) // want `cannot verify BesideCall: copy is supported as the whole right-hand side of an assignment only when its target calls nothing; assign to a local variable first`
}

// Slices of other element types.
//
// @Modifies dst
// @Ensures True
func Strings(dst, src []string) {
	copy(dst, src) // want `cannot verify Strings: copy of a slice of string is not supported yet; copy is supported for slices of numbers and booleans, and from a string into a \[\]byte; write the copy as a loop that assigns each element`
}

type point struct{ x int }

// @Modifies dst
// @Ensures True
func Points(dst, src []point) {
	copy(dst, src) // want `cannot verify Points: copy of a slice of copies.point is not supported yet`
}

// @Modifies dst
// @Ensures True
func Pointers(dst, src []*point) {
	copy(dst, src) // want `cannot verify Pointers: copy of a slice of \*copies.point is not supported yet`
}

// The loop's invariant is broken by a copy that writes the wrong element.
//
// @Requires |dst| = 4 And |src| = 4
// @Modifies dst
// @Ensures True
func InLoopWrong(dst, src []int) {
	// @Invariant 0 <= i <= 4
	// @Invariant Forall k in [0, i) : dst[k] = src[k]
	for i := range 4 { // want `loop invariant may not be preserved: Forall k in \[0, i\) : dst\[k\] = src\[k\]`
		copy(dst[i:i+1], src[3-i:4-i])
	}
}

// The decoder's slice may lie in its own array, and then the copy moves
// the array's elements down.
//
// @Ensures r = 1
func RefillOverlapWrong() (r byte) {
	var d decoder
	d.arr[0], d.arr[1] = 1, 2
	d.in = d.arr[1:3]
	copy(d.arr[:], d.in)
	return d.arr[0] // want `postcondition may not hold: r = 1`
}

// Refill requires its slice apart from its array.
//
// @Ensures True
func RefillOverlapCall() {
	var d decoder
	d.in = d.arr[1:3]
	d.Refill() // want `precondition of Refill may not hold: apart\(d.in, d.arr\)`
}

// A loop that copies into dst changes it.
//
// @Requires |dst| = 4 And |src| = 4 And src[0] != dst[0]
// @Modifies dst
// @Ensures dst'[0] = dst[0]
func LoopForgets(dst, src []int) {
	// @Invariant 0 <= i <= 4
	for i := range 4 {
		copy(dst[i:i+1], src[i:i+1])
	}
} // want `postcondition may not hold: dst'\[0\] = dst\[0\]`
