// Package audit holds correct functions whose specifications range from too
// weak to tight, to exercise the specification audit.
package audit

// Manhattan has the contract the VeGo paper criticises: non-negativity alone
// does not tie the result to the coordinates.
//
// @ Requires -1000000 <= x1 <= 1000000 And -1000000 <= x2 <= 1000000
// @ Requires -1000000 <= y1 <= 1000000 And -1000000 <= y2 <= 1000000
func Manhattan(x1, y1, x2, y2 int) (d int) { // want `vego:\ specification\ of\ Manhattan\ has\ a\ hole\ \[CONSTANT\]:\ it\ also\ accepts\ an\ implementation\ that\ returns\ the\ constant\ 1\ and\ changes\ nothing` `vego:\ specification\ of\ Manhattan\ has\ a\ hole\ \[VACUOUS\]:\ it\ also\ accepts\ an\ implementation\ that\ returns\ zero\ values\ and\ changes\ nothing`
	dx, dy := x1-x2, y1-y2
	if dx < 0 {
		dx = -dx
	}
	if dy < 0 {
		dy = -dy
	}
	return dx + dy
}

//@ Ensures d >= 0

// Distance pins the result down completely.
//
// @ Requires -1000000 <= a <= 1000000 And -1000000 <= b <= 1000000
func Distance(a, b int) (d int) {
	if a < b {
		return b - a
	}
	return a - b
}

//@ Ensures d >= 0 And (d = a - b Or d = b - a)

// Contains only promises something when it answers true, like the saddleback
// search of the paper.
func Contains(A []int, target int) (found bool) { // want `vego:\ specification\ of\ Contains\ has\ a\ hole\ \[VACUOUS\]:\ it\ also\ accepts\ an\ implementation\ that\ returns\ zero\ values\ and\ changes\ nothing`
	//@ Invariant target != A[0:i)
	for i := range A {
		if A[i] == target {
			return true
		}
	}
	return false
}

//@ Ensures found = True -> Exists k in [0, |A|) : A[k] = target

// ContainsExactly closes that hole with the other direction.
func ContainsExactly(A []int, target int) (found bool) {
	//@ Invariant target != A[0:i)
	for i := range A {
		if A[i] == target {
			return true
		}
	}
	return false
}

//@ Ensures found = True <-> Exists k in [0, |A|) : A[k] = target

//@ Predicate ascending(A) ::= Forall i in [0, |A|) : Forall j in [i, |A|) : A[i] <= A[j]

// Sort promises a sorted slice but not that it holds the input's elements.
func Sort(A []int) { // want `vego:\ specification\ of\ Sort\ has\ a\ hole\ \[CONSTANT\]:\ it\ also\ accepts\ an\ implementation\ that\ fills\ its\ slices\ with\ zero\ values` `vego:\ specification\ of\ Sort\ has\ a\ hole\ \[OBLIVIOUS\]:\ it\ also\ accepts\ an\ implementation\ that\ fills\ its\ slices\ with\ 0,\ 1,\ 2,\ \.\.\.\ whatever\ the\ input`
	//@ Invariant 0 <= i <= |A|
	//@ Invariant Forall p in [0, i) : Forall q in [p, |A|) : A[p] <= A[q]
	//@ Variant |A| - i
	for i := 0; i < len(A); i++ {
		least := i
		//@ Invariant i <= least < j <= |A|
		//@ Invariant Forall q in [i, j) : A[least] <= A[q]
		//@ Variant |A| - j
		for j := i + 1; j < len(A); j++ {
			if A[j] < A[least] {
				least = j
			}
		}
		A[i], A[least] = A[least], A[i]
	}
}

//@ Ensures ascending(A')

// Clamp bounds x from above; returning x itself is ruled out by the contract.
//
// @ Requires limit >= 0
func Clamp(x, limit int) (y int) {
	return min(x, limit)
}

//@ Ensures y <= limit And y <= x And (y = x Or y = limit)

// Tail drops the first element but its contract only bounds the length.
//
// @ Requires |A| > 0
func Tail(A []int) (R []int) { // want `vego:\ specification\ of\ Tail\ has\ a\ hole\ \[CONSTANT\]:\ it\ also\ accepts\ an\ implementation\ that\ fills\ its\ slices\ with\ zero\ values` `vego:\ specification\ of\ Tail\ has\ a\ hole\ \[MINIMAL\ CONSTRUCTOR\]:\ it\ also\ accepts\ an\ implementation\ that\ returns\ its\ argument\ A\ unchanged` `vego:\ specification\ of\ Tail\ has\ a\ hole\ \[OBLIVIOUS\]:\ it\ also\ accepts\ an\ implementation\ that\ fills\ its\ slices\ with\ 0,\ 1,\ 2,\ \.\.\.\ whatever\ the\ input` `vego:\ specification\ of\ Tail\ has\ a\ hole\ \[VACUOUS\]:\ it\ also\ accepts\ an\ implementation\ that\ returns\ zero\ values\ and\ changes\ nothing`
	R = make([]int, len(A)-1)
	//@ Invariant |R| = |A| - 1 And Forall k in [0, i) : R[k] = A[k+1]
	for i := range len(A) - 1 {
		R[i] = A[i+1]
	}
	return R
}

//@ Ensures |R| <= |A|

// SetSecond has a contract that only bites because b keeps its own length;
// a candidate that gave b the length of a would report a false hole.
//
// @ Requires |a| = 1 And |b| = 2
func SetSecond(a, b []int) {
	b[0] = 1
}

//@ Ensures |b'| != |a| -> b'[0] = 1

// Halve has a weak contract, but not one that -1 could satisfy: an unsigned
// result has no negative values, so that candidate must not be reported.
func Halve(x uint) (y uint) { // want `vego:\ specification\ of\ Halve\ has\ a\ hole\ \[CONSTANT\]:\ it\ also\ accepts\ an\ implementation\ that\ returns\ the\ constant\ 1\ and\ changes\ nothing` `vego:\ specification\ of\ Halve\ has\ a\ hole\ \[MINIMAL\ CONSTRUCTOR\]:\ it\ also\ accepts\ an\ implementation\ that\ returns\ its\ argument\ x\ unchanged`
	return x / 2
}

//@ Ensures y != 0 Or x < 2

// Shrink returns an int8. Returning the int argument unchanged is not an
// implementation, because it does not fit.
func Shrink(x int) (y int8) { // want `vego:\ specification\ of\ Shrink\ has\ a\ hole\ \[CONSTANT\]:\ it\ also\ accepts\ an\ implementation\ that\ returns\ the\ constant\ \-1\ and\ changes\ nothing` `vego:\ specification\ of\ Shrink\ has\ a\ hole\ \[CONSTANT\]:\ it\ also\ accepts\ an\ implementation\ that\ returns\ the\ constant\ 1\ and\ changes\ nothing`
	if x < 0 {
		return -1
	}
	return 1
}

//@ Ensures y != 0

// SetLast cannot be imitated by counting 0, 1, 2, ...: a byte cannot hold 299.
//
// @ Requires |a| = 300
func SetLast(a []byte, x byte) {
	a[299] = x
}

//@ Ensures a'[299] = x Or a'[299] = 299

// SetLastShort can: every index of a slice of 100 bytes fits a byte.
//
// @ Requires |a| = 100
func SetLastShort(a []byte, x byte) { // want `vego:\ specification\ of\ SetLastShort\ has\ a\ hole\ \[OBLIVIOUS\]:\ it\ also\ accepts\ an\ implementation\ that\ fills\ its\ slices\ with\ 0,\ 1,\ 2,\ \.\.\.\ whatever\ the\ input`
	a[99] = x
}

//@ Ensures a'[99] = x Or a'[99] = 99

// Update returns a string. A string of 300 bytes cannot hold 299 at its end,
// so the counting candidate must not be reported.
//
// @ Requires |a| = 300 And a[0] = 1
func Update(a []int, x string) string {
	a[0] = 0
	return x
}

//@ Ensures a'[0] = 0 And (result = x Or (|result| = 300 And result[299] = 299))
