// Package defects holds routines whose code or specification is wrong.
package defects

// @ Requires n >= 0 And d > 0
func DivideOffByOne(n, d int) (q, r int) {
	q, r = 0, n
	//@ Invariant n = d*q + r And 0 <= r
	//@ Variant r
	for d < r {
		q, r = q+1, r-d
	}
	return q, r // want `vego:\ postcondition\ may\ not\ hold:\ r\ <\ d`
}

//@ Ensures n = d*q + r And 0 <= r And r < d

// @ Requires n >= 0
func DivideMayNotTerminate(n, d int) (q, r int) {
	q, r = 0, n
	//@ Invariant n = d*q + r And 0 <= r
	//@ Variant r
	for d <= r { // want `vego:\ loop\ variant\ may\ not\ decrease:\ r`
		q, r = q+1, r-d // want `vego:\ addition\ may\ overflow\ int` `vego:\ subtraction\ may\ overflow\ int`
	}
	return q, r
}

func AbsWrong(x int) (y int) {
	return x // want `vego:\ postcondition\ may\ not\ hold:\ y\ >=\ 0`
}

//@ Ensures y >= 0

func SearchOutOfRange(A []int, target int) (index int) {
	//@ Invariant 0 <= i
	//@ Variant |A| - i + 1
	for i := 0; i <= len(A); i++ {
		if A[i] == target { // want `vego:\ index\ may\ be\ out\ of\ range`
			return i
		}
	}
	return -1
}

func NegativeIndex(A []int, i int) int {
	//@ Assert True
	if i < len(A) {
		return A[i] // want `vego:\ index\ may\ be\ negative`
	}
	return 0
}

// @ Requires 0 <= lo <= hi <= |A|
func BinarySearchStuck(A []int, target, lo, hi int) (index int) {
	//@ Invariant 0 <= lo <= hi <= |A|
	//@ Variant hi - lo
	for lo < hi { // want `vego:\ loop\ variant\ may\ not\ decrease:\ hi\ \-\ lo`
		mid := lo + (hi-lo)/2
		if A[mid] < target {
			lo = mid
		} else {
			hi = mid
		}
	}
	return lo
}

func DivisionByZero(a, b int) (q int) {
	return a / b // want `vego:\ possible\ division\ by\ zero` `vego:\ postcondition\ may\ not\ hold:\ q\*b\ <=\ a` `vego:\ division\ may\ overflow\ int`
}

//@ Ensures q*b <= a

func InvariantNotPreserved(n int) (s int) {
	//@ Invariant s <= 10
	//@ Variant n - i
	for i := 0; i < n; i++ { // want `vego:\ loop\ invariant\ may\ not\ be\ preserved:\ s\ <=\ 10`
		s += i // want `vego:\ addition\ may\ overflow\ int`
	}
	return s
}

func InvariantNotOnEntry(n int) (s int) {
	s = n
	//@ Invariant s >= 0
	//@ Variant s
	for s > 0 { // want `vego:\ loop\ invariant\ may\ not\ hold\ on\ entry:\ s\ >=\ 0`
		s--
	}
	return s
}

//@ Ensures s = 0

// @ Requires x > 0
func positive(x int) (y int) {
	return x
}

//@ Ensures y > 0

func CallBreaksPrecondition(x int) int {
	//@ Assert True
	return positive(x - 1) // want `vego:\ precondition\ of\ positive\ may\ not\ hold:\ x\ >\ 0` `vego:\ subtraction\ may\ overflow\ int`
}

// @ Requires n >= 0
func RecursionWithoutMeasure(n int) (r int) {
	if n == 0 {
		return 0
	}
	return RecursionWithoutMeasure(n - 1) // want `vego:\ recursive\ call\ needs\ a\ //@\ Measure\ annotation\ on\ RecursionWithoutMeasure\ to\ prove\ termination`
}

// @ Requires n >= 0
// @ Measure n
func RecursionGrows(n int) (r int) {
	if n == 0 {
		return 0
	}
	return RecursionGrows(n + 1) // want `vego:\ measure\ may\ not\ decrease\ in\ recursive\ call:\ n` `vego:\ addition\ may\ overflow\ int`
}

// @ Requires n >= 0
func ReachablePanic(n int) int {
	if n > 100 {
		panic("too large") // want `vego:\ panic\ may\ be\ reachable`
	}
	return n
}

func AssertFails(x int) int {
	y := x * x // want `vego:\ multiplication\ may\ overflow\ int`
	//@ Assert y > 0 // want `vego:\ assertion\ may\ not\ hold:\ y\ >\ 0`
	return y
}

func EnsuresFalse(x int) (y int) {
	return x + 1 // want `vego:\ postcondition\ may\ not\ hold:\ False` `vego:\ addition\ may\ overflow\ int`
}

//@ Ensures False

func touch(A []int) {
	if len(A) > 0 {
		A[0] = 7
	}
}

// @ Requires |A| > 0 And A[0] = 1
func ForgetsAfterCall(A []int) (x int) {
	touch(A)
	return A[0] // want `vego:\ postcondition\ may\ not\ hold:\ x\ =\ 1`
}

//@ Ensures x = 1

// @ Requires |A| > 0
func EntryVersusExit(A []int) {
	A[0] = 5
} // want `vego:\ postcondition\ may\ not\ hold:\ A\[0\]\ =\ 5`

//@ Ensures A'[0] = 5
//@ Ensures A[0] = 5

func NegativeMake(n int) (R []int) {
	R = make([]int, n) // want `vego:\ make\ length\ may\ be\ negative`
	return R
}

//@ Ensures |R| = n

func RangeClaimsTooMuch(A []int) (n int) {
	//@ Invariant n = i
	for i := range A {
		n = i + 1
	}
	return n // want `vego:\ postcondition\ may\ not\ hold:\ n\ =\ \|A\|\ \+\ 1`
}

//@ Ensures n = |A| + 1

func NoVariant(n int) (i int) {
	//@ Invariant i <= n Or n < 0
	for i < n { // want `vego:\ loop\ needs\ a\ //@\ Variant\ annotation\ to\ prove\ that\ it\ terminates`
		i++
	}
	return i
}

func SortWrongWay(A []int) {
	//@ Invariant 1 <= i
	//@ Invariant Forall a in [0, i) : Forall b in [a, i) : b < |A| -> A[a] <= A[b]
	//@ Variant |A| - i
	for i := 1; i < len(A); i++ { // want `vego:\ loop\ invariant\ may\ not\ be\ preserved:\ Forall\ a\ in\ \[0,\ i\)\ :\ Forall\ b\ in\ \[a,\ i\)\ :\ b\ <\ \|A\|\ \->\ A\[a\]\ <=\ A\[b\]`
		j := i
		//@ Invariant 0 <= j <= i < |A|
		//@ Invariant Forall a in [0, i] : Forall b in [a, i] : (a != j And b != j) -> A[a] <= A[b]
		//@ Invariant Forall b in (j, i] : A[j] <= A[b]
		//@ Variant j
		for j > 0 && A[j-1] < A[j] { // want `vego:\ loop\ invariant\ may\ not\ be\ preserved:\ Forall\ b\ in\ \(j,\ i\]\ :\ A\[j\]\ <=\ A\[b\]`
			A[j-1], A[j] = A[j], A[j-1]
			j--
		}
	}
}

func FrameTooStrong(A []int, i int) {
	if 0 <= i && i < len(A) {
		A[i] = 0
	}
} // want `vego:\ postcondition\ may\ not\ hold:\ Forall\ k\ in\ \[0,\ \|A\|\)\ :\ A'\[k\]\ =\ A\[k\]`

//@ Ensures Forall k in [0, |A|) : A'[k] = A[k]

func ModSign(a int) (r int) {
	return a % 3 // want `vego:\ postcondition\ may\ not\ hold:\ 0\ <=\ r`
}

//@ Ensures 0 <= r And r < 3

func NonlinearGap(x, y int) (z int) {
	return x * y // want `vego:\ postcondition\ may\ not\ hold:\ z\ >=\ 0` `vego:\ multiplication\ may\ overflow\ int`
}

//@ Ensures z >= 0

func MinWrong(a, b int) (m int) {
	return min(a, b) // want `vego:\ postcondition\ may\ not\ hold:\ m\ =\ a`
}

//@ Ensures m = a

func BreakSkipsInvariantExit(A []int) (i int) {
	//@ Invariant 0 <= i <= |A|
	//@ Variant |A| - i
	for i < len(A) {
		if A[i] == 0 {
			break
		}
		i++
	}
	return i // want `vego:\ postcondition\ may\ not\ hold:\ i\ =\ \|A\|`
}

//@ Ensures i = |A|
