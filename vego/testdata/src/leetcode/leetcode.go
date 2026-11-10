// Package leetcode pairs fully specified solutions of classic problems with
// defective variants, after the dual corpus of the VeGo paper.
package leetcode

// TwoSum (LC 1) finds two distinct positions whose values add up to target.
// The element bound is the one the problem statement gives.
//
// @ Requires Forall k in [0, |A|) : (-1000000000 <= A[k] And A[k] <= 1000000000)
func TwoSum(A []int, target int) (i, j int, found bool) {
	//@ Invariant 0 <= a <= |A|
	//@ Invariant Forall p in [0, a) : Forall q in (p, |A|) : A[p] + A[q] != target
	//@ Variant |A| - a
	for a := 0; a < len(A); a++ {
		//@ Invariant a < b <= |A|
		//@ Invariant Forall q in (a, b) : A[a] + A[q] != target
		//@ Variant |A| - b
		for b := a + 1; b < len(A); b++ {
			if A[a]+A[b] == target {
				return a, b, true
			}
		}
	}
	return 0, 0, false
}

//@ Ensures found = True -> (0 <= i < j < |A| And A[i] + A[j] = target)
//@ Ensures found = False -> Forall p in [0, |A|) : Forall q in (p, |A|) : A[p] + A[q] != target

// TwoSumSameIndex reuses one index, a classic defect.
//
// @ Requires Forall k in [0, |A|) : (-1000000000 <= A[k] And A[k] <= 1000000000)
func TwoSumSameIndex(A []int, target int) (i, j int, found bool) {
	//@ Invariant 0 <= a <= |A|
	//@ Variant |A| - a
	for a := 0; a < len(A); a++ {
		//@ Invariant a <= b <= |A|
		//@ Variant |A| - b
		for b := a; b < len(A); b++ {
			if A[a]+A[b] == target {
				return a, b, true // want `vego:\ postcondition\ may\ not\ hold:\ found\ =\ True\ \->\ \(0\ <=\ i\ <\ j\ <\ \|A\|\ And\ A\[i\]\ \+\ A\[j\]\ =\ target\)`
			}
		}
	}
	return 0, 0, false
}

//@ Ensures found = True -> (0 <= i < j < |A| And A[i] + A[j] = target)

//@ Predicate ascending(A) ::= Forall i in [0, |A|) : Forall j in [i, |A|) : A[i] <= A[j]

// RemoveDuplicates (LC 26) compacts a sorted slice in place and returns the
// number of distinct values, which end up strictly increasing at the front.
//
// @ Requires ascending(A)
func RemoveDuplicates(A []int) (k int) {
	if len(A) == 0 {
		return 0
	}
	k = 1
	//@ Invariant 1 <= k <= i <= |A|
	//@ Invariant Forall p in [0, k) : Forall q in (p, k) : A[p] < A[q]
	//@ Invariant Forall q in [i, |A|) : A[k-1] <= A[q]
	//@ Invariant Forall p in [i, |A|) : Forall q in [p, |A|) : A[p] <= A[q]
	//@ Variant |A| - i
	for i := 1; i < len(A); i++ {
		if A[i] != A[k-1] {
			A[k] = A[i]
			k++
		}
	}
	return k
}

//@ Ensures 0 <= k <= |A|
//@ Ensures Forall p in [0, k) : Forall q in (p, k) : A'[p] < A'[q]

// RemoveDuplicatesOffByOne writes one slot too far.
//
// @ Requires ascending(A)
func RemoveDuplicatesOffByOne(A []int) (k int) {
	if len(A) == 0 {
		return 0
	}
	k = 1
	//@ Invariant 1 <= k <= i <= |A|
	//@ Variant |A| - i
	for i := 1; i < len(A); i++ {
		if A[i] != A[k-1] {
			k++
			A[k] = A[i] // want `vego:\ index\ may\ be\ out\ of\ range`
		}
	}
	return k
}

// MaxProfit (LC 121) returns the best profit from one purchase followed by
// one sale.
//
// @ Requires Forall k in [0, |prices|) : (0 <= prices[k] And prices[k] <= 10000)
func MaxProfit(prices []int) (profit int) {
	if len(prices) == 0 {
		return 0
	}
	lowest := prices[0]
	//@ Invariant 1 <= i <= |prices| And profit >= 0
	//@ Invariant Forall p in [0, i) : lowest <= prices[p]
	//@ Invariant 0 <= lowest <= 10000
	//@ Invariant Forall p in [0, i) : Forall q in [p, i) : prices[q] - prices[p] <= profit
	//@ Variant |prices| - i
	for i := 1; i < len(prices); i++ {
		profit = max(profit, prices[i]-lowest)
		lowest = min(lowest, prices[i])
	}
	return profit
}

//@ Ensures profit >= 0
//@ Ensures Forall p in [0, |prices|) : Forall q in [p, |prices|) : prices[q] - prices[p] <= profit

// MaxProfitInverted sells before it buys.
//
// @ Requires Forall k in [0, |prices|) : (0 <= prices[k] And prices[k] <= 10000)
func MaxProfitInverted(prices []int) (profit int) {
	if len(prices) == 0 {
		return 0
	}
	highest := prices[0]
	//@ Invariant 1 <= i <= |prices| And profit >= 0 And 0 <= highest <= 10000
	//@ Invariant Forall p in [0, i) : Forall q in [p, i) : prices[q] - prices[p] <= profit
	//@ Variant |prices| - i
	for i := 1; i < len(prices); i++ { // want `vego:\ loop\ invariant\ may\ not\ be\ preserved:\ Forall\ p\ in\ \[0,\ i\)\ :\ Forall\ q\ in\ \[p,\ i\)\ :\ prices\[q\]\ \-\ prices\[p\]\ <=\ profit`
		profit = max(profit, highest-prices[i])
		highest = max(highest, prices[i])
	}
	return profit
}

//@ Ensures Forall p in [0, |prices|) : Forall q in [p, |prices|) : prices[q] - prices[p] <= profit

// Search (LC 704) is binary search with an inclusive upper bound.
//
// @ Requires ascending(A)
func Search(A []int, target int) (index int) {
	lo, hi := 0, len(A)-1
	//@ Invariant 0 <= lo And hi < |A| And lo <= hi + 1
	//@ Invariant A[0:lo) < target And target < A[hi+1:|A|)
	//@ Variant hi - lo + 1
	for lo <= hi {
		mid := lo + (hi-lo)/2
		switch {
		case A[mid] == target:
			return mid
		case A[mid] < target:
			lo = mid + 1
		default:
			hi = mid - 1
		}
	}
	return -1
}

//@ Ensures index = -1 Or (0 <= index < |A| And A[index] = target)
//@ Ensures index = -1 -> target != A[0:|A|)

// SearchStagnates never moves the lower bound past mid.
//
// @ Requires ascending(A)
func SearchStagnates(A []int, target int) (index int) {
	lo, hi := 0, len(A)-1
	//@ Invariant 0 <= lo And hi < |A| And lo <= hi + 1
	//@ Variant hi - lo + 1
	for lo <= hi { // want `vego:\ loop\ variant\ may\ not\ decrease:\ hi\ \-\ lo\ \+\ 1`
		mid := lo + (hi-lo)/2
		switch {
		case A[mid] == target:
			return mid
		case A[mid] < target:
			lo = mid
		default:
			hi = mid - 1
		}
	}
	return -1
}

// SelectionSort sorts in place by repeatedly selecting the minimum.
func SelectionSort(A []int) {
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

// Partition moves the elements below pivot to the front (Dutch flag, two
// colours) and returns the boundary.
func Partition(A []int, pivot int) (boundary int) {
	//@ Invariant 0 <= boundary <= i <= |A|
	//@ Invariant A[0:boundary) < pivot And A[boundary:i) >= pivot
	//@ Variant |A| - i
	for i := 0; i < len(A); i++ {
		if A[i] < pivot {
			A[i], A[boundary] = A[boundary], A[i]
			boundary++
		}
	}
	return boundary
}

//@ Ensures 0 <= boundary <= |A|
//@ Ensures A'[0:boundary) < pivot And A'[boundary:|A|) >= pivot
