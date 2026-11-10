// Package paper holds the listings of the VeGo paper.
package paper

// Divide computes quotient and remainder by repeated subtraction.
//
// @ Requires n >= 0 And d > 0
func Divide(n, d int) (q, r int) {
	q, r = 0, n
	//@ Invariant n >= 0 And d > 0 And n = d*q + r And 0 <= r
	//@ Variant r
	for d <= r {
		q, r = q+1, r-d
	}
	return q, r
}

//@ Ensures n = d*q + r And 0 <= r And r < d

//@ Predicate sumTo(A, i, s) ::= ((i <= 0 -> s = 0) And
//@ (i > 0 -> Exists t in Z : (sumTo(A, i-1, t) And s = t + A[i-1])))

//@ Predicate bounded(A) ::= |A| <= 1000000 And
//@   Forall k in [0, |A|) : (-1000000 <= A[k] And A[k] <= 1000000)

// SumLoop adds up a slice from left to right. The bound on the elements is
// not in the paper: without it the sum can overflow.
//
// @ Requires bounded(A)
func SumLoop(A []int) (s int) {
	s = 0
	//@ Invariant 0 <= i And i <= |A| And sumTo(A, i, s)
	//@ Invariant -1000000*i <= s And s <= 1000000*i
	//@ Variant |A| - i
	for i := 0; i < len(A); i++ {
		s = s + A[i]
	}
	return s
}

//@ Ensures sumTo(A, |A|, s)

//@ Predicate sumRecPred(A, i, s) ::= ((i >= |A| -> s = 0) And
//@ (i < |A| -> Exists t in Z : (sumRecPred(A, i+1, t) And s = t + A[i])))

// SumRec adds up a slice recursively.
//
// @ Requires 0 <= i And i <= |A|
// @ Requires bounded(A)
// @ Measure |A| - i
func SumRec(A []int, i int) (s int) {
	if i >= len(A) {
		return 0
	}
	t := SumRec(A, i+1)
	return t + A[i]
}

//@ Ensures sumRecPred(A, i, s)
//@ Ensures -1000000*(|A|-i) <= s And s <= 1000000*(|A|-i)
