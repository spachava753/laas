// Package trialfaults holds the faults that the trial on real code found,
// each with a program that verifies and a defective one that is refused.
package trialfaults

// An Assert after the last statement of a case clause is checked in that
// clause, as one at the end of an if block is.
//
// @Ensures True
func EndOfCase(x int) (r int) {
	switch {
	case x > 0:
		r = 1
		// @Assert r = 1
	}
	return r
}

// @Ensures True
func EndOfCaseThenDefault(x int) (r int) {
	switch {
	case x > 0:
		r = 1
		// @Assert r = 1
	default:
		r = 2
		// @Assert r = 2
	}
	return r
}

// A variable declared in the clause is in scope there.
//
// @Requires 0 <= n <= 100
// @Ensures True
func DeclaredInCase(k, n int) (r int) {
	switch k {
	case 1:
		m := n + 1
		r = m
		// @Assert m > n
	}
	return r
}

// An empty clause holds its annotation too.
//
// @Ensures True
func EmptyCase(x int) (r int) {
	switch {
	case x > 0:
		// @Assert x > 0
	}
	return r
}

// @Ensures True
func WrongAtEndOfCase(x int) (r int) {
	switch {
	case x > 0:
		r = 1
		// @Assert r = 2 // want `assertion may not hold: r = 2`
	default:
		r = 2
		// @Assert r = 1 // want `assertion may not hold: r = 1`
	}
	return r
}

// The Assert holds in the clause it follows and not in the next one.
//
// @Ensures True
func WrongClause(x int) (r int) {
	switch x {
	case 1:
		r = 1
		// @Assert x = 1
	case 2:
		r = 2
		// @Assert x = 1 // want `assertion may not hold: x = 1`
	}
	return r
}
