package guide

// The programs of the section on variadic functions.

// Largest returns the largest of its arguments.
//
// @Ensures m >= first
// @Ensures Forall i in [0, |rest|) : m >= rest[i]
func Largest(first int, rest ...int) (m int) {
	m = first
	// @Invariant 0 <= i <= |rest|
	// @Invariant m >= first
	// @Invariant Forall j in [0, i) : m >= rest[j]
	// @Variant |rest| - i
	for i := 0; i < len(rest); i++ {
		if rest[i] > m {
			m = rest[i]
		}
	}
	return m
}

// @Ensures m >= 7
func AtLeastSeven(x int) (m int) {
	return Largest(7, x, 3)
}

// @Requires |xs| > 0
// @Modifies xs
// @Ensures xs'[0] = 0
func ClearFirst(xs ...int) {
	xs[0] = 0
}

// @Requires |xs| > 0
func ClearAll(xs []int) {
	ClearFirst(xs...) // want `vego:\ ClearFirst\ may\ modify\ xs\.\.\.,\ which\ ClearAll\ may\ not\ modify;\ list\ it\ in\ a`
}
