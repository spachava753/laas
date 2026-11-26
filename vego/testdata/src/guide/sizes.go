package guide

import "strings"

// The section "Bounding what grows" of the guide: an append in a loop is
// reported without a bound, and verifies with one. guidesizes holds the
// same programs under a declared memory.

// @Ensures |out| = |xs|
func Upper(xs []string) (out []string) {
	// @Invariant 0 <= i <= |xs| And |out| = i
	// @Variant |xs| - i
	for i := 0; i < len(xs); i++ {
		out = append(out, strings.ToUpper(xs[i])) // want `vego: precondition of ToUpper may not hold: 6 \* \|s\| \+ 65544 <= MaxAlloc; it holds when \|xs\[i\]\| <= 10000000000000; or, if the machines the program runs on never hold 256GB of its data at once, declare that under sizes in vego-trusted.yaml, which proves this` `vego: the slice that append grows may be more than can be allocated, or have a capacity an int cannot hold; or, if the machines the program runs on never hold 256GB of its data at once, declare that under sizes in vego-trusted.yaml, which proves this`
	}
	return out
}

// @Requires |xs| <= 1000000
// @Requires Forall i in [0, |xs|) : |xs[i]| <= 1000000
// @Ensures |out| = |xs|
func UpperBounded(xs []string) (out []string) {
	// @Invariant 0 <= i <= |xs| And |out| = i
	// @Variant |xs| - i
	for i := 0; i < len(xs); i++ {
		out = append(out, strings.ToUpper(xs[i]))
	}
	return out
}
