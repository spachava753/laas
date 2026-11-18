// Package twovariants has a function with two variants, one of which is
// dropped. The function is not what its author wrote, so its contract may
// not be relied on from elsewhere.
package twovariants

// Down counts down.
//
// @Requires n >= 0
// @Variant n + 5
// @Variant n // want `vego: function Down already has a Variant`
// @Ensures r = 0
func Down(n int) (r int) {
	if n == 0 {
		return 0
	}
	return Down(n - 1)
}
