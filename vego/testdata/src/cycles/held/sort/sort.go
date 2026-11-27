// Package sort hands a comparison to slices.SortFunc from a trusted
// function of the package (h2, F2 of the review of the design of F43). The
// graph walks the body of Sort, which nobody verifies, and skipped the
// value it hands under calls, so G and CmpBack verified and a program that
// set the hook to CmpBack ran out of stack.
package sort

import "slices"

// T is sorted.
type T struct{ N int }

// Cmp compares two Ts.
//
// @Ensures True
type Cmp func(a, b T) (r int)

// hook is set by SetHook.
var hook Cmp

// SetHook is not verified.
func SetHook(c Cmp) { hook = c }

// Sort is trusted: its entry is in testdata/trusted.yaml.
func Sort(xs []T, c Cmp) {
	slices.SortFunc(xs, c)
}

// G sorts two values with the hook.
//
// @Variant 0
// @Ensures True
func G(a, b T) (n int) {
	if hook != nil {
		Sort([]T{a, b}, hook) // want `Sort is trusted and calls back into G, so that this call ends cannot be proved; verify Sort instead of trusting it; the cycle: G calls Sort at sort.go:\d+:\d+, Sort hands c to slices.SortFunc\(xs, c\)`
	}
	return 0
}

// CmpBack calls G.
//
// @Variant 1
// @Ensures True
func CmpBack(a, b T) (r int) {
	return G(a, b) // want `this call may not end: CmpBack calls G at sort.go:\d+:\d+, G calls Sort at sort.go:\d+:\d+, Sort hands c to slices\.SortFunc\(xs, c\) at sort.go:\d+:\d+, which may run CmpBack`
}
