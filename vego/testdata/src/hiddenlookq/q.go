// Package hiddenlookq is not verified. Look runs a method of what it is
// handed, which its entry says nothing of (F23 of the review of step 7 of
// F32).
package hiddenlookq

// Look calls x's Init when it has one.
func Look(x any) (r int) {
	if h, ok := x.(interface{ Init() }); ok {
		h.Init()
	}
	return 0
}
