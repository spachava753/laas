package trialfaults

// A nil slice has no length and no capacity.
//
// @Ensures n = 0
func NilLen(a []int) (n int) {
	if a == nil {
		return len(a)
	}
	return 0
}

// @Ensures n = 0
func NilCap(a []byte) (n int) {
	if a == nil {
		return cap(a)
	}
	return 0
}

// Holder holds a slice.
type Holder struct{ items []int }

// @Requires h != nil
// @Ensures n = 0
func NilField(h *Holder) (n int) {
	if h.items == nil {
		return len(h.items)
	}
	return 0
}

// A slice that is not nil may still be empty.
//
// @Ensures n > 0
func NotNilLen(a []int) (n int) {
	if a != nil {
		return len(a) // want `postcondition may not hold: n > 0`
	}
	return 1
}

// An empty slice need not be nil.
//
// @Ensures r
func EmptyIsNil(a []int) (r bool) {
	if len(a) == 0 {
		return a == nil // want `postcondition may not hold: r`
	}
	return true
}
