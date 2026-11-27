// Package interior holds ordinary programs that take the address of a
// number inside a struct, a slice, or an array (F42).
package interior

// Stats counts hits and misses.
type Stats struct {
	hits, misses int
}

// inc increments what p points to.
//
// @Requires p != nil And *p < 1000
// @Modifies p
// @Ensures *p' = *p + 1
func inc(p *int) {
	*p++
}

// Hit counts a hit through a pointer to the field, and keeps the misses.
//
// @Requires s != nil And s.hits < 1000
// @Modifies s.hits
// @Ensures s.hits' = s.hits + 1 And s.misses' = s.misses
func (s *Stats) Hit() {
	inc(&s.hits)
}

// Both counts a hit and a miss through two pointers into one struct.
//
// @Requires s != nil And s.hits < 1000 And s.misses < 1000
// @Modifies s
// @Ensures s.hits' = s.hits + 1 And s.misses' = s.misses + 1
func (s *Stats) Both() {
	p, q := &s.hits, &s.misses
	*p++
	*q++
}

// Zero sets every element through a pointer to it.
//
// @Modifies xs
// @Ensures Forall i in [0, |xs|) : xs'[i] = 0
func Zero(xs []int) {
	// @Invariant 0 <= i <= |xs| And Forall j in [0, i) : xs[j] = 0
	for i := range xs {
		p := &xs[i]
		*p = 0
	}
}

// swap exchanges what p and q point to, which may be one number.
//
// @Requires p != nil And q != nil
// @Modifies p, q
// @Ensures *p' = *q And *q' = *p
func swap(p, q *int) {
	*p, *q = *q, *p
}

// SwapFirst exchanges the first two elements of a slice.
//
// @Requires |xs| >= 2
// @Modifies xs
// @Ensures xs'[0] = xs[1] And xs'[1] = xs[0]
func SwapFirst(xs []int) {
	swap(&xs[0], &xs[1])
}

// SwapArray exchanges two elements of an array through pointers to them.
//
// @Requires 0 <= i < 4 And 0 <= j < 4
// @Ensures r[i] = a[j] And r[j] = a[i]
func SwapArray(a [4]int, i, j int) (r [4]int) {
	swap(&a[i], &a[j])
	return a
}
