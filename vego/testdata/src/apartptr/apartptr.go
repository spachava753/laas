// Package apartptr says where a pointer to a number points with apart and
// within (F42, D3 and D4): apart is assumed on entry and proved at every
// verified call, as apart of two slices is.
package apartptr

// S holds a number that a pointer can point to.
type S struct {
	n, m int
}

// Ptr hands out a pointer to n, which makes n a field a pointer can point
// to.
//
// @Requires s != nil
// @Ensures r != nil And within(r, s)
func (s *S) Ptr() (r *int) {
	return &s.n
}

// Keep writes what p points to and keeps s.n, since p does not point into
// s.
//
// @Requires p != nil And s != nil And apart(p, s)
// @Modifies p
// @Ensures s.n' = s.n
func Keep(p *int, s *S) {
	*p = 7
}

// KeepOther hands Keep a pointer into another struct.
//
// @Requires s != nil
// @Ensures r = s.n
func KeepOther(s *S) (r int) {
	t := &S{}
	Keep(&t.n, s)
	return s.n
}

// KeepSame hands Keep a pointer into the struct itself.
//
// @Requires s != nil
// @Ensures True
func KeepSame(s *S) {
	Keep(&s.n, s) // want `vego: precondition of Keep may not hold: apart\(p, s\)`
}

// First writes the first element and what p points to, which is not in xs.
//
// @Requires p != nil And |xs| > 0 And apart(p, xs)
// @Modifies p, xs
// @Ensures xs'[0] = 1 And *p' = 2
func First(p *int, xs []int) {
	xs[0] = 1
	*p = 2
}

// FirstLocal hands First a variable of its own.
//
// @Requires |xs| > 0
// @Modifies xs
// @Ensures xs'[0] = 1 And r = 2
func FirstLocal(xs []int) (r int) {
	x := 0
	First(&x, xs)
	return x
}

// FirstElement hands First an element of xs.
//
// @Requires |xs| > 1
// @Modifies xs
// @Ensures True
func FirstElement(xs []int) {
	First(&xs[1], xs) // want `vego: precondition of First may not hold: apart\(p, xs\)`
}

// Two writes through two pointers that do not point to one number.
//
// @Requires p != nil And q != nil And apart(p, q)
// @Modifies p, q
// @Ensures *p' = 1 And *q' = 2
func Two(p, q *int) {
	*p = 1
	*q = 2
}

// TwoSame hands Two one number twice.
//
// @Ensures True
func TwoSame() {
	x := 0
	Two(&x, &x) // want `vego: precondition of Two may not hold: apart\(p, q\)`
}

// Into writes through a pointer within s, which Modifies s covers.
//
// @Requires s != nil And within(p, s)
// @Modifies s
// @Ensures s.m' = s.m
func Into(p *int, s *S) {
	*p = 3
}

// IntoWrong claims the field p points to unchanged.
//
// @Requires s != nil And within(p, s) And s.n < 100
// @Modifies s
// @Ensures s.n' = s.n
func IntoWrong(p *int, s *S) {
	*p = s.n + 1
} // want `vego: postcondition may not hold: s\.n' = s\.n`

// Element writes through a pointer within xs, which Modifies xs covers.
//
// @Requires within(p, xs)
// @Modifies xs
// @Ensures True
func Element(p *int, xs []int) {
	*p = 4
}
