// Package unsafeassumed never takes the address of S.n, so the field
// keeps a region of its own and Keep verifies. That rests on the
// assumption that code which is not verified does not use unsafe or
// reflect to make a pointer to a field of a struct of another package that
// the language would not let it name; unsafeassumedq breaks it, which its
// run_test.go shows.
package unsafeassumed

// S holds two numbers.
type S struct {
	m int
	n int
}

// Keep writes what p points to and claims s.n unchanged.
//
// @Requires p != nil And s != nil
// @Modifies p
// @Ensures s.n' = s.n
func Keep(p *int, s *S) {
	*p = 7
}

// N reads n.
//
// @Requires s != nil
// @Ensures r = s.n
func N(s *S) (r int) {
	return s.n
}
