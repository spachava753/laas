// Package interiorattack is the design reviewer's attack program on interior
// pointers to single values (F42), with each claim it expects not to be
// proved shown false by run_test.go.
package interiorattack

// S holds two numbers.
type S struct{ a, b int }

// @Requires p != nil And *p < 1000
// @Modifies p
// @Ensures *p' = *p + 1
func Inc(p *int) {
	*p = *p + 1
}

// TwoFields is true: two interior pointers into one struct, written in turn.
//
// @Requires s != nil
// @Modifies s
// @Ensures s.a' = 1 And s.b' = 2
func TwoFields(s *S) {
	p, q := &s.a, &s.b
	*p = 1
	*q = 2
}

// TwoFieldsBack is true: the same, in the other order.
//
// @Requires s != nil
// @Modifies s
// @Ensures s.a' = 1 And s.b' = 2
func TwoFieldsBack(s *S) {
	q, p := &s.b, &s.a
	*q = 2
	*p = 1
}

// SameField is false: two pointers to one field.
//
// @Requires s != nil
// @Modifies s
// @Ensures s.a' = 1
func SameField(s *S) {
	p, q := &s.a, &s.a
	*p = 1
	*q = 2
} // want `vego: postcondition may not hold: s\.a' = 1`

// Aliased is false when p is &s.a.
//
// @Requires p != nil And s != nil
// @Modifies p, s
// @Ensures s.a' = 1
func Aliased(p *int, s *S) {
	s.a = 1
	*p = 2
} // want `vego: postcondition may not hold: s\.a' = 1`

// CallAliased is false: it hands Aliased &s.a and &s.
//
// @Ensures r = 1
func CallAliased() (r int) {
	var s S
	Aliased(&s.a, &s)
	return s.a
}

// IncA is true.
//
// @Requires s != nil And s.a < 100
// @Modifies s
// @Ensures s.a' = s.a + 1 And s.b' = s.b
func IncA(s *S) {
	Inc(&s.a)
}

// IncAOnly is false: it claims s.a unchanged.
//
// @Requires s != nil And s.a < 100
// @Modifies s
// @Ensures s.a' = s.a
func IncAOnly(s *S) {
	Inc(&s.a)
} // want `vego: postcondition may not hold: s\.a' = s\.a`

// IncANoModifies is refused: it writes s.a without listing s.
//
// @Requires s != nil And s.a < 100
// @Ensures True
func IncANoModifies(s *S) {
	Inc(&s.a) // want `vego: Inc may modify \&s\.a, which IncANoModifies may not modify; list it in a // @Modifies clause`
}

// ArrayElems is false when i = j.
//
// @Requires 0 <= i < 4 And 0 <= j < 4
// @Ensures r = 1
func ArrayElems(i, j int) (r int) {
	var a [4]int
	p, q := &a[i], &a[j]
	*p = 1
	*q = 2
	return *p // want `vego: postcondition may not hold: r = 1`
}

// ArrayElemsApart is true.
//
// @Requires 0 <= i < 4 And 0 <= j < 4 And i != j
// @Ensures r = 1
func ArrayElemsApart(i, j int) (r int) {
	var a [4]int
	p, q := &a[i], &a[j]
	*p = 1
	*q = 2
	return *p
}

// Swap swaps two numbers.
//
// @Requires p != nil And q != nil
// @Modifies p, q
// @Ensures *p' = *q And *q' = *p
func Swap(p, q *int) {
	*p, *q = *q, *p
}

// SwapElems is true.
//
// @Requires 0 <= i < |xs| And 0 <= j < |xs|
// @Modifies xs
// @Ensures xs'[i] = xs[j] And xs'[j] = xs[i]
func SwapElems(xs []int, i, j int) {
	Swap(&xs[i], &xs[j])
}

// KeptAcrossMove is false: the append moves, so p points to the old array.
//
// @Requires 0 < |xs| = cap(xs) And |xs| < 1000
// @Ensures r = 5
func KeptAcrossMove(xs []int) (r int) {
	p := &xs[0]
	xs = append(xs, 1)
	*p = 5 // want `vego: \*p is assigned, which KeptAcrossMove may not modify; list it in a // @Modifies clause, as `
	return xs[0]
}

// KeptInPlace is true: the append writes in place.
//
// @Requires 0 < |xs| < cap(xs)
// @Modifies xs
// @Ensures r = 5
func KeptInPlace(xs []int) (r int) {
	p := &xs[0]
	xs = append(xs, 1)
	*p = 5
	return xs[0]
}

// CopyBeside is false: t is a copy taken before the write.
//
// @Requires s != nil
// @Modifies s
// @Ensures r = 1
func CopyBeside(s *S) (r int) {
	t := *s
	p := &s.a
	*p = 1
	return t.a // want `vego: postcondition may not hold: r = 1`
}

// CopyBesideKept is true.
//
// @Requires s != nil
// @Modifies s
// @Ensures r = s.a And s.a' = 1
func CopyBesideKept(s *S) (r int) {
	t := *s
	p := &s.a
	*p = 1
	return t.a
}

// LocalCopy is false.
//
// @Ensures r = 1
func LocalCopy() (r int) {
	var s S
	t := s
	p := &s.a
	*p = 1
	return t.a // want `vego: postcondition may not hold: r = 1`
}

// Item is an element of a slice in a struct.
type Item struct{ n, m int }

// Holder holds items.
type Holder struct {
	items []Item
	total int
}

// Deep is true.
//
// @Requires o != nil And 0 <= i < |o.items|
// @Modifies o.items
// @Ensures o.items'[i].n = 7 And o.items'[i].m = o.items[i].m And o.total' = o.total
func Deep(o *Holder, i int) {
	p := &o.items[i].n
	*p = 7
}

// DeepFalse is false when i = j.
//
// @Requires o != nil And 0 <= i < |o.items| And 0 <= j < |o.items|
// @Modifies o.items
// @Ensures o.items'[j].n = o.items[j].n
func DeepFalse(o *Holder, i, j int) {
	p := &o.items[i].n
	*p = 7 + o.items[i].n%2
} // want `vego: postcondition may not hold: o\.items'\[j\]\.n = o\.items\[j\]\.n`

// SliceAndPointer is false when p is &xs[0].
//
// @Requires p != nil And |xs| > 0
// @Modifies p, xs
// @Ensures xs'[0] = 1
func SliceAndPointer(p *int, xs []int) {
	xs[0] = 1
	*p = 2
} // want `vego: postcondition may not hold: xs'\[0\] = 1`

// CallSliceAndPointer is false.
//
// @Ensures r = 1
func CallSliceAndPointer() (r int) {
	xs := []int{0, 0}
	SliceAndPointer(&xs[0], xs)
	return xs[0]
}

// LoopZero is true.
//
// @Modifies xs
// @Ensures Forall k in [0, |xs|) : xs'[k] = 0
func LoopZero(xs []int) {
	// @Invariant Forall k in [0, i) : xs[k] = 0
	for i := range xs {
		p := &xs[i]
		*p = 0
	}
}

// Total is a counter of a package.
var total int

// incTotal is true.
//
// @Requires total < 1000
// @Modifies total
// @Ensures total' = total + 1
func incTotal() {
	Inc(&total)
}

// incTotalUnlisted is refused: it writes total without listing it.
//
// @Requires total < 1000
// @Ensures True
func incTotalUnlisted() {
	Inc(&total) // want `vego: Inc may modify p, which incTotalUnlisted may not modify; list it in a // @Modifies clause,`
}

// Hits counts.
type Hits int

// @Requires h != nil And *h < 100
// @Modifies h
// @Ensures *h' = *h + 1
func (h *Hits) Add() {
	*h++
}

// Stats holds hits.
type Stats struct {
	Hits Hits
	Miss int
}

// AddHit is true.
//
// @Requires s != nil And s.Hits < 100
// @Modifies s
// @Ensures s.Hits' = s.Hits + 1 And s.Miss' = s.Miss
func AddHit(s *Stats) {
	s.Hits.Add()
}

// AddHitFalse is false.
//
// @Requires s != nil And s.Hits < 100
// @Modifies s
// @Ensures s.Hits' = s.Hits
func AddHitFalse(s *Stats) {
	s.Hits.Add()
} // want `vego: postcondition may not hold: s\.Hits' = s\.Hits`
