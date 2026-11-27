// Package ptrvalsbad has pointers to single values whose contracts are
// false, and pointers vego does not support.
package ptrvalsbad

// Inc increments what p points to.
//
// @Requires p != nil And *p < 1000
// @Modifies p
// @Ensures *p' = *p + 1
func Inc(p *int) {
	*p = *p + 1
}

// StaleRead claims the value x had before it was assigned.
//
// @Ensures r = 5
func StaleRead() (r int) {
	x := 5
	p := &x
	x = 2
	return *p // want `vego: postcondition may not hold: r = 5`
}

// Unlisted writes what p points to without listing p.
//
// @Requires p != nil
// @Ensures True
func Unlisted(p *int) {
	*p = 1 // want `vego: \*p is assigned, which Unlisted may not modify; list it in a // @Modifies clause, as p`
}

// KeepsOther claims that q is unchanged, which fails when p = q.
//
// @Requires p != nil And q != nil And *p < 1000
// @Modifies p
// @Ensures *q' = *q
func KeepsOther(p, q *int) {
	Inc(p)
} // want `vego: postcondition may not hold: \*q' = \*q`

// KeepsApart claims the same of a q that is not p, which holds.
//
// @Requires p != nil And q != nil And p != q And *p < 1000
// @Modifies p
// @Ensures *q' = *q
func KeepsApart(p, q *int) {
	Inc(p)
}

// SwapWrong claims that p keeps its value.
//
// @Requires p != nil And q != nil
// @Modifies p, q
// @Ensures *p' = *p
func SwapWrong(p, q *int) {
	*p, *q = *q, *p
} // want `vego: postcondition may not hold: \*p' = \*p`

// Config has a limit that may be absent.
type Config struct {
	Limit *int
}

// NoCheck reads the limit without checking it.
//
// @Ensures True
func NoCheck(c Config) (n int) {
	return *c.Limit // want `vego: pointer may be nil`
}

// MyInt has the memory of int.
type MyInt int

// Converted writes x through a *int converted from its *MyInt, and claims
// the old value.
//
// @Ensures r = 1
func Converted() (r MyInt) {
	x := MyInt(1)
	q := (*int)(&x)
	*q = 5
	return x // want `vego: postcondition may not hold: r = 1`
}

// Escapes returns the address of a local and claims its value.
//
// @Ensures p != nil And *p = 2
func Escapes() (p *int) {
	x := 1
	return &x // want `vego: postcondition may not hold: \*p = 2`
}

// S has a number as a field.
type S struct {
	f int
}

// FieldAddress takes the address of a field, which verifies since F42.
//
// @Ensures True
func FieldAddress() (r int) {
	var s S
	Inc(&s.f)
	return s.f
}

// ElementAddress takes the address of an element of a slice, which
// verifies since F42.
//
// @Requires |xs| > 0 And xs[0] < 1000
// @Modifies xs
// @Ensures True
func ElementAddress(xs []int) {
	Inc(&xs[0])
}

// ArrayAddress takes the address of an element of an array, which verifies
// since F42.
//
// @Ensures True
func ArrayAddress() (r int) {
	var a [2]int
	Inc(&a[0])
	return a[0]
}

// G is a package-level number.
var G int

// GlobalAddress takes the address of a package-level variable, which lives
// in a box of its own since F42, and lists nothing and requires nothing of
// it.
//
// @Ensures True
func GlobalAddress() {
	Inc(&G) // want `vego: precondition of Inc may not hold: \*p < 1000` `vego: Inc may modify p, which GlobalAddress may not modify; list it in a // @Modifies clause, as G`
}

// Counter counts.
type Counter int

// Bump increments the counter.
//
// @Requires c != nil And *c < 100
// @Modifies c
// @Ensures *c' = *c + 1
func (c *Counter) Bump() {
	*c++
}

// Stats holds a counter in a field and one embedded.
type Stats struct {
	Hits Counter
	Counter
}

// FieldMethod calls a pointer method on a field, which verifies since F42.
//
// @Requires s != nil And s.Hits < 100
// @Modifies s
// @Ensures True
func FieldMethod(s *Stats) {
	s.Hits.Bump()
}

// PromotedMethod calls a pointer method promoted from an embedded counter,
// which verifies since F42.
//
// @Requires s != nil And s.Counter < 100
// @Modifies s
// @Ensures True
func PromotedMethod(s *Stats) {
	s.Bump()
}

// ElementMethod calls a pointer method on an element of a slice, which
// verifies since F42.
//
// @Requires |cs| > 0 And cs[0] < 100
// @Modifies cs
// @Ensures True
func ElementMethod(cs []Counter) {
	cs[0].Bump()
}

// NotAPointer dereferences a number in a formula.
//
// @Ensures *n = 1 // want `vego: in Ensures annotation: n has type int, and \* follows only a pointer`
func NotAPointer(n int) {
}

// StructWhole dereferences a pointer to a struct in a formula.
//
// @Requires s != nil
// @Ensures *s = *s // want `vego: in Ensures annotation: s points to a struct, which a formula cannot name as a whole after \*; name its fields`
func StructWhole(s *S) {
}

// Twice dereferences twice in a formula.
//
// @Requires p != nil
// @Ensures **p = 1 // want `vego: in Ensures annotation: p has type int, and \* follows only a pointer`
func Twice(p *int) {
}

// ModifiesDeref names what p points to with *.
//
// @Requires p != nil
// @Modifies *p // want `vego: syntax error in Modifies annotation: Modifies names what a pointer points to by the pointer: write p, not \*p`
// @Ensures True
func ModifiesDeref(p *int) {
	*p = 1
}

// TimesPointer multiplies by a pointer.
//
// @Requires p != nil
// @Ensures 2 *p = 2 // want `vego: in Ensures annotation: expected an integer but p has type pointer`
func TimesPointer(p *int) {
}

// TimesDeref multiplies by what p points to.
//
// @Requires p != nil And *p = 1
// @Ensures 2 * *p = 2
func TimesDeref(p *int) {
}

// WithinSlice asks whether a pointer to a number lies in a slice.
//
// @Requires p != nil
// @Ensures within(p, xs) // want `vego: in Ensures annotation: within\(p, xs\): p points to a value of type int, which lies only in a value of its own, a variable or what new made, and in no slice or struct; within of two such pointers says that they are equal`
func WithinSlice(p *int, xs []int) {
}

// WithinStruct asks whether a pointer to a number lies in a struct.
//
// @Requires p != nil And s != nil
// @Ensures within(p, s) // want `vego: in Ensures annotation: within\(p, s\): p points to a value of type int, which lies only in a value of its own, a variable or what new made, and in no slice or struct; within of two such pointers says that they are equal`
func WithinStruct(p *int, s *S) {
}

// DeferredResultWrong claims the value the return assigned.
//
// @Ensures r = 1
func DeferredResultWrong() (r int) {
	p := &r
	defer func() { *p = *p + 1 }()
	return 1 // want `vego: postcondition may not hold: r = 1`
}

// CapturedWrong claims the value before the literal wrote it.
//
// @Ensures r = 1
func CapturedWrong() (r int) {
	x := 1
	p := &x
	func() { x = 4 }()
	return *p // want `vego: postcondition may not hold: r = 1`
}

// Owner owns the counter its field points to.
//
// @Owns c
type Owner struct {
	c *Counter
}

// useOwner writes what p points to and claims that what o owns is
// unchanged.
//
// @Requires o != nil And o.c != nil And p != nil
// @Modifies o, p
// @Ensures o.c' = o.c And *o.c' = *o.c
func useOwner(o *Owner, p *int) {
	*p = 7
	o.c = o.c
}

// HandOwned hands useOwner what o owns, as a *int: the box twin of the
// storage fix (A5 of the design review).
//
// @Requires o != nil And o.c != nil
// @Modifies o
// @Ensures True
func HandOwned(o *Owner) {
	useOwner(o, (*int)(o.c)) // want `vego: \(\*int\)\(o\.c\) is memory that o owns, and useOwner is handed what reaches a Owner, which can own it; useOwner assumes that nothing it is handed is what an owner it is handed owns: copy it, or pass it alone`
}

// bumpOther is trusted with an entry that describes what p points to on
// return, which its modifies does not list.
func bumpOther(p *int) { *p = *p + 1 }

// UsesBumpOther calls it.
//
// @Requires p != nil
// @Modifies p
// @Ensures True
func UsesBumpOther(p *int) {
	bumpOther(p) // want `vego: the trusted contract of ptrvalsbad\.bumpOther \(trusted\.yaml:\d+\) cannot be used: its ensures "\*p' = \*p \+ 1" describes \*p' after the call, but nothing its modifies lists is memory that \*p' reads, so the call cannot have changed it; drop the prime or list what the function writes` `vego: the trusted contract of ptrvalsbad\.bumpOther \(trusted\.yaml:\d+\) cannot be used: it contradicts itself, so anything could be proved from it`
}

// SetOnly forgets the prime of what p points to on return.
//
// @Requires p != nil
// @Modifies p
// @Ensures *p = 7 // want `vego: the Ensures clause "\*p = 7" names no result and nothing on return, so it speaks of the state when SetOnly is called, and it reads memory that SetOnly may modify; write a prime for the value on return, as in \*p', or move the clause to a Requires`
func SetOnly(p *int) {
	*p = 7
} // want `vego: postcondition may not hold: \*p = 7`

// Limited owns the int its field points to.
//
// @Owns limit
type Limited struct {
	limit *int
}

// SetLimit stores a pointer to a parameter into the owned field.
//
// @Requires l != nil
// @Modifies l
// @Ensures True
func SetLimit(l *Limited, n *int) {
	l.limit = n // want `vego: l\.limit may come to refer to memory that existed when SetLimit was called and that it did not own; an owned field may refer only to memory made since, or to part of what it referred to then; copy the value into one made with new\(int\), or do not declare the field owned`
}

// WithinStructPointer asks whether a struct lies in what p points to.
//
// @Requires p != nil And s != nil
// @Ensures within(s, p) // want `vego: in Ensures annotation: within\(s, p\): p points to a value of type int, in which nothing lies but what points to it`
func WithinStructPointer(p *int, s *S) {
}

// ValidOfNumber asks for the invariant of what p points to.
//
// @Requires p != nil And valid(p) // want `vego: in Requires annotation: valid\(p\): p is not a struct or a pointer to one`
// @Ensures True
func ValidOfNumber(p *int) {
}
