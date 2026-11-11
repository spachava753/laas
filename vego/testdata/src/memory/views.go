package memory

// Ratio and Fraction have the same fields, so a pointer to one converts to
// a pointer to the other and both then point to one struct.
type Ratio struct{ Num, Den int }

// Fraction is a Ratio under another name.
type Fraction Ratio

// DivideViews takes two pointers that may be one struct seen as two types.
//
// @ Requires p != nil And q != nil And q.Den = 2
// @ Modifies p
func DivideViews(p *Ratio, q *Fraction) int {
	p.Den = 0
	return 10 / q.Den // want `vego: possible division by zero`
}

// DivideApart says the two are different structs.
//
// @ Requires p != nil And q != nil And q.Den = 2 And ~within(p, q)
// @ Modifies p
func DivideApart(p *Ratio, q *Fraction) int {
	p.Den = 0
	return 10 / q.Den
}

//@ Ensures result = 5

// CallsDivideApart passes one struct as both, which the callee ruled out.
//
// @ Requires p != nil And p.Den = 2
// @ Modifies p
func CallsDivideApart(p *Ratio) int {
	return DivideApart(p, (*Fraction)(p)) // want `vego: precondition of DivideApart may not hold: .*`
}

// CallsDivideApartRight passes two structs.
func CallsDivideApartRight() int {
	p, q := &Ratio{Den: 3}, &Fraction{Den: 2}
	return DivideApart(p, q)
}

//@ Ensures result = 5

// Viewed converts a pointer, which gives a second view of one struct.
//
// @ Requires p != nil
// @ Modifies p
func Viewed(p *Ratio) int {
	q := (*Fraction)(p)
	q.Num = 3
	return p.Num
}

//@ Ensures result = 3 And p.Den' = p.Den

// ViewedWrong claims the write through the view is not seen.
//
// @ Requires p != nil And p.Num = 0
// @ Modifies p
func ViewedWrong(p *Ratio) int {
	q := (*Fraction)(p)
	q.Num = 3
	return p.Num // want `vego: postcondition may not hold: result = 0`
}

//@ Ensures result = 0

// ViewedUnlisted writes through a view of a struct it may not change.
//
// @ Requires p != nil
func ViewedUnlisted(p *Ratio) {
	q := (*Fraction)(p)
	q.Num = 3 // want `vego: q\.Num is assigned, which ViewedUnlisted may not modify; list it in a //@ Modifies clause`
}

// PointInSegment takes a pointer that may point into the struct it also
// takes.
//
// @ Requires p != nil And s != nil And s.From.X = 0 And s.To.X = 0
// @ Modifies p
func PointInSegment(p *Point, s *Segment) int {
	p.X = 1
	return s.From.X + s.To.X // want `vego: postcondition may not hold: result = 0`
}

//@ Ensures result = 0

// PointOutsideSegment says it does not.
//
// @ Requires p != nil And s != nil And s.From.X = 0 And s.To.X = 0 And ~within(p, s)
// @ Modifies p
func PointOutsideSegment(p *Point, s *Segment) int {
	p.X = 1
	return s.From.X + s.To.X
}

//@ Ensures result = 0

// PointIsFrom says where in the struct the pointer points.
//
// @ Requires s != nil And s.From.X = 0 And s.To.X = 0
// @ Modifies s
func PointIsFrom(s *Segment) int {
	p := &s.From
	p.X = 1
	return s.From.X + s.To.X
}

//@ Ensures result = 1

// SamePoint compares pointers into one struct.
//
// @ Requires s != nil
func SamePoint(s *Segment) bool {
	return &s.From == &s.To
}

//@ Ensures ~result

// SamePointWrong claims that two fields are at one place.
//
// @ Requires s != nil
func SamePointWrong(s *Segment) bool {
	return &s.From == &s.To // want `vego: postcondition may not hold: result`
}

//@ Ensures result

// Counters holds two counters side by side.
type Counters struct{ A, B Counter }

// IncField calls a method with a pointer receiver on a field.
//
// @ Requires cs != nil And cs.A.n = 0 And cs.A.limit = 5 And cs.B.n = 0
// @ Modifies cs
func IncField(cs *Counters) int {
	cs.A.Inc()
	return cs.A.n + cs.B.n
}

//@ Ensures result = 1

// IncFieldWrong claims the other counter was advanced too.
//
// @ Requires cs != nil And cs.A.n = 0 And cs.A.limit = 5 And cs.B.n = 0
// @ Modifies cs
func IncFieldWrong(cs *Counters) int {
	cs.A.Inc()
	return cs.A.n + cs.B.n // want `vego: postcondition may not hold: result = 2`
}

//@ Ensures result = 2

// IncElement calls a method with a pointer receiver on an element.
//
// @ Requires |cs| = 2 And cs[0].n = 0 And cs[0].limit = 5 And cs[1].n = 0 And cs[1].limit = 5
// @ Modifies cs
func IncElement(cs []Counter) int {
	cs[1].Inc()
	cs[1].Inc()
	return cs[0].n + cs[1].n
}

//@ Ensures result = 2

// IncElementUnlisted does so without saying that the slice changes.
//
// @ Requires |cs| = 2 And cs[1].n = 0 And cs[1].limit = 5
func IncElementUnlisted(cs []Counter) {
	cs[1].Inc() // want `vego: .*may not modify.*`
}

// IncElementOutOfRange calls the method on an element that is not there.
//
// @ Modifies cs
func IncElementOutOfRange(cs []Counter) {
	cs[0].Inc() // want `vego: index may be out of range` `vego: precondition of Inc may not hold: c.n < c.limit` `vego: precondition of Inc may not hold: c.limit <= 1000`
}

// ElementKept keeps a pointer to an element across a write to another.
//
// @ Requires |ps| = 3 And ps[2].X = 9
// @ Modifies ps
func ElementKept(ps []Point) int {
	last := &ps[2]
	ps[0].X = 1
	ps[1] = Point{X: 4, Y: 4}
	return last.X
}

//@ Ensures result = 9

// ElementOverwritten keeps a pointer to an element that is then replaced.
//
// @ Requires |ps| = 3 And ps[2].X = 9
// @ Modifies ps
func ElementOverwritten(ps []Point) int {
	last := &ps[2]
	ps[2] = Point{X: 4, Y: 4}
	return last.X // want `vego: postcondition may not hold: result = 9`
}

//@ Ensures result = 9

// AppendMoves appends to a slice an element pointer points into. Whether
// the pointer still points into the slice depends on the capacity.
//
// @ Requires |ps| = 1 And ps[0].X = 9
// @ Modifies ps
func AppendMoves(ps []Point) int {
	first := &ps[0]
	ps = append(ps, Point{})
	ps[0].X = 1
	return first.X // want `vego: postcondition may not hold: result = 9`
}

//@ Ensures result = 9

// LocalThroughPointer writes a variable through a pointer to it.
func LocalThroughPointer() int {
	x := Point{X: 1, Y: 2}
	p := &x
	p.X = 5
	return x.X + x.Y
}

//@ Ensures result = 7

// LocalThroughPointerWrong claims the variable kept its value.
func LocalThroughPointerWrong() int {
	x := Point{X: 1, Y: 2}
	p := &x
	p.X = 5
	return x.X // want `vego: postcondition may not hold: result = 1`
}

//@ Ensures result = 1

// PointerSeesLocal writes the variable and reads through the pointer.
func PointerSeesLocal() int {
	x := Point{X: 1}
	p := &x
	x.X = 8
	x = Point{X: x.X + 1, Y: 3}
	return p.X + p.Y
}

//@ Ensures result = 12

// PointerSeesLocalWrong claims the pointer kept the old value.
func PointerSeesLocalWrong() int {
	x := Point{X: 1}
	p := &x
	x.X = 8
	return p.X // want `vego: postcondition may not hold: result = 1`
}

//@ Ensures result = 1

// CopyOfLocal copies a variable whose address is taken; the copy is a
// value of its own.
func CopyOfLocal() int {
	x := Point{X: 1}
	p := &x
	y := x
	p.X = 5
	return y.X
}

//@ Ensures result = 1

// CopyOfLocalWrong claims the copy follows the variable.
func CopyOfLocalWrong() int {
	x := Point{X: 1}
	p := &x
	y := x
	p.X = 5
	return y.X // want `vego: postcondition may not hold: result = 5`
}

//@ Ensures result = 5

// LocalMethod calls a method with a pointer receiver on a variable.
func LocalMethod() int {
	c := Counter{limit: 3}
	c.Inc()
	c.Inc()
	return c.n
}

//@ Ensures result = 2

// LocalMethodWrong claims the variable was not changed.
func LocalMethodWrong() int {
	c := Counter{limit: 3}
	c.Inc()
	return c.n // want `vego: postcondition may not hold: result = 0`
}

//@ Ensures result = 0

// LocalMethodLimit calls the method more often than its contract allows.
func LocalMethodLimit() int {
	var c Counter
	c.limit = 1
	c.Inc()
	c.Inc() // want `vego: precondition of Inc may not hold: c\.n < c\.limit`
	return c.n
}

//@ Ensures result = 2

// LocalFieldMethod calls a method on a field of a variable.
func LocalFieldMethod() int {
	var cs Counters
	cs.B.limit = 4
	cs.B.Inc()
	return cs.A.n + cs.B.n
}

//@ Ensures result = 1

// PassLocal passes the address of a variable to a function that fills it.
func PassLocal() int {
	var r Ratio
	fill(&r)
	return r.Num + r.Den
}

//@ Ensures result = 3

// PassLocalWrong claims the variable is still zero.
func PassLocalWrong() int {
	var r Ratio
	fill(&r)
	return r.Num // want `vego: postcondition may not hold: result = 0`
}

//@ Ensures result = 0

// @ Requires r != nil
// @ Modifies r
func fill(r *Ratio) {
	r.Num, r.Den = 1, 2
}

//@ Ensures r.Num' = 1 And r.Den' = 2

// ParamAddress takes the address of a parameter, which is a copy the
// caller does not see.
func ParamAddress(p Point) int {
	q := &p
	q.X = 4
	return p.X
}

//@ Ensures result = 4

// ParamAddressWrong claims the parameter kept the value it came with.
//
// @ Requires p.X = 0
func ParamAddressWrong(p Point) int {
	q := &p
	q.X = 4
	return p.X // want `vego: postcondition may not hold: result = p\.X`
}

//@ Ensures result = p.X

// ReturnsLocal returns the address of a variable, which nobody else has.
func ReturnsLocal() *Point {
	x := Point{X: 3}
	return &x
}

//@ Ensures fresh(result) And result.X = 3

// NamedResultAddress fills a named result through a pointer.
func NamedResultAddress() (r Ratio) {
	fill(&r)
	return
}

//@ Ensures r.Num = 1 And r.Den = 2

// LocalsApart takes the addresses of two variables, which differ.
func LocalsApart() bool {
	var a, b Point
	return &a == &b
}

//@ Ensures ~result

// LocalNotParam has a variable that no parameter points to.
//
// @ Requires p != nil And p.X = 1
func LocalNotParam(p *Point) int {
	var x Point
	q := &x
	q.X = 9
	return p.X
}

//@ Ensures result = 1

// LocalInLoop writes a variable through a pointer inside a loop.
//
// @ Requires 0 <= n <= 100
func LocalInLoop(n int) int {
	var x Point
	p := &x
	//@ Invariant 0 <= i <= n And x.X = i
	//@ Variant n - i
	for i := 0; i < n; i++ {
		p.X++
	}
	return x.X
}

//@ Ensures result = n

// LocalInLoopWrong claims the loop leaves the variable alone.
//
// @ Requires 1 <= n <= 100
func LocalInLoopWrong(n int) int {
	var x Point
	p := &x
	//@ Invariant 0 <= i <= n And x.X = i
	//@ Variant n - i
	for i := 0; i < n; i++ {
		p.X++
	}
	return x.X // want `vego: postcondition may not hold: result = 0`
}

//@ Ensures result = 0

// LoopKeepsOther has a loop that writes one variable through a method and
// leaves another, of the same type, alone.
//
// @ Requires 0 <= n <= 100
func LoopKeepsOther(n int) int {
	a := Counter{limit: 1000}
	b := Counter{n: 7, limit: 1000}
	q := &b
	//@ Invariant 0 <= i <= n And a.n = i And a.limit = 1000
	//@ Variant n - i
	for i := 0; i < n; i++ {
		a.Inc()
	}
	return q.n
}

//@ Ensures result = 7

// EachIteration declares a variable in a loop; every iteration has its
// own, so the pointers kept from two iterations differ.
func EachIteration() bool {
	var first, second *Point
	//@ Invariant 0 <= i <= 2 And (i >= 1 -> first != nil) And (i >= 2 -> second != nil And first != second)
	//@ Variant 2 - i
	for i := 0; i < 2; i++ {
		var x Point
		if i == 0 {
			first = &x
		} else {
			second = &x
		}
	}
	return first == second
}

//@ Ensures ~result

// RangeAddress takes the address of the variable of a range loop, which is
// a copy of the element.
//
// @ Requires |ps| > 0
func RangeAddress(ps []Point) {
	//@ Invariant Forall k in [0, |ps|) : ps[k].X = old(ps[k].X)
	for _, p := range ps {
		q := &p
		q.X = 0
	}
}

//@ Ensures Forall k in [0, |ps|) : ps'[k].X = ps[k].X

// AddressOfInt takes the address of something that is not a struct.
func AddressOfInt() int {
	x := 1
	p := &x // want `vego: cannot verify AddressOfInt: p has unsupported type \*int`
	return *p
}

//@ Ensures result = 1

// SetOneField lists one field of one element.
//
// @ Requires |ps| > 2
// @ Modifies ps[1].X
func SetOneField(ps []Point) {
	ps[1].X = 3
}

//@ Ensures ps'[1].X = 3

// UsesSetOneField relies on everything else being kept.
//
// @ Requires |ps| > 2 And ps[1].Y = 4 And ps[2].X = 5
// @ Modifies ps
func UsesSetOneField(ps []Point) int {
	SetOneField(ps)
	return ps[1].X + ps[1].Y + ps[2].X
}

//@ Ensures result = 12

// UsesSetOneFieldWrong relies on the field that was written.
//
// @ Requires |ps| > 2 And ps[1].X = 4
// @ Modifies ps
func UsesSetOneFieldWrong(ps []Point) int {
	SetOneField(ps)
	return ps[1].X // want `vego: postcondition may not hold: result = 4`
}

//@ Ensures result = 4

// FromOnly lists one struct inside another and writes it through a pointer.
//
// @ Requires s != nil
// @ Modifies s.From
func FromOnly(s *Segment) {
	p := &s.From
	p.X = 1
	p.Y = 2
}

//@ Ensures s.From.X' = 1 And s.To.X' = s.To.X

// FromOnlyWrong writes the struct next to the one it listed.
//
// @ Requires s != nil
// @ Modifies s.From
func FromOnlyWrong(s *Segment) {
	p := &s.To
	p.X = 1 // want `vego: p\.X is assigned, which FromOnlyWrong may not modify; list it in a //@ Modifies clause`
}

// BumpEach changes each element through a pointer to it.
//
// @ Requires Forall k in [0, |ps|) : 0 <= ps[k].X <= 100
// @ Modifies ps
func BumpEach(ps []Point) {
	//@ Invariant 0 <= i <= |ps|
	//@ Invariant Forall k in [0, i) : ps[k].X = old(ps[k].X) + 1
	//@ Invariant Forall k in [i, |ps|) : ps[k].X = old(ps[k].X)
	for i := range ps {
		p := &ps[i]
		p.X++
	}
}

//@ Ensures Forall k in [0, |ps|) : ps'[k].X = ps[k].X + 1

// BumpEachWrong claims a different amount.
//
// @ Requires Forall k in [0, |ps|) : 0 <= ps[k].X <= 100
// @ Modifies ps
func BumpEachWrong(ps []Point) {
	//@ Invariant 0 <= i <= |ps|
	//@ Invariant Forall k in [0, i) : ps[k].X = old(ps[k].X) + 1
	//@ Invariant Forall k in [i, |ps|) : ps[k].X = old(ps[k].X)
	for i := range ps {
		p := &ps[i]
		p.X++
	}
} // want `vego: postcondition may not hold: Forall k in \[0, \|ps\|\) : ps'\[k\]\.X = ps\[k\]\.X \+ 2`

//@ Ensures Forall k in [0, |ps|) : ps'[k].X = ps[k].X + 2

// SwapPoints exchanges two structs that may be one.
//
// @ Requires a != nil And b != nil
// @ Modifies a, b
func SwapPoints(a, b *Point) {
	*a, *b = *b, *a
}

//@ Ensures a.X' = b.X And b.X' = a.X And a.Y' = b.Y And b.Y' = a.Y

// SwapEnds passes pointers to two elements.
//
// @ Requires |ps| > 1
// @ Modifies ps
func SwapEnds(ps []Point) {
	SwapPoints(&ps[0], &ps[len(ps)-1])
}

//@ Ensures ps'[0].X = ps[|ps|-1].X And ps'[|ps|-1].Y = ps[0].Y

// SwapEndsWrong claims the first element stayed.
//
// @ Requires |ps| > 1
// @ Modifies ps
func SwapEndsWrong(ps []Point) {
	SwapPoints(&ps[0], &ps[len(ps)-1])
} // want `vego: postcondition may not hold: ps'\[0\]\.X = ps\[0\]\.X`

//@ Ensures ps'[0].X = ps[0].X

// positive reports whether a point has a positive X.
//
// @ Requires p != nil
func positive(p *Point) bool {
	return p.X > 0
}

//@ Ensures result <-> p.X > 0

// GuardedAddress takes the address of an element only when there is one.
func GuardedAddress(ps []Point) bool {
	return len(ps) > 0 && positive(&ps[0])
}

//@ Ensures result <-> |ps| > 0 And ps[0].X > 0

// UnguardedAddress takes it in any case.
func UnguardedAddress(ps []Point) bool {
	return len(ps) >= 0 && positive(&ps[0]) // want `vego: index may be out of range`
}

//@ Ensures result <-> |ps| > 0 And ps[0].X > 0

// GuardedField takes the address of a field when the pointer is not nil.
func GuardedField(s *Segment) bool {
	return s != nil && positive(&s.To)
}

//@ Ensures result <-> s != nil And s.To.X > 0

// UnguardedField takes it on the wrong side of the test.
func UnguardedField(s *Segment) bool {
	return s == nil || positive(&s.To)
}

//@ Ensures result <-> s = nil Or s.To.X > 0

// WrongGuardField takes it when the pointer is nil.
func WrongGuardField(s *Segment) bool {
	return s == nil && positive(&s.To) // want `vego: pointer may be nil`
}

//@ Ensures ~result

// ManyNothings takes a slice whose elements have no size, which can be
// longer than any allocation.
func ManyNothings(s []struct{}) bool {
	return len(s) <= 281474976710656 // want `vego: postcondition may not hold: result`
}

//@ Ensures result

// CountNothings relies on what is known of such a slice: its length is an
// int that is not negative.
func CountNothings(s []struct{}) bool {
	return len(s) >= 0 && len(s)/2 <= len(s)
}

//@ Ensures result

// MakeNothings makes a slice that needs no memory.
//
// @ Requires 0 <= n
func MakeNothings(n int) int {
	s := make([]struct{}, n)
	return len(s)
}

//@ Ensures result = n

// Wired has a field of a type that is not modelled. The field cannot be
// used, but it is part of the struct all the same.
type Wired struct {
	X int
	C chan int
}

// OverwriteWired replaces the whole struct, and with it the field that is
// not modelled, which the clause does not list.
//
// @ Requires p != nil
// @ Modifies p.X
func OverwriteWired(p *Wired) {
	*p = Wired{X: 1} // want `vego: \*p is assigned, which OverwriteWired may not modify; list it in a //@ Modifies clause`
}

//@ Ensures p.X' = 1

// OverwriteWiredListed lists the struct.
//
// @ Requires p != nil
// @ Modifies p
func OverwriteWiredListed(p *Wired) {
	*p = Wired{X: 1}
}

//@ Ensures p.X' = 1

// SetWiredX writes the one field it lists.
//
// @ Requires p != nil
// @ Modifies p.X
func SetWiredX(p *Wired) {
	p.X = 1
}

//@ Ensures p.X' = 1

// CopyWired copies a struct with such a field through a call that may
// write all of it, which the caller did not list.
//
// @ Requires p != nil
// @ Modifies p.X
func CopyWired(p *Wired) {
	OverwriteWiredListed(p) // want `vego: OverwriteWiredListed may modify p, which CopyWired may not modify; list it in a //@ Modifies clause`
}

// EachField lists the fields of a struct one by one and then writes the
// struct as a whole.
//
// @ Requires p != nil
// @ Modifies p.X, p.Y
func EachField(p *Point) {
	*p = Point{X: 1, Y: 2}
}

//@ Ensures p.X' = 1 And p.Y' = 2

// OneOfTwoFields lists only one of them.
//
// @ Requires p != nil
// @ Modifies p.X
func OneOfTwoFields(p *Point) {
	*p = Point{X: 1, Y: 2} // want `vego: \*p is assigned, which OneOfTwoFields may not modify; list it in a //@ Modifies clause`
}

// SpareField lists a field that the function never writes.
//
// @ Requires p != nil
// @ Modifies p.X, p.Y // want `vego: Modifies lists p\.Y, but SpareField never needs to modify it.*`
func SpareField(p *Point) {
	p.X = 1
}

//@ Ensures p.X' = 1

// ReturnAssigns returns a value for a named result that a pointer points
// to. Returning assigns the result, so the pointer sees the value.
func ReturnAssigns() (r Point, p *Point) {
	p = &r
	return Point{X: 1}, p
}

//@ Ensures r.X = 1 And p.X = 1

// ReturnAssignsWrong claims the pointer still sees the old value.
func ReturnAssignsWrong() (r Point, p *Point) {
	p = &r
	return Point{X: 1}, p // want `vego: postcondition may not hold: p\.X = 0`
}

//@ Ensures r.X = 1 And p.X = 0
