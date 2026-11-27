package memory

// Ratio and Fraction have the same fields, so a pointer to one converts to
// a pointer to the other and both then point to one struct.
type Ratio struct{ Num, Den int }

// Fraction is a Ratio under another name.
type Fraction Ratio

// DivideViews takes two pointers that may be one struct seen as two types.
//
// @Requires p != nil And q != nil And q.Den = 2
// @Modifies p
func DivideViews(p *Ratio, q *Fraction) (result int) {
	p.Den = 0
	return 10 / q.Den // want `vego: possible division by zero`
}

// DivideApart says the two are different structs.
//
// @Requires p != nil And q != nil And q.Den = 2 And ~within(p, q)
// @Modifies p
// @Ensures result = 5
func DivideApart(p *Ratio, q *Fraction) (result int) {
	p.Den = 0
	return 10 / q.Den
}

// CallsDivideApart passes one struct as both, which the callee ruled out.
//
// @Requires p != nil And p.Den = 2
// @Modifies p
func CallsDivideApart(p *Ratio) (result int) {
	return DivideApart(p, (*Fraction)(p)) // want `vego: precondition of DivideApart may not hold: .*`
}

// CallsDivideApartRight passes two structs.
//
// @Ensures result = 5
func CallsDivideApartRight() (result int) {
	p, q := &Ratio{Den: 3}, &Fraction{Den: 2}
	return DivideApart(p, q)
}

// Viewed converts a pointer, which gives a second view of one struct.
//
// @Requires p != nil
// @Modifies p
// @Ensures result = 3 And p.Den' = p.Den
func Viewed(p *Ratio) (result int) {
	q := (*Fraction)(p)
	q.Num = 3
	return p.Num
}

// ViewedWrong claims the write through the view is not seen.
//
// @Requires p != nil And p.Num = 0
// @Modifies p
// @Ensures result = 0
func ViewedWrong(p *Ratio) (result int) {
	q := (*Fraction)(p)
	q.Num = 3
	return p.Num // want `vego: postcondition may not hold: result = 0`
}

// ViewedUnlisted writes through a view of a struct it may not change.
//
// @Requires p != nil
func ViewedUnlisted(p *Ratio) {
	q := (*Fraction)(p)
	q.Num = 3 // want `vego: q\.Num is assigned, which ViewedUnlisted may not modify; list it in a // @Modifies clause`
}

// PointInSegment takes a pointer that may point into the struct it also
// takes.
//
// @Requires p != nil And s != nil And s.From.X = 0 And s.To.X = 0
// @Modifies p
// @Ensures result = 0
func PointInSegment(p *Point, s *Segment) (result int) {
	p.X = 1
	return s.From.X + s.To.X // want `vego: postcondition may not hold: result = 0`
}

// PointOutsideSegment says it does not.
//
// @Requires p != nil And s != nil And s.From.X = 0 And s.To.X = 0 And ~within(p, s)
// @Modifies p
// @Ensures result = 0
func PointOutsideSegment(p *Point, s *Segment) (result int) {
	p.X = 1
	return s.From.X + s.To.X
}

// PointIsFrom says where in the struct the pointer points.
//
// @Requires s != nil And s.From.X = 0 And s.To.X = 0
// @Modifies s
// @Ensures result = 1
func PointIsFrom(s *Segment) (result int) {
	p := &s.From
	p.X = 1
	return s.From.X + s.To.X
}

// SamePoint compares pointers into one struct.
//
// @Requires s != nil
// @Ensures ~result
func SamePoint(s *Segment) (result bool) {
	return &s.From == &s.To
}

// SamePointWrong claims that two fields are at one place.
//
// @Requires s != nil
// @Ensures result
func SamePointWrong(s *Segment) (result bool) {
	return &s.From == &s.To // want `vego: postcondition may not hold: result`
}

// Counters holds two counters side by side.
type Counters struct{ A, B Counter }

// IncField calls a method with a pointer receiver on a field.
//
// @Requires cs != nil And cs.A.n = 0 And cs.A.limit = 5 And cs.B.n = 0
// @Modifies cs
// @Ensures result = 1
func IncField(cs *Counters) (result int) {
	cs.A.Inc()
	return cs.A.n + cs.B.n
}

// IncFieldWrong claims the other counter was advanced too.
//
// @Requires cs != nil And cs.A.n = 0 And cs.A.limit = 5 And cs.B.n = 0
// @Modifies cs
// @Ensures result = 2
func IncFieldWrong(cs *Counters) (result int) {
	cs.A.Inc()
	return cs.A.n + cs.B.n // want `vego: postcondition may not hold: result = 2`
}

// IncElement calls a method with a pointer receiver on an element.
//
// @Requires |cs| = 2 And cs[0].n = 0 And cs[0].limit = 5 And cs[1].n = 0 And cs[1].limit = 5
// @Modifies cs
// @Ensures result = 2
func IncElement(cs []Counter) (result int) {
	cs[1].Inc()
	cs[1].Inc()
	return cs[0].n + cs[1].n
}

// IncElementUnlisted does so without saying that the slice changes.
//
// @Requires |cs| = 2 And cs[1].n = 0 And cs[1].limit = 5
func IncElementUnlisted(cs []Counter) {
	cs[1].Inc() // want `vego: .*may not modify.*`
}

// IncElementOutOfRange calls the method on an element that is not there.
//
// @Modifies cs
func IncElementOutOfRange(cs []Counter) {
	cs[0].Inc() // want `vego: index may be out of range` `vego: precondition of Inc may not hold: c.n < c.limit` `vego: precondition of Inc may not hold: c.limit <= 1000`
}

// ElementKept keeps a pointer to an element across a write to another.
//
// @Requires |ps| = 3 And ps[2].X = 9
// @Modifies ps
// @Ensures result = 9
func ElementKept(ps []Point) (result int) {
	last := &ps[2]
	ps[0].X = 1
	ps[1] = Point{X: 4, Y: 4}
	return last.X
}

// ElementOverwritten keeps a pointer to an element that is then replaced.
//
// @Requires |ps| = 3 And ps[2].X = 9
// @Modifies ps
// @Ensures result = 9
func ElementOverwritten(ps []Point) (result int) {
	last := &ps[2]
	ps[2] = Point{X: 4, Y: 4}
	return last.X // want `vego: postcondition may not hold: result = 9`
}

// AppendMoves appends to a slice an element pointer points into. Whether
// the pointer still points into the slice depends on the capacity.
//
// @Requires |ps| = 1 And ps[0].X = 9
// @Modifies ps
// @Ensures result = 9
func AppendMoves(ps []Point) (result int) {
	first := &ps[0]
	ps = append(ps, Point{})
	ps[0].X = 1
	return first.X // want `vego: postcondition may not hold: result = 9`
}

// LocalThroughPointer writes a variable through a pointer to it.
//
// @Ensures result = 7
func LocalThroughPointer() (result int) {
	x := Point{X: 1, Y: 2}
	p := &x
	p.X = 5
	return x.X + x.Y
}

// LocalThroughPointerWrong claims the variable kept its value.
//
// @Ensures result = 1
func LocalThroughPointerWrong() (result int) {
	x := Point{X: 1, Y: 2}
	p := &x
	p.X = 5
	return x.X // want `vego: postcondition may not hold: result = 1`
}

// PointerSeesLocal writes the variable and reads through the pointer.
//
// @Ensures result = 12
func PointerSeesLocal() (result int) {
	x := Point{X: 1}
	p := &x
	x.X = 8
	x = Point{X: x.X + 1, Y: 3}
	return p.X + p.Y
}

// PointerSeesLocalWrong claims the pointer kept the old value.
//
// @Ensures result = 1
func PointerSeesLocalWrong() (result int) {
	x := Point{X: 1}
	p := &x
	x.X = 8
	return p.X // want `vego: postcondition may not hold: result = 1`
}

// CopyOfLocal copies a variable whose address is taken; the copy is a
// value of its own.
//
// @Ensures result = 1
func CopyOfLocal() (result int) {
	x := Point{X: 1}
	p := &x
	y := x
	p.X = 5
	return y.X
}

// CopyOfLocalWrong claims the copy follows the variable.
//
// @Ensures result = 5
func CopyOfLocalWrong() (result int) {
	x := Point{X: 1}
	p := &x
	y := x
	p.X = 5
	return y.X // want `vego: postcondition may not hold: result = 5`
}

// LocalMethod calls a method with a pointer receiver on a variable.
//
// @Ensures result = 2
func LocalMethod() (result int) {
	c := Counter{limit: 3}
	c.Inc()
	c.Inc()
	return c.n
}

// LocalMethodWrong claims the variable was not changed.
//
// @Ensures result = 0
func LocalMethodWrong() (result int) {
	c := Counter{limit: 3}
	c.Inc()
	return c.n // want `vego: postcondition may not hold: result = 0`
}

// LocalMethodLimit calls the method more often than its contract allows.
//
// @Ensures result = 2
func LocalMethodLimit() (result int) {
	var c Counter
	c.limit = 1
	c.Inc()
	c.Inc() // want `vego: precondition of Inc may not hold: c\.n < c\.limit`
	return c.n
}

// LocalFieldMethod calls a method on a field of a variable.
//
// @Ensures result = 1
func LocalFieldMethod() (result int) {
	var cs Counters
	cs.B.limit = 4
	cs.B.Inc()
	return cs.A.n + cs.B.n
}

// PassLocal passes the address of a variable to a function that fills it.
//
// @Ensures result = 3
func PassLocal() (result int) {
	var r Ratio
	fill(&r)
	return r.Num + r.Den
}

// PassLocalWrong claims the variable is still zero.
//
// @Ensures result = 0
func PassLocalWrong() (result int) {
	var r Ratio
	fill(&r)
	return r.Num // want `vego: postcondition may not hold: result = 0`
}

// @Requires r != nil
// @Modifies r
// @Ensures r.Num' = 1 And r.Den' = 2
func fill(r *Ratio) {
	r.Num, r.Den = 1, 2
}

// ParamAddress takes the address of a parameter, which is a copy the
// caller does not see.
//
// @Ensures result = 4
func ParamAddress(p Point) (result int) {
	q := &p
	q.X = 4
	return p.X
}

// ParamAddressWrong claims the parameter kept the value it came with.
//
// @Requires p.X = 0
// @Ensures result = p.X
func ParamAddressWrong(p Point) (result int) {
	q := &p
	q.X = 4
	return p.X // want `vego: postcondition may not hold: result = p\.X`
}

// ReturnsLocal returns the address of a variable, which nobody else has.
//
// @Ensures fresh(result) And result.X = 3
func ReturnsLocal() (result *Point) {
	x := Point{X: 3}
	return &x
}

// NamedResultAddress fills a named result through a pointer.
//
// @Ensures r.Num = 1 And r.Den = 2
func NamedResultAddress() (r Ratio) {
	fill(&r)
	return
}

// LocalsApart takes the addresses of two variables, which differ.
//
// @Ensures ~result
func LocalsApart() (result bool) {
	var a, b Point
	return &a == &b
}

// LocalNotParam has a variable that no parameter points to.
//
// @Requires p != nil And p.X = 1
// @Ensures result = 1
func LocalNotParam(p *Point) (result int) {
	var x Point
	q := &x
	q.X = 9
	return p.X
}

// LocalInLoop writes a variable through a pointer inside a loop.
//
// @Requires 0 <= n <= 100
// @Ensures result = n
func LocalInLoop(n int) (result int) {
	var x Point
	p := &x
	// @Invariant 0 <= i <= n And x.X = i
	// @Variant n - i
	for i := 0; i < n; i++ {
		p.X++
	}
	return x.X
}

// LocalInLoopWrong claims the loop leaves the variable alone.
//
// @Requires 1 <= n <= 100
// @Ensures result = 0
func LocalInLoopWrong(n int) (result int) {
	var x Point
	p := &x
	// @Invariant 0 <= i <= n And x.X = i
	// @Variant n - i
	for i := 0; i < n; i++ {
		p.X++
	}
	return x.X // want `vego: postcondition may not hold: result = 0`
}

// LoopKeepsOther has a loop that writes one variable through a method and
// leaves another, of the same type, alone.
//
// @Requires 0 <= n <= 100
// @Ensures result = 7
func LoopKeepsOther(n int) (result int) {
	a := Counter{limit: 1000}
	b := Counter{n: 7, limit: 1000}
	q := &b
	// @Invariant 0 <= i <= n And a.n = i And a.limit = 1000
	// @Variant n - i
	for i := 0; i < n; i++ {
		a.Inc()
	}
	return q.n
}

// EachIteration declares a variable in a loop; every iteration has its
// own, so the pointers kept from two iterations differ.
//
// @Ensures ~result
func EachIteration() (result bool) {
	var first, second *Point
	// @Invariant 0 <= i <= 2 And (i >= 1 -> first != nil) And (i >= 2 -> second != nil And first != second)
	// @Variant 2 - i
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

// RangeAddress takes the address of the variable of a range loop, which is
// a copy of the element.
//
// @Requires |ps| > 0
// @Ensures Forall k in [0, |ps|) : ps'[k].X = ps[k].X
func RangeAddress(ps []Point) {
	// @Invariant Forall k in [0, |ps|) : ps[k].X = old(ps[k].X)
	for _, p := range ps {
		q := &p
		q.X = 0
	}
}

// AddressOfInt takes the address of a number, which then lives in a box
// of its own (F37).
//
// @Ensures result = 1
func AddressOfInt() (result int) {
	x := 1
	p := &x
	return *p
}

// SetOneField lists one field of one element.
//
// @Requires |ps| > 2
// @Modifies ps[1].X
// @Ensures ps'[1].X = 3
func SetOneField(ps []Point) {
	ps[1].X = 3
}

// UsesSetOneField relies on everything else being kept.
//
// @Requires |ps| > 2 And ps[1].Y = 4 And ps[2].X = 5
// @Modifies ps
// @Ensures result = 12
func UsesSetOneField(ps []Point) (result int) {
	SetOneField(ps)
	return ps[1].X + ps[1].Y + ps[2].X
}

// UsesSetOneFieldWrong relies on the field that was written.
//
// @Requires |ps| > 2 And ps[1].X = 4
// @Modifies ps
// @Ensures result = 4
func UsesSetOneFieldWrong(ps []Point) (result int) {
	SetOneField(ps)
	return ps[1].X // want `vego: postcondition may not hold: result = 4`
}

// FromOnly lists one struct inside another and writes it through a pointer.
//
// @Requires s != nil
// @Modifies s.From
// @Ensures s.From.X' = 1 And s.To.X' = s.To.X
func FromOnly(s *Segment) {
	p := &s.From
	p.X = 1
	p.Y = 2
}

// FromOnlyWrong writes the struct next to the one it listed.
//
// @Requires s != nil
// @Modifies s.From
func FromOnlyWrong(s *Segment) {
	p := &s.To
	p.X = 1 // want `vego: p\.X is assigned, which FromOnlyWrong may not modify; list it in a // @Modifies clause, as s\.To\.X`
}

// BumpEach changes each element through a pointer to it.
//
// @Requires Forall k in [0, |ps|) : 0 <= ps[k].X <= 100
// @Modifies ps
// @Ensures Forall k in [0, |ps|) : ps'[k].X = ps[k].X + 1
func BumpEach(ps []Point) {
	// @Invariant 0 <= i <= |ps|
	// @Invariant Forall k in [0, i) : ps[k].X = old(ps[k].X) + 1
	// @Invariant Forall k in [i, |ps|) : ps[k].X = old(ps[k].X)
	for i := range ps {
		p := &ps[i]
		p.X++
	}
}

// BumpEachWrong claims a different amount.
//
// @Requires Forall k in [0, |ps|) : 0 <= ps[k].X <= 100
// @Modifies ps
// @Ensures Forall k in [0, |ps|) : ps'[k].X = ps[k].X + 2
func BumpEachWrong(ps []Point) {
	// @Invariant 0 <= i <= |ps|
	// @Invariant Forall k in [0, i) : ps[k].X = old(ps[k].X) + 1
	// @Invariant Forall k in [i, |ps|) : ps[k].X = old(ps[k].X)
	for i := range ps {
		p := &ps[i]
		p.X++
	}
} // want `vego: postcondition may not hold: Forall k in \[0, \|ps\|\) : ps'\[k\]\.X = ps\[k\]\.X \+ 2`

// SwapPoints exchanges two structs that may be one.
//
// @Requires a != nil And b != nil
// @Modifies a, b
// @Ensures a.X' = b.X And b.X' = a.X And a.Y' = b.Y And b.Y' = a.Y
func SwapPoints(a, b *Point) {
	*a, *b = *b, *a
}

// SwapEnds passes pointers to two elements.
//
// @Requires |ps| > 1
// @Modifies ps
// @Ensures ps'[0].X = ps[|ps|-1].X And ps'[|ps|-1].Y = ps[0].Y
func SwapEnds(ps []Point) {
	SwapPoints(&ps[0], &ps[len(ps)-1])
}

// SwapEndsWrong claims the first element stayed.
//
// @Requires |ps| > 1
// @Modifies ps
// @Ensures ps'[0].X = ps[0].X
func SwapEndsWrong(ps []Point) {
	SwapPoints(&ps[0], &ps[len(ps)-1])
} // want `vego: postcondition may not hold: ps'\[0\]\.X = ps\[0\]\.X`

// positive reports whether a point has a positive X.
//
// @Requires p != nil
// @Ensures result <-> p.X > 0
func positive(p *Point) (result bool) {
	return p.X > 0
}

// GuardedAddress takes the address of an element only when there is one.
//
// @Ensures result <-> |ps| > 0 And ps[0].X > 0
func GuardedAddress(ps []Point) (result bool) {
	return len(ps) > 0 && positive(&ps[0])
}

// UnguardedAddress takes it in any case.
//
// @Ensures result <-> |ps| > 0 And ps[0].X > 0
func UnguardedAddress(ps []Point) (result bool) {
	return len(ps) >= 0 && positive(&ps[0]) // want `vego: index may be out of range`
}

// GuardedField takes the address of a field when the pointer is not nil.
//
// @Ensures result <-> s != nil And s.To.X > 0
func GuardedField(s *Segment) (result bool) {
	return s != nil && positive(&s.To)
}

// UnguardedField takes it on the wrong side of the test.
//
// @Ensures result <-> s = nil Or s.To.X > 0
func UnguardedField(s *Segment) (result bool) {
	return s == nil || positive(&s.To)
}

// WrongGuardField takes it when the pointer is nil.
//
// @Ensures ~result
func WrongGuardField(s *Segment) (result bool) {
	return s == nil && positive(&s.To) // want `vego: pointer may be nil`
}

// ManyNothings takes a slice whose elements have no size, which can be
// longer than any allocation.
//
// @Ensures result
func ManyNothings(s []struct{}) (result bool) {
	return len(s) <= 281474976710656 // want `vego: postcondition may not hold: result`
}

// CountNothings relies on what is known of such a slice: its length is an
// int that is not negative.
//
// @Ensures result
func CountNothings(s []struct{}) (result bool) {
	return len(s) >= 0 && len(s)/2 <= len(s)
}

// MakeNothings makes a slice that needs no memory.
//
// @Requires 0 <= n
// @Ensures result = n
func MakeNothings(n int) (result int) {
	s := make([]struct{}, n)
	return len(s)
}

// Wired has a field of a type that is not modelled. The field cannot be
// used, but it is part of the struct all the same.
type Wired struct {
	X int
	C chan int
}

// OverwriteWired replaces the whole struct, and with it the field that is
// not modelled, which the clause does not list.
//
// @Requires p != nil
// @Modifies p.X
// @Ensures p.X' = 1
func OverwriteWired(p *Wired) {
	*p = Wired{X: 1} // want `vego: \*p is assigned, which OverwriteWired may not modify: nothing its // @Modifies clauses list is known to cover it; a clause covers what its path referred to when OverwriteWired was called`
}

// OverwriteWiredListed lists the struct.
//
// @Requires p != nil
// @Modifies p
// @Ensures p.X' = 1
func OverwriteWiredListed(p *Wired) {
	*p = Wired{X: 1}
}

// SetWiredX writes the one field it lists.
//
// @Requires p != nil
// @Modifies p.X
// @Ensures p.X' = 1
func SetWiredX(p *Wired) {
	p.X = 1
}

// CopyWired copies a struct with such a field through a call that may
// write all of it, which the caller did not list.
//
// @Requires p != nil
// @Modifies p.X
func CopyWired(p *Wired) {
	OverwriteWiredListed(p) // want `vego: OverwriteWiredListed may modify p, which CopyWired may not modify: nothing its // @Modifies clauses list is known to cover it; a clause covers what its path referred to when CopyWired was called`
}

// EachField lists the fields of a struct one by one and then writes the
// struct as a whole.
//
// @Requires p != nil
// @Modifies p.X, p.Y
// @Ensures p.X' = 1 And p.Y' = 2
func EachField(p *Point) {
	*p = Point{X: 1, Y: 2}
}

// OneOfTwoFields lists only one of them.
//
// @Requires p != nil
// @Modifies p.X
func OneOfTwoFields(p *Point) {
	*p = Point{X: 1, Y: 2} // want `vego: \*p is assigned, which OneOfTwoFields may not modify: nothing its // @Modifies clauses list is known to cover it; a clause covers what its path referred to when OneOfTwoFields was called`
}

// SpareField lists a field that the function never writes.
//
// @Requires p != nil
// @Modifies p.X, p.Y // want `vego: Modifies lists p\.Y, but SpareField never needs to modify it.*`
// @Ensures p.X' = 1
func SpareField(p *Point) {
	p.X = 1
}

// ReturnAssigns returns a value for a named result that a pointer points
// to. Returning assigns the result, so the pointer sees the value.
//
// @Ensures r.X = 1 And p.X = 1
func ReturnAssigns() (r Point, p *Point) {
	p = &r
	return Point{X: 1}, p
}

// ReturnAssignsWrong claims the pointer still sees the old value.
//
// @Ensures r.X = 1 And p.X = 0
func ReturnAssignsWrong() (r Point, p *Point) {
	p = &r
	return Point{X: 1}, p // want `vego: postcondition may not hold: p\.X = 0`
}

// pick returns some index below two; which one is not said.
//
// @Ensures 0 <= result < 2
func pick() (result int) { return 1 }

// IncPicked calls a method on an element chosen by a call. The call is
// evaluated once, so exactly one counter advances.
//
// @Requires |cs| = 2 And cs[0].n = 0 And cs[0].limit = 5 And cs[1].n = 0 And cs[1].limit = 5
// @Modifies cs
// @Ensures result = 1
func IncPicked(cs []Counter) (result int) {
	cs[pick()].Inc()
	return cs[0].n + cs[1].n
}

// IncPickedWrong claims to know which one.
//
// @Requires |cs| = 2 And cs[0].n = 0 And cs[0].limit = 5 And cs[1].n = 0 And cs[1].limit = 5
// @Modifies cs
// @Ensures result = 1
func IncPickedWrong(cs []Counter) (result int) {
	cs[pick()].Inc()
	return cs[1].n // want `vego: postcondition may not hold: result = 1`
}

// LoopVariableKept keeps a pointer to the variable of a for loop. Every
// iteration has a variable of its own, so the pointer stays at the one of
// the last iteration that ran, which the post statement did not advance.
//
// @Ensures result = 1
func LoopVariableKept() (result int) {
	var p *Point
	// @Invariant 0 <= x.X <= 2
	// @Invariant x.X > 0 -> (p != nil And p.X = x.X - 1)
	// @Variant 2 - x.X
	for x := (Point{}); x.X < 2; x.X++ {
		p = &x
	}
	return p.X
}

// LoopVariableShared claims that the iterations share one variable.
//
// @Ensures result = 2
func LoopVariableShared() (result int) {
	var p *Point
	// @Invariant 0 <= x.X <= 2
	// @Invariant x.X > 0 -> (p != nil And p.X = x.X)
	// @Variant 2 - x.X
	for x := (Point{}); x.X < 2; x.X++ { // want `vego: loop invariant may not be preserved: x\.X > 0 -> \(p != nil And p\.X = x\.X\)`
		p = &x
	}
	return p.X
}

// LoopVariableCounts uses such a variable only inside the loop.
//
// @Requires 0 <= n <= 100
// @Ensures result = n
func LoopVariableCounts(n int) (result int) {
	total := 0
	// @Invariant 0 <= c.n <= n And c.limit = n And total = c.n
	// @Variant n - c.n
	for c := (Counter{limit: n}); c.n < n; c.Inc() {
		total++
	}
	return total
}

// Cell and Cells put the same field of two structs side by side.
type Cell struct{ X byte }

// Cells holds two cells.
type Cells struct{ A, B Cell }

// BothCells lists the same field of two structs that lie side by side and
// then writes the struct that holds them.
//
// @Requires p != nil
// @Modifies p.A.X, p.B.X
// @Ensures p.A.X' = 1 And p.B.X' = 2
func BothCells(p *Cells) {
	*p = Cells{A: Cell{X: 1}, B: Cell{X: 2}}
}

// OneCell lists only one of them.
//
// @Requires p != nil
// @Modifies p.A.X
func OneCell(p *Cells) {
	*p = Cells{A: Cell{X: 1}, B: Cell{X: 2}} // want `vego: \*p is assigned, which OneCell may not modify: nothing its // @Modifies clauses list is known to cover it; a clause covers what its path referred to when OneCell was called`
}

// EndsOnly lists two elements and writes the one between them.
//
// @Requires |ps| = 3
// @Modifies ps[0], ps[2]
func EndsOnly(ps []Point) {
	ps[0].X = 1
	ps[2].X = 1
	ps[1].X = 1 // want `vego: ps\[1\]\.X is assigned, which EndsOnly may not modify: nothing its // @Modifies clauses list is known to cover it; a clause covers what its path referred to when EndsOnly was called`
}

// ReplaceFirst appends into the capacity of a slice it emptied, which
// writes the one element it listed.
//
// @Requires |ps| = 1
// @Modifies ps[0]
// @Ensures |result| = 1 And result[0].X = 1
func ReplaceFirst(ps []Point) (result []Point) {
	ps = ps[:0]
	return append(ps, Point{X: 1})
}

// ReplaceSecond appends to the slice as it is, which writes past the one
// element it listed when there is room.
//
// @Requires |ps| = 1
// @Modifies ps[0]
// @Ensures |result| = 2
func ReplaceSecond(ps []Point) (result []Point) {
	return append(ps, Point{X: 1}) // want `vego: append may write into the capacity of ps, which ReplaceSecond may not modify: nothing its // @Modifies clauses list is known to cover it; a clause covers what its path referred to when ReplaceSecond was called`
}

// setIfPresent writes through its pointer unless it is nil.
//
// @Modifies p.X
// @Ensures p != nil -> p.X' = 1
func setIfPresent(p *Point) {
	if p != nil {
		p.X = 1
	}
}

// PassNil passes nil, through which nothing can be written.
//
// @Ensures result = 0
func PassNil() (result int) {
	setIfPresent(nil)
	return 0
}

// PassMaybeNil passes a pointer that may or may not be nil and that it may
// not write through.
//
// @Ensures True
func PassMaybeNil(p *Point) {
	setIfPresent(p) // want `vego: setIfPresent may modify what it calls p\.X, which PassMaybeNil may not modify; list it in a // @Modifies clause`
}

// Boxed holds an array, which a slice can be a second view of.
type Boxed struct{ A [1]int }

// ResetBoxed overwrites the struct, and with it the array that the slice
// may be a view of, so the claim is not proved: it is false when s is
// p.A[:] (TestResetBoxed).
//
// @Requires p != nil And |s| = 1 And s[0] = 7
// @Modifies p
// @Ensures result = 7
func ResetBoxed(p *Boxed, s []int) (result int) {
	*p = Boxed{}
	return s[0] // want `vego: postcondition may not hold: result = 7`
}

// Padded has an array nobody can name, which is no obstacle.
type Padded struct {
	X int
	_ [4]int
}

// SetPadded uses such a struct.
//
// @Requires p != nil
// @Modifies p
// @Ensures p.X' = 1
func SetPadded(p *Padded) {
	*p = Padded{X: 1}
}

// Nothings returns pointers into two arrays of elements without size,
// which may be at one address.
//
// @Ensures p != q // want `vego: in Ensures annotation: pointers to values of size zero may or may not be equal, so they can only be compared with nil`
func Nothings() (p, q *struct{}) {
	a := make([]struct{}, 1)
	b := make([]struct{}, 1)
	return &a[0], &b[0]
}

// NothingsNotNil compares such pointers with nil only.
//
// @Ensures p != nil And q != nil
func NothingsNotNil() (p, q *struct{}) {
	a := make([]struct{}, 1)
	b := make([]struct{}, 1)
	return &a[0], &b[0]
}

// GrowNothings grows a slice of elements without size in a loop. Where
// its array is says nothing, so it may be where q points.
//
// @Requires q != nil
// @Ensures ~within(result, q)
func GrowNothings(q *struct{}) (result *struct{}) {
	var s []struct{}
	// @Invariant 0 <= i <= 1 And |s| = i
	// @Variant 1 - i
	for i := 0; i < 1; i++ {
		s = append(s, struct{}{})
	}
	return &s[0] // want `vego: postcondition may not hold: ~within\(result, q\)`
}

// GrowPoints does the same with elements that have a size, whose new
// array is apart from everything that was there before.
//
// @Requires q != nil
// @Ensures ~within(result, q)
func GrowPoints(q *Point) (result *Point) {
	var s []Point
	// @Invariant 0 <= i <= 1 And |s| = i
	// @Variant 1 - i
	for i := 0; i < 1; i++ {
		s = append(s, Point{})
	}
	return &s[0]
}

// TooManyNothings appends to a slice that already has as many elements as
// an int can count, which panics.
//
// @Ensures result = 1
func TooManyNothings() (result int) {
	s := make([]struct{}, 9223372036854775807)
	s = append(s, struct{}{}) // want `vego: .*may be more than can be allocated`
	return 0
}

// OneMoreNothing appends where there is room to count.
//
// @Requires 0 <= n < 1000
// @Ensures result = n + 1
func OneMoreNothing(n int) (result int) {
	s := make([]struct{}, n)
	s = append(s, struct{}{})
	return len(s)
}

// PointerOrMap compares a pointer with a map, which are different things.
//
// @Requires p = m // want `vego: in Requires annotation: a pointer can only be compared with a pointer or with nil`
func PointerOrMap(p *Point, m map[int]int) {}

// NothingOrMap does so with a pointer to a value without size.
//
// @Requires p = m // want `vego: in Requires annotation: a pointer can only be compared with a pointer or with nil`
func NothingOrMap(p *struct{}, m map[int]int) {}

// SameMap compares two maps, which is fine.
//
// @Requires m = n
// @Ensures result
func SameMap(m, n map[int]int) (result bool) {
	return len(m) == len(n)
}
