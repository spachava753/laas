package guide

// The programs of the section on pointers to numbers, booleans, and
// strings.

// Increment increments what p points to.
//
// @Requires p != nil And *p < 1000
// @Modifies p
// @Ensures *p' = *p + 1
func Increment(p *int) {
	*p = *p + 1
}

// @Ensures r = 6
func IncrementLocal() (r int) {
	x := 5
	Increment(&x)
	return x
}

// @Requires p != nil And q != nil
// @Modifies p, q
// @Ensures *p' = *q And *q' = *p
func SwapInts(p, q *int) {
	*p, *q = *q, *p
}

// Options has a limit that may be absent.
type Options struct {
	Limit *int
}

// @Ensures o.Limit != nil -> n = *o.Limit
// @Ensures o.Limit = nil -> n = d
func LimitOr(o Options, d int) (n int) {
	if o.Limit != nil {
		n = *o.Limit
	} else {
		n = d
	}
	return n
}

// Clicks counts clicks.
type Clicks int

// @Requires t != nil And *t < 100
// @Modifies t
// @Ensures *t' = *t + 1
func (t *Clicks) Add() {
	*t++
}

// @Ensures r = 2
func CountTwice() (r Clicks) {
	var t Clicks
	t.Add()
	t.Add()
	return t
}

// Span holds two numbers.
type Span struct{ lo, hi int }

// @Ensures r = 1 And s = 0
func AddressOfField() (r, s int) {
	var b Span
	Increment(&b.lo)
	return b.lo, b.hi
}

// @Requires p != nil And b != nil
// @Modifies p, b
// @Ensures b.lo' = 1
func OverwriteLo(p *int, b *Span) {
	b.lo = 1
	*p = 2
} // want `vego: postcondition may not hold: b\.lo' = 1`

// @Requires p != nil And b != nil And apart(p, b)
// @Modifies p, b
// @Ensures b.lo' = 1
func KeepHi(p *int, b *Span) {
	b.lo = 1
	*p = 2
}

// @Ensures True
func KeepHiSame() {
	var b Span
	KeepHi(&b.lo, &b) // want `vego: precondition of KeepHi may not hold: apart\(p, b\)`
}

// @Requires out != nil And |*out| < 1000
// @Modifies out, *out
// @Ensures |*out'| = |*out| + 1 And (*out')[|*out|] = s
// @Ensures Forall i in [0, |*out|) : (*out')[i] = (*out)[i]
// @Ensures fresh(*out) Or within(*out', *out)
func AppendTo(out *[]string, s string) {
	*out = append(*out, s)
}

// @Ensures |r| = 2 And r[0] = "a" And r[1] = "b"
func CollectTwo() (r []string) {
	var xs []string
	AppendTo(&xs, "a")
	AppendTo(&xs, "b")
	return xs
}
