// Package sourcecalls holds functions whose parameters of unnamed function
// types have a contract under Calls, and their callers.
package sourcecalls

// each calls f with every element of xs.
//
// @Calls f(x) When 0 <= x < 100
// @Requires Forall i in [0, |xs|) : 0 <= xs[i] < 100
// @Ensures True
func each(xs []int, f func(int)) {
	for _, x := range xs {
		f(x)
	}
}

// Sum adds the elements through a literal that assigns a variable of its
// own. What the runs assign is forgotten after the call, as a loop forgets
// what its body assigns, so nothing more is promised.
//
// @Requires Forall i in [0, |xs|) : 0 <= xs[i] < 100
// @Ensures True
func Sum(xs []int) (s int) {
	total := 0
	each(xs, func(x int) {
		if total < 1000000 {
			total += x
		}
	})
	return total
}

// filter keeps the strings keep accepts.
//
// @Calls keep(s)
// @Requires |xs| <= 1000000
// @Ensures |out| <= |xs|
func filter(xs []string, keep func(string) bool) (out []string) {
	// @Invariant |out| <= i
	for i, x := range xs {
		if keep(x) {
			out = append(out, x)
		}
		_ = i
	}
	return out
}

// NonEmpty hands filter a literal that reads nothing of its own.
//
// @Requires |xs| <= 1000000
// @Ensures |r| <= |xs|
func NonEmpty(xs []string) (r []string) {
	return filter(xs, func(s string) bool { return s != "" })
}

type counter struct{ n int }

// @Requires c != nil And 0 <= x < 100
// @Modifies c
// @Ensures True
func (c *counter) add(x int) {
	if c.n < 1000000 {
		c.n += x
	}
}

// @Requires 0 <= x < 100
// @Ensures True
func check(x int) {}

// Handed hands each a method value and a function.
//
// @Requires c != nil And Forall i in [0, |xs|) : 0 <= xs[i] < 100
// @Modifies c
// @Ensures True
func Handed(xs []int, c *counter) {
	each(xs, c.add)
	each(xs, check)
}

// Nested calls each in a literal handed to each.
//
// @Requires Forall i in [0, |xs|) : 0 <= xs[i] < 100
// @Ensures True
func Nested(xs []int) {
	n := 0
	each(xs, func(x int) {
		each(xs, func(y int) {
			if n < 1000000 {
				n++
			}
		})
	})
}

// keepsDirect reads, after a call of f, what its slice refers to: f may
// not write it.
//
// @Calls f()
// @Requires |xs| = 2 And xs[0] = 7
// @Ensures r = 7
func keepsDirect(xs []int, f func()) (r int) {
	ys := xs[1:2]
	f()
	_ = ys[0]
	return xs[0]
}

// keepsWritten reads, after a call of f, what it wrote and may write: f
// may not write it.
//
// @Calls f()
// @Requires |xs| = 2
// @Modifies xs
// @Ensures r = 9
func keepsWritten(xs []int, f func()) (r int) {
	xs[1] = 9
	f()
	return xs[1]
}

// try returns what f returns: a call of f is a source of unpredictable
// failure, so the contract need not say when it succeeds (F13).
//
// @Calls f()
// @Ensures True
func try(f func() (err error)) (err error) {
	return f()
}

// Any hands f an interface value, which a literal can only use as vego
// models it.
//
// @Calls f(x)
// @Ensures True
func Any(v any, f func(any)) {
	f(v)
}

// @Ensures True
func HandsAny() {
	Any(3, func(x any) {})
}

// twice has two function parameters, handed the same function.
//
// @Calls f(x) When 0 <= x
// @Calls g(x) When 0 <= x
// @Ensures True
func twice(f func(int), g func(int)) {
	f(1)
	g(2)
}

// @Requires 0 <= x
// @Ensures True
func positive(x int) {}

// @Ensures True
func Twice() {
	twice(positive, positive)
}

type elem struct{ n int }

// eachElem calls f with each element of xs, which its When says of each
// argument: an element xs held when eachElem was called.
//
// @Calls f(p) When Exists k in [0, |xs|) : p = old(xs[k])
// @Ensures True
func eachElem(xs []*elem, f func(*elem)) {
	// @Invariant 0 <= i
	for i := range xs {
		f(xs[i])
	}
}

// Elems reads each element eachElem hands with no nil test.
//
// @Requires Forall i in [0, |xs|) : xs[i] != nil
// @Ensures True
func Elems(xs []*elem) {
	eachElem(xs, func(p *elem) {
		_ = p.n
	})
}
