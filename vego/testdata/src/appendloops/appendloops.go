// Package appendloops appends in a loop to a slice in memory: a field
// reached through a pointer and what a pointer to a slice points to (F42).
// The verifier adds the invariant that the slice is in its array or in one
// made since where nothing else in the loop can write it.
package appendloops

// B holds items.
type B struct {
	Items []int
	n     int
}

// FillField appends n numbers to a field.
//
// @Requires b != nil And 0 <= n < 1000 And |b.Items| < 1000
// @Modifies b, b.Items
// @Ensures |b.Items'| = |b.Items| + n And b.n' = b.n
func FillField(b *B, n int) {
	// @Invariant 0 <= i <= n And |b.Items| = |old(b.Items)| + i And b.n = old(b.n)
	// @Variant n - i
	for i := 0; i < n; i++ {
		b.Items = append(b.Items, i)
	}
}

// Fill appends n numbers through a pointer to a slice.
//
// @Requires out != nil And 0 <= n < 1000 And |*out| < 1000
// @Modifies out, *out
// @Ensures |*out'| = |*out| + n
func Fill(out *[]int, n int) {
	// @Invariant 0 <= i <= n And |*out| = |old(*out)| + i
	// @Variant n - i
	for i := 0; i < n; i++ {
		*out = append(*out, i)
	}
}

// MadeHere appends n numbers to a field of a struct made here.
//
// @Requires 0 <= n < 1000
// @Ensures |r| = n
func MadeHere(n int) (r []int) {
	b := &B{}
	// @Invariant 0 <= i <= n And |b.Items| = i
	// @Variant n - i
	for i := 0; i < n; i++ {
		b.Items = append(b.Items, i)
	}
	return b.Items
}

// Doubles appends the slice to itself.
//
// @Requires b != nil And 0 <= n < 10 And |b.Items| < 100
// @Modifies b, b.Items
// @Ensures True
func Doubles(b *B, n int) {
	// @Invariant 0 <= i <= n And |b.Items| < 200
	// @Variant n - i
	for i := 0; i < n && len(b.Items) < 100; i++ {
		b.Items = append(b.Items, b.Items...)
	}
}

// Rows appends a number for each pair, and skips the rest of a row with a
// labelled continue, which is a back edge of the outer loop too.
//
// @Requires b != nil And 0 <= n < 100 And |b.Items| < 1000
// @Modifies b, b.Items
// @Ensures True
func Rows(b *B, n int) {
	// @Invariant 0 <= i <= n And |b.Items| <= |old(b.Items)| + i
	// @Variant n - i
outer:
	for i := 0; i < n; i++ {
		// @Invariant 0 <= j <= n And |b.Items| <= |old(b.Items)| + i
		// @Variant n - j
		for j := 0; j < n; j++ {
			if j == 1 {
				b.Items = append(b.Items, i)
				continue outer
			}
		}
	}
}

// Overwrites appends to b.Items and also stores through q, which may point
// to b.Items: then b.Items is neither in its array nor in a new one at the
// end of an iteration, so the invariant is not added, and the append is
// refused as before.
//
// @Requires b != nil And q != nil And 0 <= n < 1000 And |b.Items| < 1000 And |other| < 10
// @Modifies b, b.Items, q
// @Ensures True
func Overwrites(b *B, q *[]int, other []int, n int) {
	// @Invariant 0 <= i <= n And |b.Items| <= |old(b.Items)| + i + 10
	// @Variant n - i
	for i := 0; i < n; i++ {
		b.Items = append(b.Items, i) // want `vego: append may write into the capacity of b\.Items, which Overwrites may not modify`
		*q = other
	}
}

// logs counts.
//
// @Requires b != nil And b.n < 1000000
// @Modifies b.n
// @Ensures b.n' = b.n + 1
func logs(b *B) {
	b.n++
}

// WithCall appends beside a call that may write, so the invariant is not
// added and the append is refused as before.
//
// @Requires b != nil And 0 <= n < 1000 And |b.Items| < 1000 And b.n < 1000
// @Modifies b, b.Items
// @Ensures True
func WithCall(b *B, n int) {
	// @Invariant 0 <= i <= n And b.n = old(b.n) + i And |b.Items| = |old(b.Items)| + i
	// @Variant n - i
	for i := 0; i < n; i++ {
		b.Items = append(b.Items, i) // want `vego: append may write into the capacity of b\.Items, which WithCall may not modify`
		logs(b)
	}
}

// WithCallSaid writes the invariant itself, with within and old.
//
// @Requires b != nil And 0 <= n < 1000 And |b.Items| < 1000 And b.n < 1000
// @Modifies b, b.Items
// @Ensures True
func WithCallSaid(b *B, n int) {
	// @Invariant 0 <= i <= n And b.n = old(b.n) + i And |b.Items| = |old(b.Items)| + i
	// @Invariant fresh(b.Items) Or within(b.Items, old(b.Items))
	// @Variant n - i
	for i := 0; i < n; i++ {
		b.Items = append(b.Items, i)
		logs(b)
	}
}

// Replaced claims that a slice made here lies within the one it had on
// entry.
//
// @Requires b != nil
// @Modifies b
// @Ensures True
func Replaced(b *B) {
	b.Items = make([]int, 1)
	// @Assert within(b.Items, old(b.Items)) // want `vego: assertion may not hold: within\(b\.Items, old\(b\.Items\)\)`
}

// Kept says that the slice is still apart from another one it was apart
// from on entry.
//
// @Requires b != nil And apart(b.Items, ys)
// @Modifies b
// @Ensures True
func Kept(b *B, ys []int) {
	b.n = 1
	// @Assert apart(ys, old(b.Items))
}

// Each appends to a field of each struct in turn, through a variable each
// iteration sets: the place is another one at each iteration, so the
// invariant is not added and the append is refused as before.
//
// @Requires b != nil And c != nil And |b.Items| < 1000 And |c.Items| < 1000
// @Modifies b, b.Items, c, c.Items
// @Ensures True
func Each(b, c *B) {
	// @Invariant |b.Items| <= |old(b.Items)| + i And |c.Items| <= |old(c.Items)| + i
	for i, p := range []*B{b, c} {
		p.Items = append(p.Items, i) // want `vego: append may write into the capacity of p\.Items, which Each may not modify`
	}
}

// Moved appends through a pointer the loop moves to another struct.
//
// @Requires b != nil And c != nil And 0 <= n < 1000 And |b.Items| < 1000 And |c.Items| < 1000
// @Modifies b, b.Items, c, c.Items
// @Ensures True
func Moved(b, c *B, n int) {
	p := b
	// @Invariant 0 <= i <= n And (p = b Or p = c)
	// @Invariant |b.Items| <= |old(b.Items)| + i And |c.Items| <= |old(c.Items)| + i
	// @Variant n - i
	for i := 0; i < n; i++ {
		p.Items = append(p.Items, i) // want `vego: append may write into the capacity of p\.Items, which Moved may not modify`
		p = c
	}
}

// Reset appends to b.Items and also assigns it otherwise.
//
// @Requires b != nil And 0 <= n < 1000 And |b.Items| < 1000
// @Modifies b, b.Items
// @Ensures True
func Reset(b *B, n int) {
	// @Invariant 0 <= i <= n And |b.Items| <= |old(b.Items)| + i
	// @Variant n - i
	for i := 0; i < n; i++ {
		b.Items = append(b.Items, i) // want `vego: append may write into the capacity of b\.Items, which Reset may not modify`
		b.Items = b.Items[:len(b.Items)-1]
	}
}

// Shared appends to two fields that may share an array: each append writes
// into the capacity of its own slice, which the contract names.
//
// @Requires b != nil And c != nil And 0 <= n < 1000 And |b.Items| < 1000 And |c.Items| < 1000
// @Modifies b, b.Items, c, c.Items
// @Ensures True
func Shared(b, c *B, n int) {
	// @Invariant 0 <= i <= n And |b.Items| <= |old(b.Items)| + 2 * i And |c.Items| <= |old(c.Items)| + 2 * i
	// @Variant n - i
	for i := 0; i < n; i++ {
		b.Items = append(b.Items, i)
		c.Items = append(c.Items, i)
	}
}

// Skips appends on odd i only, and goes on past the append on even i.
//
// @Requires b != nil And 0 <= n < 1000 And |b.Items| < 1000
// @Modifies b, b.Items
// @Ensures |b.Items'| <= |b.Items| + n
func Skips(b *B, n int) {
	// @Invariant 0 <= i <= n And |b.Items| <= |old(b.Items)| + i
	// @Variant n - i
	for i := 0; i < n; i++ {
		if i%2 == 0 {
			continue
		}
		b.Items = append(b.Items, i)
	}
}

// Spare loses what it stored in the spare capacity of b.Items, which
// FillField may write.
//
// @Ensures True
func Spare() {
	x := make([]int, 1, 10)
	b := &B{Items: x[:1]}
	y := x[1:2]
	y[0] = 5
	FillField(b, 3)
	// @Assert y[0] = 5 // want `vego: assertion may not hold: y\[0\] = 5`
}

// Lost claims that a slice is apart from another one it was not said to be
// apart from on entry.
//
// @Requires b != nil
// @Modifies b
// @Ensures True
func Lost(b *B, ys []int) {
	b.n = 1
	// @Assert apart(ys, old(b.Items)) // want `vego: assertion may not hold: apart\(ys, old\(b\.Items\)\)`
}

// InContract says within with old in a contract, where old(b.Items) is
// b.Items on entry as b.Items is.
//
// @Requires b != nil
// @Modifies b
// @Ensures within(b.Items', old(b.Items))
func InContract(b *B) {
	b.n = 1
}

// OfLocal says within with old of a local, which has no value on entry.
//
// @Requires b != nil
// @Modifies b
// @Ensures True
func OfLocal(b *B) {
	k := b.Items
	b.n = 1
	// @Assert within(b.Items, old(k)) // want `vego: in Assert annotation: old\(k\): k is not a parameter`
	_ = k
}

// Cleared appends to b.Items and stores the whole struct, which writes
// b.Items too: the invariant is not added, and the append is refused as
// before. The append writes into the spare capacity of c.Items, which
// Cleared does not list.
//
// @Requires b != nil And c != nil And b != c And 0 <= n < 1000 And |c.Items| < 1000
// @Modifies b, b.Items
// @Ensures True
func Cleared(b, c *B, n int) {
	// @Invariant 0 <= i <= n
	// @Variant n - i
	for i := 0; i < n; i++ {
		*b = *c
		b.Items = append(b.Items, i) // want `vego: append may write into the capacity of b\.Items, which Cleared may not modify`
	}
}

// Holder holds a B by value.
type Holder struct {
	In B
}

// ClearedIn stores a struct that holds the place, and then appends to a nil
// slice, which allocates.
//
// @Requires h != nil And 0 <= n < 1000
// @Modifies h
// @Ensures True
func ClearedIn(h *Holder, n int) {
	// @Invariant 0 <= i <= n And (i = 0 Or |h.In.Items| <= 1)
	// @Variant n - i
	for i := 0; i < n; i++ {
		h.In = B{}
		h.In.Items = append(h.In.Items, i)
	}
}
