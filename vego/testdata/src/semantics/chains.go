package semantics

import (
	"bufio"
	"bytes"
)

// Each function below repeats one operation 30 times. If the rule for the
// operation put its operand into the result more than once, what the
// verifier builds would double at each step, and the bound on the size of
// a formula would refuse the function at once.

// MaxChain keeps the largest of its arguments, one at a time.
//
// @Ensures r >= a0 And r >= a29
func MaxChain(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29 int) (r int) {
	m := a0
	m = max(m, a1)
	m = max(m, a2)
	m = max(m, a3)
	m = max(m, a4)
	m = max(m, a5)
	m = max(m, a6)
	m = max(m, a7)
	m = max(m, a8)
	m = max(m, a9)
	m = max(m, a10)
	m = max(m, a11)
	m = max(m, a12)
	m = max(m, a13)
	m = max(m, a14)
	m = max(m, a15)
	m = max(m, a16)
	m = max(m, a17)
	m = max(m, a18)
	m = max(m, a19)
	m = max(m, a20)
	m = max(m, a21)
	m = max(m, a22)
	m = max(m, a23)
	m = max(m, a24)
	m = max(m, a25)
	m = max(m, a26)
	m = max(m, a27)
	m = max(m, a28)
	m = max(m, a29)
	return m
}

// MaxAll takes the largest of its arguments at once.
//
// @Ensures r >= a0 And r >= a29
func MaxAll(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29 int) (r int) {
	return max(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29)
}

// ShiftChain halves a signed number again and again, rounding down.
//
// @Requires -8 <= x <= 8
// @Ensures -1 <= r <= 0
func ShiftChain(x int) (r int) {
	x >>= 1
	x >>= 1
	x >>= 1
	x >>= 1
	x >>= 1
	x >>= 1
	x >>= 1
	x >>= 1
	x >>= 1
	x >>= 1
	x >>= 1
	x >>= 1
	x >>= 1
	x >>= 1
	x >>= 1
	x >>= 1
	x >>= 1
	x >>= 1
	x >>= 1
	x >>= 1
	x >>= 1
	x >>= 1
	x >>= 1
	x >>= 1
	x >>= 1
	x >>= 1
	x >>= 1
	x >>= 1
	x >>= 1
	x >>= 1
	return x
}

// CutChain cuts the first byte off a string again and again.
//
// @Requires |s| >= 30
// @Ensures |r| = |s| - 30
func CutChain(s string) (r string) {
	s = s[1:]
	s = s[1:]
	s = s[1:]
	s = s[1:]
	s = s[1:]
	s = s[1:]
	s = s[1:]
	s = s[1:]
	s = s[1:]
	s = s[1:]
	s = s[1:]
	s = s[1:]
	s = s[1:]
	s = s[1:]
	s = s[1:]
	s = s[1:]
	s = s[1:]
	s = s[1:]
	s = s[1:]
	s = s[1:]
	s = s[1:]
	s = s[1:]
	s = s[1:]
	s = s[1:]
	s = s[1:]
	s = s[1:]
	s = s[1:]
	s = s[1:]
	s = s[1:]
	s = s[1:]
	return s
}

// PutChain puts keys into a map one after the other.
//
// @Ensures |r| = 30
func PutChain() (r map[int]int) {
	m := map[int]int{}
	m[0] = 0
	m[1] = 1
	m[2] = 2
	m[3] = 3
	m[4] = 4
	m[5] = 5
	m[6] = 6
	m[7] = 7
	m[8] = 8
	m[9] = 9
	m[10] = 10
	m[11] = 11
	m[12] = 12
	m[13] = 13
	m[14] = 14
	m[15] = 15
	m[16] = 16
	m[17] = 17
	m[18] = 18
	m[19] = 19
	m[20] = 20
	m[21] = 21
	m[22] = 22
	m[23] = 23
	m[24] = 24
	m[25] = 25
	m[26] = 26
	m[27] = 27
	m[28] = 28
	m[29] = 29
	return m
}

// XorChain flips every bit again and again, the way some code writes ^x.
//
// @Ensures r = x
func XorChain(x int) (r int) {
	y := x
	y ^= -1
	y ^= -1
	y ^= -1
	y ^= -1
	y ^= -1
	y ^= -1
	y ^= -1
	y ^= -1
	y ^= -1
	y ^= -1
	y ^= -1
	y ^= -1
	y ^= -1
	y ^= -1
	y ^= -1
	y ^= -1
	y ^= -1
	y ^= -1
	y ^= -1
	y ^= -1
	y ^= -1
	y ^= -1
	y ^= -1
	y ^= -1
	y ^= -1
	y ^= -1
	y ^= -1
	y ^= -1
	y ^= -1
	y ^= -1
	return y
}

// OrChain sets in a number the bits it already has.
//
// @Ensures r = x
func OrChain(x int) (r int) {
	y := x
	y |= y
	y |= y
	y |= y
	y |= y
	y |= y
	y |= y
	y |= y
	y |= y
	y |= y
	y |= y
	y |= y
	y |= y
	y |= y
	y |= y
	y |= y
	y |= y
	y |= y
	y |= y
	y |= y
	y |= y
	y |= y
	y |= y
	y |= y
	y |= y
	y |= y
	y |= y
	y |= y
	y |= y
	y |= y
	y |= y
	return y
}

// ConvChain copies a string to bytes and back again and again.
//
// @Requires |s| <= 10
// @Ensures |r| = |s|
func ConvChain(s string) (r string) {
	t := s
	t = string([]byte(t))
	t = string([]byte(t))
	t = string([]byte(t))
	t = string([]byte(t))
	t = string([]byte(t))
	t = string([]byte(t))
	t = string([]byte(t))
	t = string([]byte(t))
	t = string([]byte(t))
	t = string([]byte(t))
	t = string([]byte(t))
	t = string([]byte(t))
	t = string([]byte(t))
	t = string([]byte(t))
	t = string([]byte(t))
	t = string([]byte(t))
	t = string([]byte(t))
	t = string([]byte(t))
	t = string([]byte(t))
	t = string([]byte(t))
	t = string([]byte(t))
	t = string([]byte(t))
	t = string([]byte(t))
	t = string([]byte(t))
	t = string([]byte(t))
	t = string([]byte(t))
	t = string([]byte(t))
	t = string([]byte(t))
	t = string([]byte(t))
	t = string([]byte(t))
	return t
}

// CopyChain copies elements of a slice into each other again and again: a
// write of a value read from the memory it writes.
//
// @Requires |A| >= 2
// @Modifies A
// @Ensures A'[0] = A[1] And A'[1] = A[1]
func CopyChain(A []int) {
	A[0] = A[1]
	A[1] = A[0]
	A[0] = A[1]
	A[1] = A[0]
	A[0] = A[1]
	A[1] = A[0]
	A[0] = A[1]
	A[1] = A[0]
	A[0] = A[1]
	A[1] = A[0]
	A[0] = A[1]
	A[1] = A[0]
	A[0] = A[1]
	A[1] = A[0]
	A[0] = A[1]
	A[1] = A[0]
	A[0] = A[1]
	A[1] = A[0]
	A[0] = A[1]
	A[1] = A[0]
	A[0] = A[1]
	A[1] = A[0]
	A[0] = A[1]
	A[1] = A[0]
	A[0] = A[1]
	A[1] = A[0]
	A[0] = A[1]
	A[1] = A[0]
	A[0] = A[1]
	A[1] = A[0]
}

// IndexChain writes at an index it reads from the slice it writes.
//
// @Requires |A| >= 1 And 0 <= A[0] < |A|
// @Modifies A
// @Ensures True
func IndexChain(A []int) {
	A[A[0]] = 0
	A[A[0]] = 0
	A[A[0]] = 0
	A[A[0]] = 0
	A[A[0]] = 0
	A[A[0]] = 0
	A[A[0]] = 0
	A[A[0]] = 0
	A[A[0]] = 0
	A[A[0]] = 0
	A[A[0]] = 0
	A[A[0]] = 0
	A[A[0]] = 0
	A[A[0]] = 0
	A[A[0]] = 0
	A[A[0]] = 0
	A[A[0]] = 0
	A[A[0]] = 0
	A[A[0]] = 0
	A[A[0]] = 0
	A[A[0]] = 0
	A[A[0]] = 0
	A[A[0]] = 0
	A[A[0]] = 0
	A[A[0]] = 0
	A[A[0]] = 0
	A[A[0]] = 0
	A[A[0]] = 0
	A[A[0]] = 0
	A[A[0]] = 0
}

// XorSelfChain clears a number by itself again and again.
//
// @Ensures r = 0
func XorSelfChain(x int) (r int) {
	y := x
	y ^= y
	y ^= y
	y ^= y
	y ^= y
	y ^= y
	y ^= y
	y ^= y
	y ^= y
	y ^= y
	y ^= y
	y ^= y
	y ^= y
	y ^= y
	y ^= y
	y ^= y
	y ^= y
	y ^= y
	y ^= y
	y ^= y
	y ^= y
	y ^= y
	y ^= y
	y ^= y
	y ^= y
	y ^= y
	y ^= y
	y ^= y
	y ^= y
	y ^= y
	y ^= y
	return y
}

// Step keeps a number small.
//
// @Requires 0 <= x <= 10
// @Ensures 0 <= y <= 10
type Step func(x int) (y int)

// CallChain calls through a function value again and again.
//
// @Requires f != nil And 0 <= x <= 10
// @Ensures 0 <= r <= 10
func CallChain(f Step, x int) (r int) {
	x = f(x)
	x = f(x)
	x = f(x)
	x = f(x)
	x = f(x)
	x = f(x)
	x = f(x)
	x = f(x)
	x = f(x)
	x = f(x)
	x = f(x)
	x = f(x)
	x = f(x)
	x = f(x)
	x = f(x)
	x = f(x)
	x = f(x)
	x = f(x)
	x = f(x)
	x = f(x)
	x = f(x)
	x = f(x)
	x = f(x)
	x = f(x)
	x = f(x)
	x = f(x)
	x = f(x)
	x = f(x)
	x = f(x)
	x = f(x)
	return x
}

type Store struct{ n int }

// Setter sets the number of a store.
//
// @Requires c != nil
// @Modifies c.n
type Setter func(c *Store)

// MakeChain makes a function literal into a value again and again. Each is
// verified with a renamed copy of what is known where it is made, which
// holds what the ones before it added.
//
// @Requires |fs| = 30
// @Modifies fs
// @Ensures True
func MakeChain(fs []Setter, k int) {
	fs[0] = func(c *Store) { c.n = k }
	fs[1] = func(c *Store) { c.n = k }
	fs[2] = func(c *Store) { c.n = k }
	fs[3] = func(c *Store) { c.n = k }
	fs[4] = func(c *Store) { c.n = k }
	fs[5] = func(c *Store) { c.n = k }
	fs[6] = func(c *Store) { c.n = k }
	fs[7] = func(c *Store) { c.n = k }
	fs[8] = func(c *Store) { c.n = k }
	fs[9] = func(c *Store) { c.n = k }
	fs[10] = func(c *Store) { c.n = k }
	fs[11] = func(c *Store) { c.n = k }
	fs[12] = func(c *Store) { c.n = k }
	fs[13] = func(c *Store) { c.n = k }
	fs[14] = func(c *Store) { c.n = k }
	fs[15] = func(c *Store) { c.n = k }
	fs[16] = func(c *Store) { c.n = k }
	fs[17] = func(c *Store) { c.n = k }
	fs[18] = func(c *Store) { c.n = k }
	fs[19] = func(c *Store) { c.n = k }
	fs[20] = func(c *Store) { c.n = k }
	fs[21] = func(c *Store) { c.n = k }
	fs[22] = func(c *Store) { c.n = k }
	fs[23] = func(c *Store) { c.n = k }
	fs[24] = func(c *Store) { c.n = k }
	fs[25] = func(c *Store) { c.n = k }
	fs[26] = func(c *Store) { c.n = k }
	fs[27] = func(c *Store) { c.n = k }
	fs[28] = func(c *Store) { c.n = k }
	fs[29] = func(c *Store) { c.n = k }
}

// Gate has a state that Shut changes.
//
// @State shut
type Gate interface {
	// @Receiver g
	// @Requires ~shut(g)
	// @Modifies g
	// @Ensures shut(g')
	Shut()
}

func openedGate() (g Gate) { return nil }

// CloseChain shuts thirty interface values, each new, each a write of the
// row of its home in the region of states, which every later read of a
// state goes through.
//
// @Ensures shut(g)
func CloseChain() (g Gate) {
	g = openedGate()
	g.Shut()
	g = openedGate()
	g.Shut()
	g = openedGate()
	g.Shut()
	g = openedGate()
	g.Shut()
	g = openedGate()
	g.Shut()
	g = openedGate()
	g.Shut()
	g = openedGate()
	g.Shut()
	g = openedGate()
	g.Shut()
	g = openedGate()
	g.Shut()
	g = openedGate()
	g.Shut()
	g = openedGate()
	g.Shut()
	g = openedGate()
	g.Shut()
	g = openedGate()
	g.Shut()
	g = openedGate()
	g.Shut()
	g = openedGate()
	g.Shut()
	g = openedGate()
	g.Shut()
	g = openedGate()
	g.Shut()
	g = openedGate()
	g.Shut()
	g = openedGate()
	g.Shut()
	g = openedGate()
	g.Shut()
	g = openedGate()
	g.Shut()
	g = openedGate()
	g.Shut()
	g = openedGate()
	g.Shut()
	g = openedGate()
	g.Shut()
	g = openedGate()
	g.Shut()
	g = openedGate()
	g.Shut()
	g = openedGate()
	g.Shut()
	g = openedGate()
	g.Shut()
	g = openedGate()
	g.Shut()
	g = openedGate()
	g.Shut()
	return g
}

// pick returns its first argument.
//
// @Ensures m = first
func pick(first int, rest ...int) (m int) {
	return first
}

// PackChain passes a value to a variadic function 30 times, twice more in
// its new slice each time, and gets it back.
//
// @Ensures r = a
func PackChain(a int) (r int) {
	m := a
	m = pick(m, m, m)
	m = pick(m, m, m)
	m = pick(m, m, m)
	m = pick(m, m, m)
	m = pick(m, m, m)
	m = pick(m, m, m)
	m = pick(m, m, m)
	m = pick(m, m, m)
	m = pick(m, m, m)
	m = pick(m, m, m)
	m = pick(m, m, m)
	m = pick(m, m, m)
	m = pick(m, m, m)
	m = pick(m, m, m)
	m = pick(m, m, m)
	m = pick(m, m, m)
	m = pick(m, m, m)
	m = pick(m, m, m)
	m = pick(m, m, m)
	m = pick(m, m, m)
	m = pick(m, m, m)
	m = pick(m, m, m)
	m = pick(m, m, m)
	m = pick(m, m, m)
	m = pick(m, m, m)
	m = pick(m, m, m)
	m = pick(m, m, m)
	m = pick(m, m, m)
	m = pick(m, m, m)
	m = pick(m, m, m)
	return m
}

// SpreadChain adds the elements of t 30 times to a slice with room for all
// of them, each time copying them as append(s, t...) does.
//
// @Requires |t| = 1
// @Ensures |r| = 30 And r[29] = t[0]
func SpreadChain(t []int) (r []int) {
	s := make([]int, 0, 30)
	s = append(s, t...)
	s = append(s, t...)
	s = append(s, t...)
	s = append(s, t...)
	s = append(s, t...)
	s = append(s, t...)
	s = append(s, t...)
	s = append(s, t...)
	s = append(s, t...)
	s = append(s, t...)
	s = append(s, t...)
	s = append(s, t...)
	s = append(s, t...)
	s = append(s, t...)
	s = append(s, t...)
	s = append(s, t...)
	s = append(s, t...)
	s = append(s, t...)
	s = append(s, t...)
	s = append(s, t...)
	s = append(s, t...)
	s = append(s, t...)
	s = append(s, t...)
	s = append(s, t...)
	s = append(s, t...)
	s = append(s, t...)
	s = append(s, t...)
	s = append(s, t...)
	s = append(s, t...)
	s = append(s, t...)
	return s
}

// TextChain adds the bytes of a string 30 times.
//
// @Ensures |r| = 60 And r[59] = 98
func TextChain() (r []byte) {
	b := make([]byte, 0, 60)
	b = append(b, "ab"...)
	b = append(b, "ab"...)
	b = append(b, "ab"...)
	b = append(b, "ab"...)
	b = append(b, "ab"...)
	b = append(b, "ab"...)
	b = append(b, "ab"...)
	b = append(b, "ab"...)
	b = append(b, "ab"...)
	b = append(b, "ab"...)
	b = append(b, "ab"...)
	b = append(b, "ab"...)
	b = append(b, "ab"...)
	b = append(b, "ab"...)
	b = append(b, "ab"...)
	b = append(b, "ab"...)
	b = append(b, "ab"...)
	b = append(b, "ab"...)
	b = append(b, "ab"...)
	b = append(b, "ab"...)
	b = append(b, "ab"...)
	b = append(b, "ab"...)
	b = append(b, "ab"...)
	b = append(b, "ab"...)
	b = append(b, "ab"...)
	b = append(b, "ab"...)
	b = append(b, "ab"...)
	b = append(b, "ab"...)
	b = append(b, "ab"...)
	b = append(b, "ab"...)
	return b
}

// RuneChain encodes a rune again and again, each time the rune of the
// length of the last encoding.
//
// @Requires 0 <= r < 1114112
// @Ensures 1 <= |s| <= 4
func RuneChain(r rune) (s string) {
	s = string(r)
	s = string(rune(len(s) + 127))
	s = string(rune(len(s) + 127))
	s = string(rune(len(s) + 127))
	s = string(rune(len(s) + 127))
	s = string(rune(len(s) + 127))
	s = string(rune(len(s) + 127))
	s = string(rune(len(s) + 127))
	s = string(rune(len(s) + 127))
	s = string(rune(len(s) + 127))
	s = string(rune(len(s) + 127))
	s = string(rune(len(s) + 127))
	s = string(rune(len(s) + 127))
	s = string(rune(len(s) + 127))
	s = string(rune(len(s) + 127))
	s = string(rune(len(s) + 127))
	s = string(rune(len(s) + 127))
	s = string(rune(len(s) + 127))
	s = string(rune(len(s) + 127))
	s = string(rune(len(s) + 127))
	s = string(rune(len(s) + 127))
	s = string(rune(len(s) + 127))
	s = string(rune(len(s) + 127))
	s = string(rune(len(s) + 127))
	s = string(rune(len(s) + 127))
	s = string(rune(len(s) + 127))
	s = string(rune(len(s) + 127))
	s = string(rune(len(s) + 127))
	s = string(rune(len(s) + 127))
	s = string(rune(len(s) + 127))
	return s
}

// RangeChain counts the keys of a map thirty times over, one range after
// another, each with the keys it has visited named.
//
// @Requires |m| <= 1000
// @Ensures n = 30 * |m|
func RangeChain(m map[int]int) (n int) {
	// @Visited d0
	// @Invariant n = 0 * |m| + |d0|
	for range m {
		n++
	}
	// @Visited d1
	// @Invariant n = 1 * |m| + |d1|
	for range m {
		n++
	}
	// @Visited d2
	// @Invariant n = 2 * |m| + |d2|
	for range m {
		n++
	}
	// @Visited d3
	// @Invariant n = 3 * |m| + |d3|
	for range m {
		n++
	}
	// @Visited d4
	// @Invariant n = 4 * |m| + |d4|
	for range m {
		n++
	}
	// @Visited d5
	// @Invariant n = 5 * |m| + |d5|
	for range m {
		n++
	}
	// @Visited d6
	// @Invariant n = 6 * |m| + |d6|
	for range m {
		n++
	}
	// @Visited d7
	// @Invariant n = 7 * |m| + |d7|
	for range m {
		n++
	}
	// @Visited d8
	// @Invariant n = 8 * |m| + |d8|
	for range m {
		n++
	}
	// @Visited d9
	// @Invariant n = 9 * |m| + |d9|
	for range m {
		n++
	}
	// @Visited d10
	// @Invariant n = 10 * |m| + |d10|
	for range m {
		n++
	}
	// @Visited d11
	// @Invariant n = 11 * |m| + |d11|
	for range m {
		n++
	}
	// @Visited d12
	// @Invariant n = 12 * |m| + |d12|
	for range m {
		n++
	}
	// @Visited d13
	// @Invariant n = 13 * |m| + |d13|
	for range m {
		n++
	}
	// @Visited d14
	// @Invariant n = 14 * |m| + |d14|
	for range m {
		n++
	}
	// @Visited d15
	// @Invariant n = 15 * |m| + |d15|
	for range m {
		n++
	}
	// @Visited d16
	// @Invariant n = 16 * |m| + |d16|
	for range m {
		n++
	}
	// @Visited d17
	// @Invariant n = 17 * |m| + |d17|
	for range m {
		n++
	}
	// @Visited d18
	// @Invariant n = 18 * |m| + |d18|
	for range m {
		n++
	}
	// @Visited d19
	// @Invariant n = 19 * |m| + |d19|
	for range m {
		n++
	}
	// @Visited d20
	// @Invariant n = 20 * |m| + |d20|
	for range m {
		n++
	}
	// @Visited d21
	// @Invariant n = 21 * |m| + |d21|
	for range m {
		n++
	}
	// @Visited d22
	// @Invariant n = 22 * |m| + |d22|
	for range m {
		n++
	}
	// @Visited d23
	// @Invariant n = 23 * |m| + |d23|
	for range m {
		n++
	}
	// @Visited d24
	// @Invariant n = 24 * |m| + |d24|
	for range m {
		n++
	}
	// @Visited d25
	// @Invariant n = 25 * |m| + |d25|
	for range m {
		n++
	}
	// @Visited d26
	// @Invariant n = 26 * |m| + |d26|
	for range m {
		n++
	}
	// @Visited d27
	// @Invariant n = 27 * |m| + |d27|
	for range m {
		n++
	}
	// @Visited d28
	// @Invariant n = 28 * |m| + |d28|
	for range m {
		n++
	}
	// @Visited d29
	// @Invariant n = 29 * |m| + |d29|
	for range m {
		n++
	}
	return n
}

// setKey sets one key of a map.
//
// @Requires m != nil
// @Modifies m[k]
// @Ensures has(m', k) And m'[k] = 1
func setKey(m map[int]int, k int) {
	m[k] = 1
}

// EntryChain sets thirty keys through a callee that lists one entry each
// time, so each call forgets one entry and keeps the count exact.
//
// @Ensures |r| = 30
func EntryChain() (r map[int]int) {
	m := map[int]int{}
	setKey(m, 0)
	setKey(m, 1)
	setKey(m, 2)
	setKey(m, 3)
	setKey(m, 4)
	setKey(m, 5)
	setKey(m, 6)
	setKey(m, 7)
	setKey(m, 8)
	setKey(m, 9)
	setKey(m, 10)
	setKey(m, 11)
	setKey(m, 12)
	setKey(m, 13)
	setKey(m, 14)
	setKey(m, 15)
	setKey(m, 16)
	setKey(m, 17)
	setKey(m, 18)
	setKey(m, 19)
	setKey(m, 20)
	setKey(m, 21)
	setKey(m, 22)
	setKey(m, 23)
	setKey(m, 24)
	setKey(m, 25)
	setKey(m, 26)
	setKey(m, 27)
	setKey(m, 28)
	setKey(m, 29)
	return m
}

// Writer writes behind its receiver.
type Writer interface {
	// @Receiver w
	// @Modifies w
	// @Ensures True
	Put(p []byte)
}

// WriteChain writes through s thirty times, each a call that may write
// every region at the cells of s's footprint, and keeps q, which every read
// of it after the last call finds through the thirty epochs.
//
// @Requires s != nil And q != nil
// @Modifies s
// @Ensures q.A' = q.A
func WriteChain(s Writer, q *Pair) {
	s.Put(nil)
	s.Put(nil)
	s.Put(nil)
	s.Put(nil)
	s.Put(nil)
	s.Put(nil)
	s.Put(nil)
	s.Put(nil)
	s.Put(nil)
	s.Put(nil)
	s.Put(nil)
	s.Put(nil)
	s.Put(nil)
	s.Put(nil)
	s.Put(nil)
	s.Put(nil)
	s.Put(nil)
	s.Put(nil)
	s.Put(nil)
	s.Put(nil)
	s.Put(nil)
	s.Put(nil)
	s.Put(nil)
	s.Put(nil)
	s.Put(nil)
	s.Put(nil)
	s.Put(nil)
	s.Put(nil)
	s.Put(nil)
	s.Put(nil)
}

// Pair is two numbers.
type Pair struct{ A, B int }

// SpliceChain writes thirty bytes to a Writer it is handed, each a call
// that writes the array the Writer owns as a splice of the row before it,
// and reads a byte of its own after the last, through the thirty splices.
//
// @Requires bw != nil And ready(bw)
// @Modifies bw
// @Ensures r = 7
func SpliceChain(bw *bufio.Writer) (r byte) {
	p := make([]byte, 1)
	p[0] = 7
	_ = bw.WriteByte(0)
	_ = bw.WriteByte(1)
	_ = bw.WriteByte(2)
	_ = bw.WriteByte(3)
	_ = bw.WriteByte(4)
	_ = bw.WriteByte(5)
	_ = bw.WriteByte(6)
	_ = bw.WriteByte(7)
	_ = bw.WriteByte(8)
	_ = bw.WriteByte(9)
	_ = bw.WriteByte(10)
	_ = bw.WriteByte(11)
	_ = bw.WriteByte(12)
	_ = bw.WriteByte(13)
	_ = bw.WriteByte(14)
	_ = bw.WriteByte(15)
	_ = bw.WriteByte(16)
	_ = bw.WriteByte(17)
	_ = bw.WriteByte(18)
	_ = bw.WriteByte(19)
	_ = bw.WriteByte(20)
	_ = bw.WriteByte(21)
	_ = bw.WriteByte(22)
	_ = bw.WriteByte(23)
	_ = bw.WriteByte(24)
	_ = bw.WriteByte(25)
	_ = bw.WriteByte(26)
	_ = bw.WriteByte(27)
	_ = bw.WriteByte(28)
	_ = bw.WriteByte(29)
	return p[0]
}

// BufferLengthChain writes a Buffer fifteen times and reads its length
// after each write. The length of an owner is a formula over its fields,
// here |buf| - off, read from one fetch of its struct, so the pointer
// enters each read once, and the length is an integer, which no later
// length reads. Fifteen writes, not thirty as elsewhere in this file: a
// rule that doubled the term at each write would have grown it 2^15 times
// here, far past the growth check, and each write costs more than the one
// before it.
//
// @Requires b != nil And |b| = 0
// @Modifies b
// @Ensures n = 15
func BufferLengthChain(b *bytes.Buffer) (n int) {
	b.WriteByte('x')
	// @Assert |b| = 1
	b.WriteByte('x')
	// @Assert |b| = 2
	b.WriteByte('x')
	// @Assert |b| = 3
	b.WriteByte('x')
	// @Assert |b| = 4
	b.WriteByte('x')
	// @Assert |b| = 5
	b.WriteByte('x')
	// @Assert |b| = 6
	b.WriteByte('x')
	// @Assert |b| = 7
	b.WriteByte('x')
	// @Assert |b| = 8
	b.WriteByte('x')
	// @Assert |b| = 9
	b.WriteByte('x')
	// @Assert |b| = 10
	b.WriteByte('x')
	// @Assert |b| = 11
	b.WriteByte('x')
	// @Assert |b| = 12
	b.WriteByte('x')
	// @Assert |b| = 13
	b.WriteByte('x')
	// @Assert |b| = 14
	b.WriteByte('x')
	// @Assert |b| = 15
	return b.Len()
}

// Hop is an error held through a pointer.
type Hop struct{ n int }

// @Ensures True
func (h *Hop) Error() (s string) { return "hop" }

// HopChain converts thirty pointers read from a slice to error, and
// compares each error with the one before: a conversion reads the
// allocation of its pointer twice, for the position of a nil pointer
// (goLeaves), and names it first. In this step no conversion is handed
// what another made, so the chain where a conversion's result is read
// again comes with type assertions.
//
// @Requires |ps| >= 30
// @Ensures True
func HopChain(ps []*Hop) (same bool) {
	var e, last error
	same = true
	e = ps[0]
	same = same && e != last
	last = e
	e = ps[1]
	same = same && e != last
	last = e
	e = ps[2]
	same = same && e != last
	last = e
	e = ps[3]
	same = same && e != last
	last = e
	e = ps[4]
	same = same && e != last
	last = e
	e = ps[5]
	same = same && e != last
	last = e
	e = ps[6]
	same = same && e != last
	last = e
	e = ps[7]
	same = same && e != last
	last = e
	e = ps[8]
	same = same && e != last
	last = e
	e = ps[9]
	same = same && e != last
	last = e
	e = ps[10]
	same = same && e != last
	last = e
	e = ps[11]
	same = same && e != last
	last = e
	e = ps[12]
	same = same && e != last
	last = e
	e = ps[13]
	same = same && e != last
	last = e
	e = ps[14]
	same = same && e != last
	last = e
	e = ps[15]
	same = same && e != last
	last = e
	e = ps[16]
	same = same && e != last
	last = e
	e = ps[17]
	same = same && e != last
	last = e
	e = ps[18]
	same = same && e != last
	last = e
	e = ps[19]
	same = same && e != last
	last = e
	e = ps[20]
	same = same && e != last
	last = e
	e = ps[21]
	same = same && e != last
	last = e
	e = ps[22]
	same = same && e != last
	last = e
	e = ps[23]
	same = same && e != last
	last = e
	e = ps[24]
	same = same && e != last
	last = e
	e = ps[25]
	same = same && e != last
	last = e
	e = ps[26]
	same = same && e != last
	last = e
	e = ps[27]
	same = same && e != last
	last = e
	e = ps[28]
	same = same && e != last
	last = e
	e = ps[29]
	same = same && e != last
	last = e
	return same
}

// Link is an error that holds a pointer.
type Link struct{ next *Link }

// @Ensures True
func (l *Link) Error() (s string) { return "link" }

// LinkChain converts a pointer to error and takes it out again thirty
// times, each conversion handed what the last assertion gave: the
// allocation a conversion reads twice, for the position of a nil pointer
// (goLeaves), is named first, so the terms do not double.
//
// @Ensures True
func LinkChain(p *Link) (q *Link) {
	var e error
	q = p
	e = q
	q = e.(*Link)
	e = q
	q = e.(*Link)
	e = q
	q = e.(*Link)
	e = q
	q = e.(*Link)
	e = q
	q = e.(*Link)
	e = q
	q = e.(*Link)
	e = q
	q = e.(*Link)
	e = q
	q = e.(*Link)
	e = q
	q = e.(*Link)
	e = q
	q = e.(*Link)
	e = q
	q = e.(*Link)
	e = q
	q = e.(*Link)
	e = q
	q = e.(*Link)
	e = q
	q = e.(*Link)
	e = q
	q = e.(*Link)
	e = q
	q = e.(*Link)
	e = q
	q = e.(*Link)
	e = q
	q = e.(*Link)
	e = q
	q = e.(*Link)
	e = q
	q = e.(*Link)
	e = q
	q = e.(*Link)
	e = q
	q = e.(*Link)
	e = q
	q = e.(*Link)
	e = q
	q = e.(*Link)
	e = q
	q = e.(*Link)
	e = q
	q = e.(*Link)
	e = q
	q = e.(*Link)
	e = q
	q = e.(*Link)
	e = q
	q = e.(*Link)
	e = q
	q = e.(*Link)
	return q
}

// AnyChain converts a pointer to any and takes it out again thirty times,
// each conversion handed what the last assertion gave (S1 of F34): the
// reference an assertion reads twice is named first, as the allocation a
// conversion reads twice is, so the terms do not double.
//
// @Ensures True
func AnyChain(p *Link) (q *Link) {
	var a any
	q = p
	a = q
	q = a.(*Link)
	a = q
	q = a.(*Link)
	a = q
	q = a.(*Link)
	a = q
	q = a.(*Link)
	a = q
	q = a.(*Link)
	a = q
	q = a.(*Link)
	a = q
	q = a.(*Link)
	a = q
	q = a.(*Link)
	a = q
	q = a.(*Link)
	a = q
	q = a.(*Link)
	a = q
	q = a.(*Link)
	a = q
	q = a.(*Link)
	a = q
	q = a.(*Link)
	a = q
	q = a.(*Link)
	a = q
	q = a.(*Link)
	a = q
	q = a.(*Link)
	a = q
	q = a.(*Link)
	a = q
	q = a.(*Link)
	a = q
	q = a.(*Link)
	a = q
	q = a.(*Link)
	a = q
	q = a.(*Link)
	a = q
	q = a.(*Link)
	a = q
	q = a.(*Link)
	a = q
	q = a.(*Link)
	a = q
	q = a.(*Link)
	a = q
	q = a.(*Link)
	a = q
	q = a.(*Link)
	a = q
	q = a.(*Link)
	a = q
	q = a.(*Link)
	a = q
	q = a.(*Link)
	return q
}

// SwitchChain does the same through a type switch, whose cases read the
// reference each; the other case returns, so the paths do not double.
//
// @Ensures True
func SwitchChain(p *Link) (q *Link) {
	var a any
	q = p
	a = q
	switch x := a.(type) {
	case *Link:
		q = x
	default:
		return nil
	}
	a = q
	switch x := a.(type) {
	case *Link:
		q = x
	default:
		return nil
	}
	a = q
	switch x := a.(type) {
	case *Link:
		q = x
	default:
		return nil
	}
	a = q
	switch x := a.(type) {
	case *Link:
		q = x
	default:
		return nil
	}
	a = q
	switch x := a.(type) {
	case *Link:
		q = x
	default:
		return nil
	}
	a = q
	switch x := a.(type) {
	case *Link:
		q = x
	default:
		return nil
	}
	a = q
	switch x := a.(type) {
	case *Link:
		q = x
	default:
		return nil
	}
	a = q
	switch x := a.(type) {
	case *Link:
		q = x
	default:
		return nil
	}
	a = q
	switch x := a.(type) {
	case *Link:
		q = x
	default:
		return nil
	}
	a = q
	switch x := a.(type) {
	case *Link:
		q = x
	default:
		return nil
	}
	a = q
	switch x := a.(type) {
	case *Link:
		q = x
	default:
		return nil
	}
	a = q
	switch x := a.(type) {
	case *Link:
		q = x
	default:
		return nil
	}
	a = q
	switch x := a.(type) {
	case *Link:
		q = x
	default:
		return nil
	}
	a = q
	switch x := a.(type) {
	case *Link:
		q = x
	default:
		return nil
	}
	a = q
	switch x := a.(type) {
	case *Link:
		q = x
	default:
		return nil
	}
	a = q
	switch x := a.(type) {
	case *Link:
		q = x
	default:
		return nil
	}
	a = q
	switch x := a.(type) {
	case *Link:
		q = x
	default:
		return nil
	}
	a = q
	switch x := a.(type) {
	case *Link:
		q = x
	default:
		return nil
	}
	a = q
	switch x := a.(type) {
	case *Link:
		q = x
	default:
		return nil
	}
	a = q
	switch x := a.(type) {
	case *Link:
		q = x
	default:
		return nil
	}
	a = q
	switch x := a.(type) {
	case *Link:
		q = x
	default:
		return nil
	}
	a = q
	switch x := a.(type) {
	case *Link:
		q = x
	default:
		return nil
	}
	a = q
	switch x := a.(type) {
	case *Link:
		q = x
	default:
		return nil
	}
	a = q
	switch x := a.(type) {
	case *Link:
		q = x
	default:
		return nil
	}
	a = q
	switch x := a.(type) {
	case *Link:
		q = x
	default:
		return nil
	}
	a = q
	switch x := a.(type) {
	case *Link:
		q = x
	default:
		return nil
	}
	a = q
	switch x := a.(type) {
	case *Link:
		q = x
	default:
		return nil
	}
	a = q
	switch x := a.(type) {
	case *Link:
		q = x
	default:
		return nil
	}
	a = q
	switch x := a.(type) {
	case *Link:
		q = x
	default:
		return nil
	}
	a = q
	switch x := a.(type) {
	case *Link:
		q = x
	default:
		return nil
	}
	return q
}

// EqChain compares interface values twenty times, each comparison of the
// result of an assertion of the last one's operand (S3 of F34): the
// references == reads several times are named first, so the terms do not
// double.
//
// @Requires holds(v, int)
// @Ensures True
func EqChain(v any) (r bool) {
	a := v
	r = a == 1
	a = any(a.(int))
	r = a == 1
	a = any(a.(int))
	r = a == 1
	a = any(a.(int))
	r = a == 1
	a = any(a.(int))
	r = a == 1
	a = any(a.(int))
	r = a == 1
	a = any(a.(int))
	r = a == 1
	a = any(a.(int))
	r = a == 1
	a = any(a.(int))
	r = a == 1
	a = any(a.(int))
	r = a == 1
	a = any(a.(int))
	r = a == 1
	a = any(a.(int))
	r = a == 1
	a = any(a.(int))
	r = a == 1
	a = any(a.(int))
	r = a == 1
	a = any(a.(int))
	r = a == 1
	a = any(a.(int))
	r = a == 1
	a = any(a.(int))
	r = a == 1
	a = any(a.(int))
	r = a == 1
	a = any(a.(int))
	r = a == 1
	a = any(a.(int))
	r = a == 1
	a = any(a.(int))
	return r
}

// ArrayChain writes each element of an array value from the one before it.
//
// @Ensures r = 30
func ArrayChain() (r int) {
	var a [31]int
	a[1] = a[0] + 1
	a[2] = a[1] + 1
	a[3] = a[2] + 1
	a[4] = a[3] + 1
	a[5] = a[4] + 1
	a[6] = a[5] + 1
	a[7] = a[6] + 1
	a[8] = a[7] + 1
	a[9] = a[8] + 1
	a[10] = a[9] + 1
	a[11] = a[10] + 1
	a[12] = a[11] + 1
	a[13] = a[12] + 1
	a[14] = a[13] + 1
	a[15] = a[14] + 1
	a[16] = a[15] + 1
	a[17] = a[16] + 1
	a[18] = a[17] + 1
	a[19] = a[18] + 1
	a[20] = a[19] + 1
	a[21] = a[20] + 1
	a[22] = a[21] + 1
	a[23] = a[22] + 1
	a[24] = a[23] + 1
	a[25] = a[24] + 1
	a[26] = a[25] + 1
	a[27] = a[26] + 1
	a[28] = a[27] + 1
	a[29] = a[28] + 1
	a[30] = a[29] + 1
	return a[30]
}

// @Ensures r = |p|
func peekInts(p []int) (r int) { return len(p) }

// ArrayBoxedChain is ArrayChain with the array in memory.
//
// @Ensures r = 30
func ArrayBoxedChain() (r int) {
	var a [31]int
	_ = peekInts(a[:])
	a[1] = a[0] + 1
	a[2] = a[1] + 1
	a[3] = a[2] + 1
	a[4] = a[3] + 1
	a[5] = a[4] + 1
	a[6] = a[5] + 1
	a[7] = a[6] + 1
	a[8] = a[7] + 1
	a[9] = a[8] + 1
	a[10] = a[9] + 1
	a[11] = a[10] + 1
	a[12] = a[11] + 1
	a[13] = a[12] + 1
	a[14] = a[13] + 1
	a[15] = a[14] + 1
	a[16] = a[15] + 1
	a[17] = a[16] + 1
	a[18] = a[17] + 1
	a[19] = a[18] + 1
	a[20] = a[19] + 1
	a[21] = a[20] + 1
	a[22] = a[21] + 1
	a[23] = a[22] + 1
	a[24] = a[23] + 1
	a[25] = a[24] + 1
	a[26] = a[25] + 1
	a[27] = a[26] + 1
	a[28] = a[27] + 1
	a[29] = a[28] + 1
	a[30] = a[29] + 1
	return a[30]
}

// ArrayCopyChain copies two arrays in memory into each other, each copy
// a cut of one row spliced into another.
//
// @Ensures r = 1
func ArrayCopyChain() (r int) {
	var a, b [8]int
	_, _ = peekInts(a[:]), peekInts(b[:])
	a[0] = 1
	b = a
	a = b
	b = a
	a = b
	b = a
	a = b
	b = a
	a = b
	b = a
	a = b
	b = a
	a = b
	b = a
	a = b
	b = a
	a = b
	b = a
	a = b
	b = a
	a = b
	b = a
	a = b
	b = a
	a = b
	b = a
	a = b
	b = a
	a = b
	b = a
	a = b
	return a[0]
}
