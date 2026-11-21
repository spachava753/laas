package semantics

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
