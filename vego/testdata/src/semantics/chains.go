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
