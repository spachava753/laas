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
