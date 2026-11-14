// Package integers checks that arithmetic on every integer type is proved
// not to overflow, since Go would wrap silently.
package integers

// Increment adds one where that is known to fit.
//
// @ Requires x < MaxInt
func Increment(x int) (y int) {
	return x + 1
}

//@ Ensures y = x + 1

// IncrementUnbounded can wrap around to the least int.
func IncrementUnbounded(x int) (y int) {
	return x + 1 // want `vego:\ addition\ may\ overflow\ int`
}

//@ Ensures y = x + 1

// Saturating clamps instead of overflowing.
func Saturating(x uint8) (y uint8) {
	if x == 255 {
		return x
	}
	return x + 1
}

//@ Ensures y >= x And (y = x Or y = x + 1)

// WrapsByte wraps from 255 to 0.
func WrapsByte(x uint8) (y uint8) {
	x++ // want `vego:\ addition\ may\ overflow\ uint8`
	return x
}

//@ Ensures y > 0

// Underflow wraps below zero: unsigned subtraction needs a <= b proved.
func Underflow(a, b uint) (d uint) {
	return b - a // want `vego:\ subtraction\ may\ overflow\ uint`
}

//@ Ensures d + a = b

// Difference subtracts the smaller from the larger.
func Difference(a, b uint) (d uint) {
	if a > b {
		return a - b
	}
	return b - a
}

//@ Ensures d + a = b Or d + b = a

// Negate has no result for the least value.
func Negate(x int32) int32 {
	//@ Assert MinInt32 <= x <= MaxInt32
	return -x // want `vego:\ negation\ may\ overflow\ int32`
}

// Quotient overflows only for the least value divided by -1.
//
// @ Requires b != 0
func Quotient(a, b int64) int64 {
	//@ Assert True
	return a / b // want `vego:\ division\ may\ overflow\ int64`
}

// SafeQuotient rules that case out.
//
// @ Requires b > 0
func SafeQuotient(a, b int64) (q int64) {
	return a / b
}

//@ Ensures MinInt64 <= q <= MaxInt64

// Narrow converts only what fits.
func Narrow(x int) (y int8, ok bool) {
	if x < -128 || x > 127 {
		return 0, false
	}
	return int8(x), true
}

//@ Ensures ok = True -> y = x

// Truncates loses the high bits.
func Truncates(x int) (y uint8) {
	return uint8(x) // want `vego:\ conversion\ may\ not\ fit\ uint8`
}

//@ Ensures y = x

// SignToUnsigned cannot represent a negative number.
func SignToUnsigned(x int) (y uint) {
	return uint(x) // want `vego:\ conversion\ may\ not\ fit\ uint`
}

//@ Ensures y = x

// Widen always fits.
func Widen(x uint8, y int32) (z int64) {
	return int64(x) + int64(y)
}

//@ Ensures z = x + y

// Flatten computes a row-major index. Proving that it is in range multiplies
// the bounds on row and col.
//
// @ Requires 0 <= row < rows And 0 <= col < cols
// @ Requires |grid| = rows * cols And rows <= 10000 And cols <= 10000
func Flatten(grid []int, rows, cols, row, col int) int {
	return grid[row*cols+col]
}

// Area multiplies two bounded sides.
//
// @ Requires 0 <= w <= 30000 And 0 <= h <= 30000
func Area(w, h int32) (a int32) {
	return w * h
}

//@ Ensures 0 <= a <= 900000000

// AreaTooLarge exceeds the range of int32.
//
// @ Requires 0 <= w <= 50000 And 0 <= h <= 50000
func AreaTooLarge(w, h int32) (a int32) {
	return w * h // want `vego:\ multiplication\ may\ overflow\ int32`
}

//@ Ensures a >= 0

// SumBytes adds bytes into an int, which cannot overflow for any slice that
// fits in memory on a 64-bit platform, given a bound on the length.
//
// @ Requires |data| <= 1000000
func SumBytes(data []byte) (sum int) {
	//@ Invariant 0 <= sum <= 255 * i
	for i := range data {
		sum += int(data[i])
	}
	return sum
}

//@ Ensures 0 <= sum <= 255 * |data|

// Midpoint is the overflow-free form of (lo+hi)/2.
//
// @ Requires 0 <= lo <= hi
func Midpoint(lo, hi int) (mid int) {
	return lo + (hi-lo)/2
}

//@ Ensures lo <= mid <= hi

// MidpointOverflows is the classic binary search bug.
//
// @ Requires 0 <= lo <= hi
func MidpointOverflows(lo, hi int) (mid int) {
	return (lo + hi) / 2 // want `vego:\ addition\ may\ overflow\ int`
}

//@ Ensures lo <= mid <= hi

//@ Predicate fib(n, f) ::= (n <= 1 -> f = n) And
//@   (n > 1 -> Exists a in Z : Exists b in Z : (fib(n-1, a) And fib(n-2, b) And f = a + b))

// Fib overflows for n above 92, and nothing here bounds n.
//
// @ Requires n >= 0
func Fib(n int) (f int) {
	if n == 0 {
		return 0
	}
	previous, current := 0, 1
	//@ Invariant 1 <= i <= n And fib(i-1, previous) And fib(i, current)
	//@ Variant n - i
	for i := 1; i < n; i++ {
		previous, current = current, previous+current // want `vego:\ addition\ may\ overflow\ int`
	}
	return current
}

//@ Ensures fib(n, f)

// Allocate needs a length that fits an int.
func Allocate(n uint64) []int {
	//@ Assert n >= 0
	return make([]int, n) // want `vego:\ make\ length\ may\ overflow\ int` `vego: the slice made may be more than can be allocated`
}

// Limits uses the named limits in annotations.
func Limits(x int16) (y int32) {
	return int32(x) * 2
}

//@ Ensures 2*MinInt16 <= y <= 2*MaxInt16
//@ Ensures MinInt32 < y And y < MaxInt32

// Countdown decrements an unsigned counter without passing zero.
func Countdown(n uint) (steps uint) {
	//@ Invariant steps + n = old(n)
	//@ Variant n
	for n > 0 {
		n--
		steps++
	}
	return steps
}

//@ Ensures steps = n

// CountdownOffByOne decrements once too often.
func CountdownOffByOne(n uint) {
	//@ Invariant n >= 0
	//@ Variant n + 1
	for n >= 0 {
		n-- // want `vego:\ subtraction\ may\ overflow\ uint`
	}
}

// TooMuchCapacity asks for a capacity that does not fit an int.
//
// @ Requires n > MaxInt
func TooMuchCapacity(n uint64) int {
	s := make([]byte, 0, n) // want `vego:\ make\ capacity\ may\ overflow\ int`
	return len(s)
}

//@ Ensures result = 0

// Oversize makes a slice longer than any allocation can be.
//
// @ Requires n = MaxInt
func Oversize(n int) []byte {
	s := make([]byte, n) // want `vego: the slice made may be more than can be allocated`
	s = append(s, 0)
	return s
}

//@ Ensures False

// Huge asks for more memory than the runtime hands out in one piece, with a
// length that fits an int.
func Huge() []uint64 {
	return make([]uint64, 2305843009213693952) // want `vego: the slice made may be more than can be allocated`
}

//@ Ensures |result| = 2305843009213693952

// GrowsUnbounded appends to a slice that may already be as large as an
// allocation can be.
func GrowsUnbounded(s []byte) []byte {
	return append(s, 0) // want `vego: append may write into the capacity of s, which GrowsUnbounded may not modify` `vego: the slice that append grows may be more than can be allocated`
}

//@ Ensures |result| = |s| + 1
