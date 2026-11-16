package integers

// Half halves by shifting.
//
// @Requires 0 <= x
// @Ensures result = x / 2
func Half(x int) (result int) {
	return x >> 1
}

// HalfWrong claims a shift to the right rounds a negative number towards
// zero, as division does.
//
// @Ensures result = x / 2
func HalfWrong(x int) (result int) {
	return x >> 1 // want `vego: postcondition may not hold: result = x / 2`
}

// HalfDown says what it does: it rounds towards minus infinity.
//
// @Ensures 2*result <= x < 2*result + 2
func HalfDown(x int) (result int) {
	return x >> 1
}

// Times8 multiplies by shifting, which must not lose bits.
//
// @Requires 0 <= x <= 1000
// @Ensures result = 8 * x
func Times8(x int) (result int) {
	return x << 3
}

// Times8Unbounded shifts a number that may be too large.
//
// @Ensures result = 8 * x
func Times8Unbounded(x int) (result int) {
	return x << 3 // want `vego: shift may overflow int`
}

// Bit returns the number with only bit k set.
//
// @Requires 0 <= k < 16
// @Ensures 1 <= result <= 32768
func Bit(k int) (result int) {
	return 1 << k
}

// BitTooFar shifts by a count that may push the bit out.
//
// @Requires 0 <= k
// @Ensures result >= 1
func BitTooFar(k int) (result int) {
	return 1 << k // want `vego: shift may overflow int`
}

// NegativeCount shifts by a count that may be negative, which panics.
//
// @Ensures result <= x
func NegativeCount(x uint8, k int) (result uint8) {
	return x >> k // want `vego: shift count may be negative`
}

// ShiftedDown shifts by a count that is not a constant.
//
// @Requires 0 <= k
// @Ensures result <= x
func ShiftedDown(x uint32, k int) (result uint32) {
	return x >> k
}

// LowByte masks the low eight bits.
//
// @Ensures result = x % 256
func LowByte(x uint32) (result uint32) {
	return x & 0xFF
}

// LowByteWrong claims the mask keeps nine bits.
//
// @Ensures result = x % 512
func LowByteWrong(x uint32) (result uint32) {
	return x & 0xFF // want `vego: postcondition may not hold: result = x % 512`
}

// IsOdd tests the lowest bit.
//
// @Ensures result <-> x % 2 = 1
func IsOdd(x uint) (result bool) {
	return x&1 == 1
}

// Pack puts two bytes into sixteen bits.
//
// @Ensures result = 256 * hi + lo
func Pack(hi, lo byte) (result uint16) {
	return uint16(hi)<<8 | uint16(lo)
}

// PackWrong claims the bytes end up the other way round.
//
// @Ensures result = 256 * lo + hi
func PackWrong(hi, lo byte) (result uint16) {
	return uint16(hi)<<8 | uint16(lo) // want `vego: postcondition may not hold: result = 256 \* lo \+ hi`
}

// Pack4 puts four bytes into thirty-two bits.
//
// @Ensures result = 16777216 * a + 65536 * b + 256 * c + d
func Pack4(a, b, c, d byte) (result uint32) {
	return uint32(a)<<24 | uint32(b)<<16 | uint32(c)<<8 | uint32(d)
}

// Unpack takes the two bytes out again.
//
// @Ensures 256 * hi + lo = x
func Unpack(x uint16) (hi, lo byte) {
	return byte(x >> 8), byte(x & 0xFF)
}

// Bounded combines two numbers; whatever comes out is no larger than both
// together and no smaller than either.
//
// @Ensures x <= result And y <= result And result <= x + y
func Bounded(x, y uint8) (result uint8) {
	return x | y
}

// Toggle flips bits; nothing is known beyond the bounds.
//
// @Ensures result <= x + y
func Toggle(x, y uint8) (result uint8) {
	return x ^ y
}

// ToggleWrong claims to know the result.
//
// @Ensures result = x + y
func ToggleWrong(x, y uint8) (result uint8) {
	return x ^ y // want `vego: postcondition may not hold: result = x \+ y`
}

// Clear removes the low bit.
//
// @Ensures result = x - x % 2
func Clear(x uint8) (result uint8) {
	return x &^ 1
}

// Inverse flips every bit of an unsigned number and of a signed one.
//
// @Ensures a = 255 - x And b = -y - 1
func Inverse(x uint8, y int8) (a uint8, b int8) {
	return ^x, ^y
}

// Accumulate uses the assignment forms.
//
// @Requires 0 <= x <= 100
// @Ensures 0 <= result <= 127
func Accumulate(x int) (result int) {
	x <<= 2
	x |= 3
	x &= 0xFF
	x >>= 1
	return x
}

// CountBits counts the bits of a byte with a loop.
//
// @Ensures 0 <= result <= 8
func CountBits(x uint8) (result int) {
	n := 0
	// @Invariant 0 <= i <= 8 And 0 <= n <= i
	// @Variant 8 - i
	for i := 0; i < 8; i++ {
		if x>>i&1 == 1 {
			n++
		}
	}
	return n
}

// NarrowThenWide shifts a narrow number and then a wide one by the same
// count, which is more than the narrow one has bits.
//
// @Requires k = 16
// @Ensures result = 1
func NarrowThenWide(k uint) (result uint64) {
	_ = uint8(1) >> k
	return uint64(65536) >> k
}

// SmallOr combines two numbers of four bits, which gives one of four bits.
//
// @Requires x <= 15 And y <= 15
// @Ensures result <= 15
func SmallOr(x, y uint8) (result uint8) {
	return x | y
}

// SmallXor does the same with the other operator.
//
// @Requires x <= 15 And y <= 15
// @Ensures result <= 15
func SmallXor(x, y uint8) (result uint8) {
	return x ^ y
}

// SmallOrWrong claims three bits.
//
// @Requires x <= 15 And y <= 15
// @Ensures result <= 7
func SmallOrWrong(x, y uint8) (result uint8) {
	return x | y // want `vego: postcondition may not hold: result <= 7`
}

const flagB = 2

// SetsFlag sets a bit and then tests it.
//
// @Ensures result
func SetsFlag(f uint8) (result bool) {
	f |= flagB
	return f&flagB != 0
}

// ClearsFlag clears a bit and then tests it.
//
// @Ensures result
func ClearsFlag(f uint8) (result bool) {
	f &^= flagB
	return f&flagB == 0
}

// SetsOtherFlag sets one bit and tests another, of which nothing is known.
//
// @Ensures result
func SetsOtherFlag(f uint8) (result bool) {
	f |= flagB
	return f&4 != 0 // want `vego: postcondition may not hold: result`
}

// BuildsMask sets one bit after another and stays within four bits.
//
// @Ensures result <= 15
func BuildsMask() (result uint8) {
	var m uint8
	// @Invariant 0 <= k <= 4 And m <= 15
	// @Variant 4 - k
	for k := 0; k < 4; k++ {
		m |= 1 << k
	}
	return m
}

// NarrowThenWideOr combines two numbers as bytes, in an expression that is
// skipped, and then as they are.
//
// @Requires x <= 511 And y <= 511
// @Ensures result <= 511
func NarrowThenWideOr(x, y uint16) (result uint16) {
	_ = false && (uint8(x)&uint8(y) == 0)
	return x | y
}

// BitOfNegative reads one bit of a negative number, which has the bits
// that -x - 1 lacks.
//
// @Requires x = -1
// @Ensures result = 8
func BitOfNegative(x int) (result int) {
	return x & 8
}

// BitOfNegativeClear expects a bit that -9 does not have.
//
// @Requires x = -9
// @Ensures result = 8
func BitOfNegativeClear(x int) (result int) {
	return x & 8 // want `vego: postcondition may not hold: result = 8`
}
