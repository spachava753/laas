package integers

// Half halves by shifting.
//
// @ Requires 0 <= x
func Half(x int) int {
	return x >> 1
}

//@ Ensures result = x / 2

// HalfWrong claims a shift to the right rounds a negative number towards
// zero, as division does.
func HalfWrong(x int) int {
	return x >> 1 // want `vego: postcondition may not hold: result = x / 2`
}

//@ Ensures result = x / 2

// HalfDown says what it does: it rounds towards minus infinity.
func HalfDown(x int) int {
	return x >> 1
}

//@ Ensures 2*result <= x < 2*result + 2

// Times8 multiplies by shifting, which must not lose bits.
//
// @ Requires 0 <= x <= 1000
func Times8(x int) int {
	return x << 3
}

//@ Ensures result = 8 * x

// Times8Unbounded shifts a number that may be too large.
func Times8Unbounded(x int) int {
	return x << 3 // want `vego: shift may overflow int`
}

//@ Ensures result = 8 * x

// Bit returns the number with only bit k set.
//
// @ Requires 0 <= k < 16
func Bit(k int) int {
	return 1 << k
}

//@ Ensures 1 <= result <= 32768

// BitTooFar shifts by a count that may push the bit out.
//
// @ Requires 0 <= k
func BitTooFar(k int) int {
	return 1 << k // want `vego: shift may overflow int`
}

//@ Ensures result >= 1

// NegativeCount shifts by a count that may be negative, which panics.
func NegativeCount(x uint8, k int) uint8 {
	return x >> k // want `vego: shift count may be negative`
}

//@ Ensures result <= x

// ShiftedDown shifts by a count that is not a constant.
//
// @ Requires 0 <= k
func ShiftedDown(x uint32, k int) uint32 {
	return x >> k
}

//@ Ensures result <= x

// LowByte masks the low eight bits.
func LowByte(x uint32) uint32 {
	return x & 0xFF
}

//@ Ensures result = x % 256

// LowByteWrong claims the mask keeps nine bits.
func LowByteWrong(x uint32) uint32 {
	return x & 0xFF // want `vego: postcondition may not hold: result = x % 512`
}

//@ Ensures result = x % 512

// IsOdd tests the lowest bit.
func IsOdd(x uint) bool {
	return x&1 == 1
}

//@ Ensures result <-> x % 2 = 1

// Pack puts two bytes into sixteen bits.
func Pack(hi, lo byte) uint16 {
	return uint16(hi)<<8 | uint16(lo)
}

//@ Ensures result = 256 * hi + lo

// PackWrong claims the bytes end up the other way round.
func PackWrong(hi, lo byte) uint16 {
	return uint16(hi)<<8 | uint16(lo) // want `vego: postcondition may not hold: result = 256 \* lo \+ hi`
}

//@ Ensures result = 256 * lo + hi

// Pack4 puts four bytes into thirty-two bits.
func Pack4(a, b, c, d byte) uint32 {
	return uint32(a)<<24 | uint32(b)<<16 | uint32(c)<<8 | uint32(d)
}

//@ Ensures result = 16777216 * a + 65536 * b + 256 * c + d

// Unpack takes the two bytes out again.
func Unpack(x uint16) (hi, lo byte) {
	return byte(x >> 8), byte(x & 0xFF)
}

//@ Ensures 256 * hi + lo = x

// Bounded combines two numbers; whatever comes out is no larger than both
// together and no smaller than either.
func Bounded(x, y uint8) uint8 {
	return x | y
}

//@ Ensures x <= result And y <= result And result <= x + y

// Toggle flips bits; nothing is known beyond the bounds.
func Toggle(x, y uint8) uint8 {
	return x ^ y
}

//@ Ensures result <= x + y

// ToggleWrong claims to know the result.
func ToggleWrong(x, y uint8) uint8 {
	return x ^ y // want `vego: postcondition may not hold: result = x \+ y`
}

//@ Ensures result = x + y

// Clear removes the low bit.
func Clear(x uint8) uint8 {
	return x &^ 1
}

//@ Ensures result = x - x % 2

// Inverse flips every bit of an unsigned number and of a signed one.
func Inverse(x uint8, y int8) (a uint8, b int8) {
	return ^x, ^y
}

//@ Ensures a = 255 - x And b = -y - 1

// Accumulate uses the assignment forms.
//
// @ Requires 0 <= x <= 100
func Accumulate(x int) int {
	x <<= 2
	x |= 3
	x &= 0xFF
	x >>= 1
	return x
}

//@ Ensures 0 <= result <= 127

// CountBits counts the bits of a byte with a loop.
func CountBits(x uint8) int {
	n := 0
	//@ Invariant 0 <= i <= 8 And 0 <= n <= i
	//@ Variant 8 - i
	for i := 0; i < 8; i++ {
		if x>>i&1 == 1 {
			n++
		}
	}
	return n
}

//@ Ensures 0 <= result <= 8

// NarrowThenWide shifts a narrow number and then a wide one by the same
// count, which is more than the narrow one has bits.
//
// @ Requires k = 16
func NarrowThenWide(k uint) uint64 {
	_ = uint8(1) >> k
	return uint64(65536) >> k
}

//@ Ensures result = 1

// SmallOr combines two numbers of four bits, which gives one of four bits.
//
// @ Requires x <= 15 And y <= 15
func SmallOr(x, y uint8) uint8 {
	return x | y
}

//@ Ensures result <= 15

// SmallXor does the same with the other operator.
//
// @ Requires x <= 15 And y <= 15
func SmallXor(x, y uint8) uint8 {
	return x ^ y
}

//@ Ensures result <= 15

// SmallOrWrong claims three bits.
//
// @ Requires x <= 15 And y <= 15
func SmallOrWrong(x, y uint8) uint8 {
	return x | y // want `vego: postcondition may not hold: result <= 7`
}

//@ Ensures result <= 7

const flagB = 2

// SetsFlag sets a bit and then tests it.
func SetsFlag(f uint8) bool {
	f |= flagB
	return f&flagB != 0
}

//@ Ensures result

// ClearsFlag clears a bit and then tests it.
func ClearsFlag(f uint8) bool {
	f &^= flagB
	return f&flagB == 0
}

//@ Ensures result

// SetsOtherFlag sets one bit and tests another, of which nothing is known.
func SetsOtherFlag(f uint8) bool {
	f |= flagB
	return f&4 != 0 // want `vego: postcondition may not hold: result`
}

//@ Ensures result

// BuildsMask sets one bit after another and stays within four bits.
func BuildsMask() uint8 {
	var m uint8
	//@ Invariant 0 <= k <= 4 And m <= 15
	//@ Variant 4 - k
	for k := 0; k < 4; k++ {
		m |= 1 << k
	}
	return m
}

//@ Ensures result <= 15
