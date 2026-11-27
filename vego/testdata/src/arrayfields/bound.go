package arrayfields

// Big holds an array of eight-byte numbers at its end, past 2^46 bytes: a
// slice of it has the offset 2^46 + lo, and F36's bound off·8 + cap·8 <=
// 2^48 is false of it, while the slice is real (F21 of the review of the
// design of step 3a; on 386 the same is true of an array of int32 past
// 1100 << 20 bytes, TestSliceBoundEdges).
type Big struct {
	Pad [1 << 46]byte
	C   [4]int64
}

// G assumes, of a slice that lies within b.C, the bound every slice
// carries, and must not prove False from it.
//
// @Requires b != nil And |xs| > 0 And within(xs, b.C)
// @Ensures False
func G(xs []int64, b *Big) {
} // want `vego: postcondition may not hold: False`
