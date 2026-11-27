package arrayptrs

// LenInFormula names the length of a nil pointer to an array, which Go
// gives as 4 and the slice it is held as as 0: formulas do not name what a
// pointer to an array points to.
//
// @Ensures True
func LenInFormula() {
	var p *[4]int
	// @Assert |p| = 0 // want `in Assert annotation: p is not a slice, a string, a map, a strings.Builder, or a bytes.Buffer, and has no length`
	_ = p
}

// ElemInFormula names an element through a pointer to an array.
//
// @Requires b != nil
// @Modifies b.Word
// @Ensures True
func ElemInFormula(b *Block) {
	p := &b.Word
	p[1] = 3
	// @Assert p[1] = 3 // want `in Assert annotation: p: a \*\[4\]uint32 cannot be indexed`
}

// Aliases writes through one view of an array and reads through another.
//
// @Requires b != nil
// @Modifies b.Word
// @Ensures r = 4
func Aliases(b *Block) (r uint32) {
	p := &b.Word
	q := (*[4]uint32)(b.Word[:])
	q[2] = 4
	return p[2]
}

// LocalStruct takes the address of an array field of a local struct.
//
// @Ensures r = 2
func LocalStruct() (r uint32) {
	var x Block
	p := &x.Word
	p[0] = 2
	return x.Word[0]
}

// Moves assigns the pointer in the loop and writes through it: the loop
// forgets where it points, as it forgets a slice it assigns, and no
// formula can say, so the write is refused.
//
// @Requires b != nil And c != nil And b != c And 0 <= n < 10
// @Modifies b.Word, c.Word
// @Ensures b.N' = b.N
func Moves(b, c *Block, n int) {
	p := &b.Word
	// @Invariant True
	for range n {
		p[0] = 1 // want `vego: pointer may be nil` `p\[0\] is assigned, which Moves may not modify`
		p = &c.Word
	}
}
