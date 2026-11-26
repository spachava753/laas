package arraystructs

// The ways of making elements of a slice of structs that hold a byte
// array, each read in a contract (a fault of F36 found in F37: a slice
// literal zeroed the region of the array's elements with whole arrays).

// Cell holds a byte array after a number.
type Cell struct {
	n   int
	buf [4]byte
}

// MakeLiteral makes a slice of one zero Cell with a literal.
//
// @Ensures |r| = 1 And r[0].buf[0] = 0 And r[0].buf[3] = 0
func MakeLiteral() (r []Cell) {
	return []Cell{{}}
}

// MakeMake makes a slice of zero Cells with make.
//
// @Requires 0 < n <= 10
// @Ensures |r| = n And r[n-1].buf[3] = 0
func MakeMake(n int) (r []Cell) {
	return make([]Cell, n)
}

// MakeAppend appends a Cell to a slice.
//
// @Requires |xs| < 100
// @Modifies xs
// @Ensures |r| = |xs| + 1 And r[|xs|].buf[2] = 5
func MakeAppend(xs []Cell) (r []Cell) {
	return append(xs, Cell{buf: [4]byte{0, 0, 5, 0}})
}

// Holder holds a Cell.
type Holder struct {
	c Cell
}

// MakeHolder makes a Holder whose Cell's array holds 9 last.
//
// @Ensures r != nil And r.c.buf[3] = 9 And r.c.buf[0] = 0
func MakeHolder() (r *Holder) {
	return &Holder{c: Cell{buf: [4]byte{0, 0, 0, 9}}}
}

// Assign assigns an element of a slice of Cells.
//
// @Requires |xs| > 0
// @Modifies xs
// @Ensures xs'[0].buf[3] = 4 And xs'[0].buf[0] = 0
func Assign(xs []Cell) {
	xs[0] = Cell{buf: [4]byte{0, 0, 0, 4}}
}

// MakeLiteralWrong claims what the literal does not hold.
//
// @Ensures r[0].buf[3] = 1
func MakeLiteralWrong() (r []Cell) {
	return []Cell{{}} // want `vego: postcondition may not hold: r\[0\]\.buf\[3\] = 1`
}

// MakeMakeWrong claims a byte that make leaves zero.
//
// @Requires 0 < n <= 10
// @Ensures r[0].buf[0] = 1
func MakeMakeWrong(n int) (r []Cell) {
	return make([]Cell, n) // want `vego: postcondition may not hold: r\[0\]\.buf\[0\] = 1`
}

// MakeAppendWrong claims a byte of the appended Cell that it does not hold.
//
// @Requires |xs| < 100
// @Modifies xs
// @Ensures r[|xs|].buf[2] = 6
func MakeAppendWrong(xs []Cell) (r []Cell) {
	return append(xs, Cell{buf: [4]byte{0, 0, 5, 0}}) // want `vego: postcondition may not hold: r\[\|xs\|\]\.buf\[2\] = 6`
}

// MakeHolderWrong claims the first byte of the held array.
//
// @Ensures r.c.buf[0] = 9
func MakeHolderWrong() (r *Holder) {
	return &Holder{c: Cell{buf: [4]byte{0, 0, 0, 9}}} // want `vego: postcondition may not hold: r\.c\.buf\[0\] = 9`
}

// AssignWrong claims a byte of the assigned element that it does not hold.
//
// @Requires |xs| > 0
// @Modifies xs
// @Ensures xs'[0].buf[2] = 4
func AssignWrong(xs []Cell) {
	xs[0] = Cell{buf: [4]byte{0, 0, 0, 4}}
} // want `vego: postcondition may not hold: xs'\[0\]\.buf\[2\] = 4`
