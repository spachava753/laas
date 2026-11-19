package integers

// When x & y is one of its operands, the verifier writes x | y, x ^ y, and
// x &^ y with that operand cancelled. Each function below reaches one such
// case and states its exact result. An operand of -1 has every bit, so
// x & -1 is x; an operand made from the other with |, &, or &^ makes the and
// one of them too.

// @Ensures r = -1
func OrAllRight(v int) (r int) { return v | -1 }

// @Ensures r = -1
func OrAllLeft(v int) (r int) { return -1 | v }

// @Ensures r = -1 - v
func XorAllRight(v int) (r int) { return v ^ -1 }

// @Ensures r = -1 - v
func XorAllLeft(v int) (r int) { return -1 ^ v }

// @Ensures r = 0
func AndNotAllRight(v int) (r int) { return v &^ -1 }

// @Ensures r = -1 - v
func AndNotAllLeft(v int) (r int) { return -1 &^ v }

// @Ensures r = v
func OrSelf(v int) (r int) { return v | v }

// @Ensures r = 0
func XorSelf(v int) (r int) { return v ^ v }

// @Ensures r = 0
func AndNotSelf(v int) (r int) { return v &^ v }

// OrAgain sets the bits of m in a number that has them already.
//
// @Ensures result
func OrAgain(a, m int) (result bool) {
	t := a | m
	return t|m == t
}

// XorAfterOr clears the bits of m in a number that has them.
//
// @Ensures result
func XorAfterOr(a, m int) (result bool) {
	t := a | m
	return t^m == a&^m
}

// OrAfterAnd sets the bits of m in a number that has only bits of m.
//
// @Ensures result
func OrAfterAnd(a, m int) (result bool) {
	t := a & m
	return t|m == m
}

// XorAfterAnd flips the bits of m in a number that has only bits of m.
//
// @Ensures result
func XorAfterAnd(a, m int) (result bool) {
	t := a & m
	return t^m == m&^a
}

// AndNotAfterAnd clears the bits of m in a number that has only bits of m.
//
// @Ensures result
func AndNotAfterAnd(a, m int) (result bool) {
	t := a & m
	return t&^m == 0
}

// WrongOrLeft claims that -1 | v is v.
//
// @Ensures r = v
func WrongOrLeft(v int) (r int) {
	return -1 | v // want `vego: postcondition may not hold: r = v`
}

// WrongXorRight claims that v ^ -1 is v - (-1).
//
// @Ensures r = v + 1
func WrongXorRight(v int) (r int) {
	return v ^ -1 // want `vego: postcondition may not hold: r = v \+ 1`
}

// WrongAndNotLeft claims that -1 &^ v is zero.
//
// @Ensures r = 0
func WrongAndNotLeft(v int) (r int) {
	return -1 &^ v // want `vego: postcondition may not hold: r = 0`
}

// WrongOrSelf claims that v | v is zero.
//
// @Ensures r = 0
func WrongOrSelf(v int) (r int) {
	return v | v // want `vego: postcondition may not hold: r = 0`
}
