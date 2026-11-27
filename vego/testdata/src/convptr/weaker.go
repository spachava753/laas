package convptr

// Unnamed converts to an unnamed interface type, which has no contract.
//
// @Ensures True
func Unnamed() (r int) {
	var a A = T{}
	p := (*interface{ M() (r int) })(&a) // want `vego: cannot verify Unnamed: converting \&a from \*A to \*interface\{M\(\) \(r int\)`
	return (*p).M()
}

// T2 returns 2.
type T2 struct{}

// M returns 2.
//
// @Ensures r = 2
func (T2) M() (r int) {
	return 2
}

// Weaker converts a B, whose contract promises 2, to an A, whose contract
// promises 1: also false, since A's Ensures r = 1 is not B's r = 2.
//
// @Ensures r = 1
func Weaker() (r int) {
	var b B = T2{}
	pa := (*A)(&b) // want `vego: cannot verify Weaker: converting \&b from \*B to \*A is not supported: th`
	return (*pa).M()
}
