package footprints

import "io"

// The reviewer's program of F33 of the review of F38: a struct converted
// to an interface whose methods write behind their receiver, and then a
// read of an element under a quantifier in a formula that no gatherer
// collects. The read put a fact with the quantifier's bound variable on the
// path, and the solver refused it as out of scope, in the default mode at
// the base; now nothing is stated of such a position.

type crashCounter struct {
	N int
}

// @Requires c != nil
// @Modifies c
// @Ensures n = |p| And err = nil
func (c *crashCounter) Write(p []byte) (n int, err error) {
	c.N = 1
	return len(p), nil
}

// @Requires w != nil
// @Modifies w
// @Ensures True
func crashEmit(w io.Writer) {
	_, _ = w.Write([]byte("x"))
}

// @Requires Forall i in [0, |l|) : |l[i]| <= 100
// @Ensures True
func crashShort(l []string) {
}

// @Ensures True
func ReadAfterWriter(l []string) {
	c := &crashCounter{}
	crashEmit(c)
	crashShort(l) // want `vego: precondition of crashShort may not hold: Forall i in \[0, \|l\|\) : \|l\[i\]\| <= 100`
}
