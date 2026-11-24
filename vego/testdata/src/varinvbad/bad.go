// Package varinvbad declares invariants that cannot be relied on.
package varinvbad

// @Invariant 0 <= Count // want `^vego: the invariant of Count cannot be relied on: Count is exported, and code of another package may assign it; an invariant holds only of variables that only the package changes$`
var Count int

// @Invariant 0 <= n // want `^vego: the invariant of n cannot be relied on: n is changed at bad.go:\d+ in bump, which is not verified; every change of a variable with an invariant must be made by a function of the package that is verified, which restores it, so call one$`
var n int

func bump() { n-- }

// @Invariant |table| > 0 // want `^vego: the invariant of table cannot be relied on: the use of table at bad.go:\d+ lets a reference to what it refers to out of it, so a write through another reference could break the invariant without naming the variable$`
var table = []int{1}

// Table hands the slice out.
//
// @Ensures True
func Table() (r []int) { return table }

// @Invariant 0 <= m // want `^vego: the invariant of m cannot be relied on: m is changed at bad.go:\d+ in an init function that is not verified; give it a contract, as // @Modifies m; every change`
var m int

func init() { m = 1 }

// @Invariant lo = 0 Or lo < hi // want `^vego: the invariant of lo cannot be relied on: it names hi, which is not a variable of its group and which the build changes; declare hi in the same var declaration$`
var lo int

var hi = 10

// setLo sets lo below hi.
//
// @Modifies lo
// @Ensures True
func setLo() {
	if hi > 5 {
		lo = 5
	}
}

// setHi changes hi, which is not of lo's group.
//
// @Modifies hi
// @Ensures True
func setHi() { hi = 1 }
