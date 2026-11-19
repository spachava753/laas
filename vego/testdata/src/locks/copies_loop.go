//go:build go1.22

package locks

// The variable of a three-clause loop is a new one in each iteration from
// Go 1.22 on, which Go copies from the last one; the build constraint gives
// this file that version.

// @Ensures True
func CopyLoopVariable() {
	for a := (Account{}); a.balance < 1; a.balance++ { // want `cannot verify CopyLoopVariable: the loop variable a has type Account, which holds a sync.Mutex, and Go copies it into each iteration; declare it before the loop`
		take2(&a, &a)
	}
}

