//go:build go1.21

// Package funcvaluesoldloop is compiled as Go 1.21, where the iterations of a
// loop share their variables, so a literal made in one sees the variable as
// later iterations leave it.
package funcvaluesoldloop

// @Requires 0 <= x <= 1000
// @Ensures 0 <= y <= 2000
type Mapper func(x int) (y int)

// Loop makes a literal in each iteration that returns the loop variable.
//
// @Requires |out| = |xs| And Forall j in [0, |xs|) : 0 <= xs[j] <= 1000
// @Modifies out
// @Ensures True
func Loop(xs []int, out []Mapper) {
	for i, x := range xs {
		out[i] = func(y int) int {
			return x // want `vego: postcondition may not hold: 0 <= y <= 2000`
		}
	}
}
