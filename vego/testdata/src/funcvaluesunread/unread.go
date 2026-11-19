// Package funcvaluesunread has an annotation that is not read, so none of
// its contracts is handed to other packages.
package funcvaluesunread

// Op does something.
//
// @Ensures True
type Op func(x int) (y int)

// @Ensure True // want `vego: unknown annotation "Ensure"`
func helper() {}
