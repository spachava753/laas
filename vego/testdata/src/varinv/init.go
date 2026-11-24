package varinv

// @Invariant step > 0
var step = 1

// init sets the step; with a contract it is verified as any writer, and
// restores the invariant on return.
//
// @Modifies step
// @Ensures True
func init() {
	step = 2
}

// @Invariant 0 <= depth
var depth int

// init breaks it.
//
// @Modifies depth
// @Ensures True
func init() {
	depth = -1
} // want `^vego: invariant of depth may not hold on return: 0 <= depth; it was not kept from entry, since depth may have changed: the assignment to depth at init.go:23:2 may write it$`

// Steps relies on step.
//
// @Ensures True
func Steps(x int) (r int) {
	return x / step
}
