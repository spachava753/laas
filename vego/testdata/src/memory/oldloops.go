//go:build go1.21

package memory

// This file is compiled as Go 1.21, where all iterations of a loop share
// its variables.

// OldLoopVariable keeps a pointer to the variable of a for loop, which the
// post statement then advances.
//
// @ Ensures result = 2
func OldLoopVariable() (result int) {
	var p *Point
	// @ Invariant 0 <= x.X <= 2
	// @ Invariant x.X > 0 -> (p != nil And p.X = x.X)
	// @ Variant 2 - x.X
	for x := (Point{}); x.X < 2; x.X++ {
		p = &x
	}
	return p.X
}

// OldLoopVariableWrong claims the behaviour of newer Go.
//
// @ Ensures result = 1
func OldLoopVariableWrong() (result int) {
	var p *Point
	// @ Invariant 0 <= x.X <= 2
	// @ Invariant x.X > 0 -> (p != nil And p.X = x.X - 1)
	// @ Variant 2 - x.X
	for x := (Point{}); x.X < 2; x.X++ { // want `vego: loop invariant may not be preserved: x\.X > 0 -> \(p != nil And p\.X = x\.X - 1\)`
		p = &x
	}
	return p.X
}

// OldRangeVariable takes the address of the variable of a range loop.
//
// @ Requires |ps| > 0
// @ Ensures True
func OldRangeVariable(ps []Point) (result int) {
	total := 0
	for _, p := range ps { // want `vego: cannot verify OldRangeVariable: before Go 1.22 the iterations of a range loop share their variables, which is not supported when the address of one is taken`
		q := &p
		total = q.X
	}
	return total
}
