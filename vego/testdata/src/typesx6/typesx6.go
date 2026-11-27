// Package typesx6 writes one exported field of each of 6 struct types
// through a pointer of its own. The fields lie in one region, since a
// pointer to an int may point to any of them, and the read of each through
// its pointer skips the writes through the others, whose types are apart
// (R6 of F42). It is in the table of costs, as manywrites is.
package typesx6

// T0 holds a number.
type T0 struct {
	X  int
	Z0 int
}

// T1 holds a number.
type T1 struct {
	X  int
	Z1 int
}

// T2 holds a number.
type T2 struct {
	X  int
	Z2 int
}

// T3 holds a number.
type T3 struct {
	X  int
	Z3 int
}

// T4 holds a number.
type T4 struct {
	X  int
	Z4 int
}

// T5 holds a number.
type T5 struct {
	X  int
	Z5 int
}

// Set sets the X of 6 structs of 6 types.
//
// @Requires p0 != nil And p1 != nil And p2 != nil And p3 != nil And p4 != nil And p5 != nil
// @Modifies p0.X, p1.X, p2.X, p3.X, p4.X, p5.X
// @Ensures p0.X' = 0 And p1.X' = 1 And p2.X' = 2 And p3.X' = 3 And p4.X' = 4 And p5.X' = 5
func Set(p0 *T0, p1 *T1, p2 *T2, p3 *T3, p4 *T4, p5 *T5) {
	p0.X = 0
	p1.X = 1
	p2.X = 2
	p3.X = 3
	p4.X = 4
	p5.X = 5
}
