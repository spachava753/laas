// Package typesx20 writes one exported field of each of 20 struct types
// through a pointer of its own. The fields lie in one region, since a
// pointer to an int may point to any of them, and the read of each through
// its pointer skips the writes through the others, whose types are apart
// (R6 of F42). It is in the table of costs, as manywrites is.
package typesx20

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

// T6 holds a number.
type T6 struct {
	X  int
	Z6 int
}

// T7 holds a number.
type T7 struct {
	X  int
	Z7 int
}

// T8 holds a number.
type T8 struct {
	X  int
	Z8 int
}

// T9 holds a number.
type T9 struct {
	X  int
	Z9 int
}

// T10 holds a number.
type T10 struct {
	X   int
	Z10 int
}

// T11 holds a number.
type T11 struct {
	X   int
	Z11 int
}

// T12 holds a number.
type T12 struct {
	X   int
	Z12 int
}

// T13 holds a number.
type T13 struct {
	X   int
	Z13 int
}

// T14 holds a number.
type T14 struct {
	X   int
	Z14 int
}

// T15 holds a number.
type T15 struct {
	X   int
	Z15 int
}

// T16 holds a number.
type T16 struct {
	X   int
	Z16 int
}

// T17 holds a number.
type T17 struct {
	X   int
	Z17 int
}

// T18 holds a number.
type T18 struct {
	X   int
	Z18 int
}

// T19 holds a number.
type T19 struct {
	X   int
	Z19 int
}

// Set sets the X of 20 structs of 20 types.
//
// @Requires p0 != nil And p1 != nil And p2 != nil And p3 != nil And p4 != nil And p5 != nil And p6 != nil And p7 != nil And p8 != nil And p9 != nil And p10 != nil And p11 != nil And p12 != nil And p13 != nil And p14 != nil And p15 != nil And p16 != nil And p17 != nil And p18 != nil And p19 != nil
// @Modifies p0.X, p1.X, p2.X, p3.X, p4.X, p5.X, p6.X, p7.X, p8.X, p9.X, p10.X, p11.X, p12.X, p13.X, p14.X, p15.X, p16.X, p17.X, p18.X, p19.X
// @Ensures p0.X' = 0 And p1.X' = 1 And p2.X' = 2 And p3.X' = 3 And p4.X' = 4 And p5.X' = 5 And p6.X' = 6 And p7.X' = 7 And p8.X' = 8 And p9.X' = 9 And p10.X' = 10 And p11.X' = 11 And p12.X' = 12 And p13.X' = 13 And p14.X' = 14 And p15.X' = 15 And p16.X' = 16 And p17.X' = 17 And p18.X' = 18 And p19.X' = 19
func Set(p0 *T0, p1 *T1, p2 *T2, p3 *T3, p4 *T4, p5 *T5, p6 *T6, p7 *T7, p8 *T8, p9 *T9, p10 *T10, p11 *T11, p12 *T12, p13 *T13, p14 *T14, p15 *T15, p16 *T16, p17 *T17, p18 *T18, p19 *T19) {
	p0.X = 0
	p1.X = 1
	p2.X = 2
	p3.X = 3
	p4.X = 4
	p5.X = 5
	p6.X = 6
	p7.X = 7
	p8.X = 8
	p9.X = 9
	p10.X = 10
	p11.X = 11
	p12.X = 12
	p13.X = 13
	p14.X = 14
	p15.X = 15
	p16.X = 16
	p17.X = 17
	p18.X = 18
	p19.X = 19
}
