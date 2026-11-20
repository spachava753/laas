// Package costs is verified with -vego.cost and a small resource limit, so
// that some questions stop at the limit.
package costs

// Add adds two small numbers.
//
// @Requires 0 <= a <= 100 And 0 <= b <= 100
// @Ensures r = a + b
func Add(a, b int) (r int) {
	return a + b
}

// Product multiplies four numbers.
//
// @Requires 0 <= a <= 1000 And 0 <= b <= 1000 And 0 <= c <= 1000 And 0 <= d <= 1000
// @Ensures r >= 0
func Product(a, b, c, d int) (r int) {
	s := a * b
	t := s * c // want `multiplication may overflow int \(Z3 reached its resource limit`
	return t * d // want `multiplication may overflow int \(Z3 reached its resource limit`
}

// P holds a number.
type P struct{ x int }

// Set writes through a pointer.
//
// @Requires p != nil
// @Modifies p.x
// @Ensures p.x' = 1
func Set(p *P) {
	p.x = 1
}

// read is trusted; see the trust file of the tests.
func read(s string) (n int, err error) { return len(s), nil }

// Read returns what read returns.
//
// @Ensures True
func Read(s string) (n int, err error) {
	return read(s)
}
