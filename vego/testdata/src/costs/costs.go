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

// Cube multiplies a number by itself three times.
//
// @Requires 0 <= a <= 1000 And 0 <= b <= 1000 And 0 <= c <= 1000
// @Ensures r >= 0
func Cube(a, b, c int) (r int) {
	s := a * b
	return s * c // want `multiplication may overflow int \(Z3 reached its resource limit`
}
