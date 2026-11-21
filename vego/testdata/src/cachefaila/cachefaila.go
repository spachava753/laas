// Package cachefaila is the first package of TestCacheErrorFailsTheRun.
// Its problems hold the number 987654321, which no problem of cachefailb
// holds.
package cachefaila

// @Ensures r <-> x < 987654321
func Below(x int) (r bool) {
	return x < 987654321
}

// @Requires x < 987654321
// @Ensures r = x + 1
func Step(x int) (r int) {
	return x + 1
}
