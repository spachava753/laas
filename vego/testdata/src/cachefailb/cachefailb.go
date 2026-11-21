// Package cachefailb is the second package of TestCacheErrorFailsTheRun,
// which verifies it after cachefaila has met an error of the cache. None
// of its problems holds the number of cachefaila.
package cachefailb

// @Requires 0 <= x < 1000
// @Ensures r = 2 * x
func Double(x int) (r int) {
	return x + x
}

// @Ensures r <-> x > 7
func Above(x int) (r bool) {
	return x > 7
}
