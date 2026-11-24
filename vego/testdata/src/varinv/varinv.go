// Package varinv holds invariants of package-level variables (part 2 of
// package-level variables): assumed where a function touches them, proved
// where one may have changed them and before every call that may assume
// them.
package varinv

import "io"

// @Invariant 0 <= size And size = |cache|
var (
	cache = map[string]int{}
	size  int
)

// put adds a key and counts it.
//
// @Requires size < 1000000
// @Modifies cache, size
// @Ensures True
func put(k string) {
	if _, ok := cache[k]; ok {
		return
	}
	cache[k] = 1
	size++
}

// forget adds a key and does not count it.
//
// @Modifies cache
// @Ensures True
func forget(k string) {
	if _, ok := cache[k]; !ok {
		cache[k] = 1
	}
} // want `^vego: invariant of cache, size may not hold on return: 0 <= size And size = \|cache\|$`

// Size is not negative, by the invariant.
//
// @Ensures n >= 0
func Size() (n int) {
	return size
}

// putThenAsk asks Size while the invariant is broken.
//
// @Requires size < 1000000
// @Modifies cache, size
// @Ensures True
func putThenAsk(k string) {
	if _, ok := cache[k]; ok {
		return
	}
	cache[k] = 1
	_ = Size() // want `^vego: invariant of cache, size may not hold before the call to Size, which may assume it: 0 <= size And size = \|cache\|$`
	size++
}

// askThenPut asks while it holds.
//
// @Requires size < 1000000
// @Modifies cache, size
// @Ensures True
func askThenPut(k string) {
	_ = Size()
	put(k)
}

// @Invariant 0 <= hits
var hits int

// hit counts.
//
// @Modifies hits
// @Ensures True
func hit() {
	if hits < 1000 {
		hits++
	}
}

// reset breaks it.
//
// @Modifies hits
// @Ensures True
func reset() {
	hits = -1
} // want `^vego: invariant of hits may not hold on return: 0 <= hits$`

// Hits is not negative, by the invariant.
//
// @Ensures r >= 0
func Hits() (r int) { return hits }

type logger struct{}

// Write reads hits, and is not verified.
func (logger) Write(p []byte) (int, error) { return len(p) + Hits(), nil }

// writeBroken writes through w while hits is broken; w may be a logger,
// which reads hits through Hits.
//
// @Requires w != nil
// @Modifies hits, w
// @Ensures True
func writeBroken(w io.Writer) {
	hits = -1
	w.Write([]byte("x")) // want `^vego: invariant of hits may not hold before the call to w.Write, which may assume it: 0 <= hits$`
	hits = 0
}

// @Invariant ready // want `^vego: invariant of ready may not hold when the package is initialised: ready; it must follow from what the declarations give the variables$`
var ready bool

// @Invariant limit > 0
var limit = 10

// setLimit keeps it.
//
// @Requires n > 0
// @Modifies limit
// @Ensures limit' = n
func setLimit(n int) { limit = n }

// Divide relies on it.
//
// @Ensures True
func Divide(x int) (r int) {
	if x < 0 {
		return 0
	}
	return x / limit
}
