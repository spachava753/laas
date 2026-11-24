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
} // want `^vego: invariant of cache, size may not hold on return: size = \|cache\|; it was not kept from entry, since \|cache\| may have changed: the assignment to cache\[k\] at varinv.go:34:3 may write it$`

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
	_ = Size() // want `^vego: invariant of cache, size may not hold before the call to Size, which may assume it: size = \|cache\|; it was not kept from entry, since \|cache\| may have changed: the assignment to cache\[k\] at varinv.go:54:2 may write it$`
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
} // want `^vego: invariant of hits may not hold on return: 0 <= hits; it was not kept from entry, since hits may have changed: the assignment to hits at varinv.go:87:2 may write it$`

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
	w.Write([]byte("x")) // want `^vego: invariant of hits may not hold before the call to w.Write, which may assume it: 0 <= hits; it was not kept from entry, since hits may have changed: the assignment to hits at varinv.go:107:2 may write it$`
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

// @Invariant Forall k in prices : prices[k] >= 0
var prices = map[string]int{}

// setPrice keeps every price not negative.
//
// @Requires p >= 0
// @Modifies prices
// @Ensures True
func setPrice(k string, p int) {
	prices[k] = p
}

// reprice sets two prices; the invariant that the first call restored is
// kept by frame before the second, which may assume it.
//
// @Requires p >= 0
// @Modifies prices, hits
// @Ensures True
func reprice(k string, p int) {
	setPrice(k, p)
	hit()
	setPrice("other", p)
}

// discount may make a price negative.
//
// @Modifies prices
// @Ensures True
func discount(k string) {
	prices[k] = prices[k] - 1
} // want `^vego: invariant of prices may not hold on return: Forall k in prices : prices\[k\] >= 0; it was not kept from entry, since what it reads may have changed: the assignment to prices\[k\] at varinv.go:164:2 may write it$`

// @Invariant |names| <= 100
var names = []string{"a"}

// count reads a slice it is handed, keeps nothing of it, and writes
// nothing through it.
//
// @Ensures n = |s|
func count(s []string) (n int) {
	return len(s)
}

// NamesCount hands the group's slice to count, which only reads it.
//
// @Ensures n <= 100
func NamesCount() (n int) {
	return count(names)
}

// @Invariant |tags| <= 100 And (Forall i in [0, |tags|) : tags[i] != "") // want `^vego: the invariant of tags cannot be relied on: the use of tags at varinv.go:204 lets a reference to what it refers to out of it, so a write through another reference could break the invariant without naming the variable$`
var tags = []string{"x"}

// blank writes through what it is handed.
//
// @Requires |s| > 0
// @Modifies s
// @Ensures True
func blank(s []string) {
	s[0] = ""
}

// Blank hands the group's slice to a function that writes through it,
// which the invariant does not allow.
//
// @Modifies tags
// @Ensures True
func Blank() {
	if len(tags) > 0 {
		blank(tags)
	}
}

// @Invariant cache2 != nil And (Forall k in cache2 : cache2[k] >= 0)
var cache2 = map[string]int{}

// touchThenWrite may set one entry, then writes through w; the invariant
// is kept by frame across the write, since no footprint holds what cache2
// refers to (F35 of the review of step 2 of part 2).
//
// @Requires w != nil
// @Modifies cache2, w
// @Ensures True
func touchThenWrite(w io.Writer, c bool) {
	if c {
		cache2["a"] = 1
	}
	w.Write([]byte("x"))
}

// writeThenReset writes through w and may replace the map.
//
// @Requires w != nil
// @Modifies cache2, w
// @Ensures True
func writeThenReset(w io.Writer) {
	w.Write([]byte("x"))
	if len(cache2) > 1000000 {
		cache2 = map[string]int{}
	}
}

// writeNegative breaks it before the write.
//
// @Requires w != nil
// @Modifies cache2, w
// @Ensures True
func writeNegative(w io.Writer) {
	cache2["a"] = -1
	w.Write([]byte("x"))
} // want `^vego: invariant of cache2 may not hold on return: \(Forall k in cache2 : cache2\[k\] >= 0\)`

type node struct {
	n    int
	next *node
}

// @Invariant head != nil And head.next != nil And head.next.n >= 0
var head = &node{next: &node{n: 1}}

// relink stores, through head's path, memory made where it stands, which
// keeps the group's memory reached only through head (F36 of the review of
// part 2).
//
// @Requires n >= 0
// @Modifies head
// @Ensures True
func relink(n int) {
	if head != nil {
		head.next = &node{n: n}
	}
}

// Peek is not negative, by the invariant.
//
// @Ensures r >= 0
func Peek() (r int) {
	if head == nil || head.next == nil {
		return 0
	}
	return head.next.n
}
