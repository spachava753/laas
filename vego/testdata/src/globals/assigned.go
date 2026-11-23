package globals

import (
	"io"
	"math"
)

// Assigned package-level variables (part 2 of package-level variables):
// their storage lies in regions of their own, a verified function lists
// what it changes, and a caller forgets what a callee lists.

var hits int

// Hit counts a hit, and saturates.
//
// @Modifies hits
// @Ensures hits < MaxInt -> hits' = hits + 1
func Hit() {
	if hits < math.MaxInt {
		hits++
	}
}

// HitUnlisted assigns the variable and does not list it.
//
// @Ensures True
func HitUnlisted() {
	hits = 0 // want `^vego: hits is assigned, which HitUnlisted may not modify; list it in a // @Modifies clause$`
}

// Hits reads it.
//
// @Ensures r = hits
func Hits() (r int) {
	return hits
}

// HitTwice claims the variable is the same around a call that changes it.
//
// @Modifies hits
// @Ensures r
func HitTwice() (r bool) {
	a := hits
	Hit()
	return a == hits // want `^vego: postcondition may not hold: r$`
}

// @Requires hits < MaxInt
// @Modifies hits
// @Ensures r
func hitOnce() (r bool) {
	a := hits
	Hit()
	return hits == a+1
}

// HitsKept reads it around a call that does not change it.
//
// @Ensures r
func HitsKept() (r bool) {
	a := hits
	_ = Hits()
	return a == hits
}

// CallsHit calls Hit and does not list what it changes.
//
// @Ensures True
func CallsHit() {
	Hit() // want `^vego: Hit may modify what it calls hits, which CallsHit may not modify; list it in a // @Modifies clause$`
}

// HitLoop calls Hit in a loop.
//
// @Requires 0 <= n
// @Modifies hits
// @Ensures True
func HitLoop(n int) {
	// @Variant n - i
	for i := 0; i < n; i++ {
		Hit()
	}
}

// LoopKeeps claims the variable unchanged after a loop that writes it.
//
// @Requires 0 < n
// @Modifies hits
// @Ensures hits' = hits
func LoopKeeps(n int) {
	// @Variant n - i
	for i := 0; i < n; i++ {
		hits = 5
	}
} // want `^vego: postcondition may not hold: hits' = hits$`

type tally struct{ hits, misses int }

var stats tally

// @Requires stats.misses < 1000
// @Modifies stats.misses
// @Ensures stats.misses' = stats.misses + 1 And stats.hits' = stats.hits
func miss() {
	stats.misses++
}

// ResetStats sets both fields.
//
// @Modifies stats
// @Ensures stats.hits' = 0 And stats.misses' = 0
func ResetStats() {
	stats = tally{}
}

// @Modifies hits
// @Ensures r = 1
func setHits() (r int) {
	hits = 7
	return 1
}

// Ordered reads the variable beside a call that writes it.
//
// @Requires hits < 100
// @Modifies hits
// @Ensures True
func ordered() (r int) {
	return hits + setHits() // want `^vego: hits may be read before or after the call to setHits, which may change it, and Go does not fix the order; split the statement so that the order is the one you mean, as in hits0 := hits before it$`
}

// DeferredHits writes in a deferred literal.
//
// @Modifies hits
// @Ensures hits' = 3
func DeferredHits() {
	defer func() { hits = 3 }()
	hits = 1
}

// InPlaceHits writes in a literal called where it is written.
//
// @Modifies hits
// @Ensures hits' = 4
func InPlaceHits() {
	func() { hits = 4 }()
}

// OldHits claims the entry value is the current one after a write.
//
// @Modifies hits
// @Ensures True
func OldHits() {
	hits = 9
	// @Assert old(hits) = hits // want `^vego: assertion may not hold: old\(hits\) = hits$`
}

// @Ensures True
type reader func() (r int)

// ValueHits makes a value where hits is 5, and calls it after hits became
// 6: the value reads the variable when it runs.
//
// @Modifies hits
// @Ensures r = 5
func ValueHits() (r int) {
	hits = 5
	var f reader = func() (r int) { return hits }
	hits = 6
	return f() // want `^vego: postcondition may not hold: r = 5$`
}

var errBusy = errorsNew()

func errorsNew() error { return nil }

// Busy says when it succeeds, which a sample of hits shows can happen.
//
// @Ensures hits = 0 -> err = nil
func Busy() (err error) {
	if hits != 0 {
		return errBusy
	}
	return nil
}

var byName = map[string]int{}

// Register fills a table that a fixed variable holds.
//
// @Modifies byName
// @Ensures byName'[k] = n
func Register(k string, n int) {
	byName[k] = n
}

// RegisterUnlisted does not list it.
//
// @Ensures True
func RegisterUnlisted(k string) {
	byName[k] = 1 // want `^vego: byName\[k\] is assigned, which RegisterUnlisted may not modify; it is memory that the package-level variable byName refers to; list byName in a // @Modifies clause$`
}

var cache map[string]int

// Fill makes the map of an assigned variable and writes it.
//
// @Modifies cache
// @Ensures cache'["k"] = 1
func Fill() {
	if cache == nil {
		cache = map[string]int{}
	}
	cache["k"] = 1
}

// Answer counts and writes through a writer, which keeps the count.
//
// @Requires w != nil
// @Modifies hits, w
// @Ensures hits < MaxInt -> hits' = hits + 1
func Answer(w io.Writer) {
	Hit()
	w.Write([]byte("x"))
}

// Hidden asks of its callers a condition on a variable they cannot name.
//
// @Requires hits < 10 // want `^vego: the Requires clause hits < 10 reads hits, a package-level variable that is not exported, and code of another package can call Hidden, where no caller can name the condition or see it fail; test the value in the body instead$`
// @Ensures True
func Hidden() {}

// @Requires hits < 10
// @Ensures True
func hidden2() {}

// usesHidden2 meets it.
//
// @Modifies hits
// @Ensures True
func usesHidden2() {
	hits = 0
	hidden2()
}

// valued is unexported, and is made into a value here.
var _ = valued

// @Requires hits < 10 // want `^vego: the Requires clause hits < 10 reads hits, a package-level variable that is not exported, and code of another package can call valued, where no caller can name the condition or see it fail; test the value in the body instead$`
// @Ensures True
func valued() {}

// WriteThenAnswer claims a write before a write through w is lost.
//
// @Requires w != nil
// @Modifies hits, w
// @Ensures hits' = hits
func WriteThenAnswer(w io.Writer) {
	hits = 5
	w.Write([]byte("x"))
} // want `^vego: postcondition may not hold: hits' = hits$`

// ReadAroundAnswer keeps a variable it only reads across a write through w.
//
// @Requires w != nil
// @Modifies w
// @Ensures r
func ReadAroundAnswer(w io.Writer) (r bool) {
	a := hits
	w.Write([]byte("x"))
	return a == hits
}
