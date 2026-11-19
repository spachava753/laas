package callbacks

import (
	"math/rand"
	"sort"
	"strings"
)

// The trusted helpers whose entries speak of what the function they are
// handed returns.

func probe(f func(p int8) bool) bool { return f(0) }

func pair(f func(i int) bool) (a, b bool) { return f(0), f(0) }

func touchAsk(c *counter, f func(i int) bool) bool {
	c.n++
	return f(0)
}

func memReq(xs []int, f func(i int) bool) bool { return false }
func twoArgs(f func(i, j int) bool) bool       { return f(0, 0) }
func appliedEarly(f func(i int) bool) bool     { return f(0) }

// BinarySearch finds where x belongs in a sorted slice.
//
// @Requires Forall i in [0, |s|) : Forall j in [i, |s|) : s[i] <= s[j]
// @Ensures 0 <= i <= |s|
// @Ensures Forall k in [0, i) : s[k] < x
// @Ensures i < |s| -> s[i] >= x
func BinarySearch(s []int, x int) (i int) {
	return sort.Search(len(s), func(i int) bool { return s[i] >= x })
}

// Unsorted claims as much for a slice that may not be sorted.
//
// @Ensures 0 <= i <= |s|
func Unsorted(s []int, x int) (i int) {
	return sort.Search(len(s), func(i int) bool { return s[i] >= x }) // want `vego: postcondition may not hold: 0 <= i <= \|s\|`
}

// atLeastFive is verified, and what it returns is fixed by its argument.
//
// @Ensures b <-> i >= 5
func atLeastFive(i int) (b bool) {
	return i >= 5
}

// FindsFive hands sort.Search a function whose result its contract fixes.
//
// @Requires n > 5
// @Ensures r = 5
func FindsFive(n int) (r int) {
	return sort.Search(n, atLeastFive)
}

// HandsLoose hands it one whose contract does not fix its result.
//
// @Requires n > 5
// @Ensures True
func HandsLoose(n int) (r int) {
	return sort.Search(n, positive) // want `vego: positive run by sort.Search is not proved to return the same result whenever it is called with the same argument, which the trusted contract of sort.Search relies on`
}

// FindsInRange hands sort.Find a comparison.
//
// @Requires Forall i in [0, |s|) : Forall j in [i, |s|) : s[i] <= s[j]
// @Requires Forall i in [0, |s|) : 0 <= s[i] <= 1000
// @Requires 0 <= x <= 1000
// @Ensures found -> s[i] = x
// @Ensures ~found -> Forall k in [0, |s|) : s[k] != x
func FindsInRange(s []int, x int) (i int, found bool) {
	return sort.Find(len(s), func(k int) int { return x - s[k] })
}

// Random hands sort.Search a function that answers at random.
//
// @Requires n >= 0
// @Ensures True
func Random(n int) (r int) {
	return sort.Search(n, func(i int) bool { // want `vego: the function literal run by sort.Search is not proved to return the same result whenever it is called with the same argument`
		return rand.Intn(2) == 0
	})
}

// Pair asks pair, which calls what it is handed twice with the same
// argument, about a function that answers at random.
//
// @Ensures a = b
func Pair() (a, b bool) {
	return pair(func(i int) bool { // want `vego: the function literal run by pair is not proved to return the same result whenever it is called with the same argument`
		return rand.Intn(2) == 0
	})
}

// Remembers answers with what an earlier run left in a variable it
// captures.
//
// @Ensures a = b
func Remembers() (a, b bool) {
	x := 0
	return pair(func(i int) bool { // want `vego: the function literal run by pair is not proved to return the same result whenever it is called with the same argument`
		r := x > 0
		x = i + 1
		return r
	})
}

// Narrow hands probe a function of an int8, which only runs for numbers of
// that type; nothing follows for others.
//
// @Requires |a| = 256
// @Ensures True
func Narrow(a []int) {
	_ = probe(func(p int8) bool { return a[int(p)+128] > 0 })
	// @Assert False // want `vego: assertion may not hold: False`
}

// ReadsWhatIsWritten hands touchAsk a function that answers from the
// counter that touchAsk writes.
//
// @Requires c != nil And c.n < 1000
// @Modifies c
// @Ensures True
func ReadsWhatIsWritten(c *counter) (b bool) {
	return touchAsk(c, func(i int) bool { // want `vego: the function literal run by touchAsk is not proved to return the same result whenever it is called with the same argument`
		return c.n > 0
	})
}

// ReadsOther answers from a counter that nothing writes.
//
// @Requires c != nil And d != nil And c != d
// @Requires c.n < 1000 And d.n = 3
// @Modifies c
// @Ensures b
func ReadsOther(c, d *counter) (b bool) {
	return touchAsk(c, func(i int) bool { return d.n > 0 })
}

// Counting hands strings.FieldsFunc a predicate that counts its calls.
//
// @Ensures True
func Counting(line string) (n int) {
	calls := 0
	fields := strings.FieldsFunc(line, func(r rune) bool { // want `vego: the function literal run by strings.FieldsFunc is not proved to return the same result whenever it is called with the same argument`
		before := calls
		calls = 1
		return before > 0 && r == ','
	})
	return len(fields)
}

// Fields hands it a predicate that does not.
//
// @Ensures True
func Fields(line string) (n int) {
	fields := strings.FieldsFunc(line, func(r rune) bool { return r == ',' || r == ';' })
	return len(fields)
}

// countdown hands sort.Search a function that calls countdown on a
// smaller number.
//
// @Requires n >= 0
// @Variant n
// @Ensures b
func countdown(n int) (b bool) {
	_ = sort.Search(n, func(i int) bool { return countdown(i) })
	return true
}

// UsesMemReq and the functions after it call the helpers whose entries
// apply what they are handed and have a defect.
//
// @Ensures True
func UsesMemReq(xs []int) {
	_ = memReq(xs, func(i int) bool { return true }) // want `the trusted contract of callbacks.memReq \(trusted.yaml:\d+\) cannot be used: its ensures applies f, and its calls requires for f read memory` `cannot verify UsesMemReq: `
}

// @Ensures True
func UsesTwoArgs() {
	_ = twoArgs(func(i, j int) bool { return true }) // want `its ensures applies f, whose type func\(i int, j int\) bool does not have one integer parameter and one integer or boolean result` `cannot verify UsesTwoArgs: `
}

// @Ensures True
func UsesAppliedEarly() {
	_ = appliedEarly(func(i int) bool { return true }) // want `its requires "f\(0\)" applies f; only its ensures can speak of what f returns` `in its requires "f\(0\)": f\(...\) can only be used in ensures` `cannot verify UsesAppliedEarly: `
}
