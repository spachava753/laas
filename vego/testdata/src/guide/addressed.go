package guide

import (
	"fmt"
	"io"
	"log"
	"math"
	"regexp"
	"strings"
)

// Quota holds a limit.
type Quota struct {
	limit int
	used  int
}

var quota Quota

// loadQuota sets the limit of what q points to.
//
// @Requires q != nil
// @Modifies q.limit
// @Ensures q.limit' = n
func loadQuota(q *Quota, n int) {
	q.limit = n
}

// setupQuota loads the package's quota through its address.
//
// @Modifies quota
// @Ensures quota.limit' = 100
func setupQuota() {
	loadQuota(&quota, 100)
}

// spend writes a field of the variable by its name.
//
// @Requires quota.used < quota.limit
// @Modifies quota.used
// @Ensures quota.used' = quota.used + 1
func spend() {
	quota.used++
}

var transcript strings.Builder

// recordLine writes a line into the builder and a line through w, and keeps the
// length of the builder across the write through w.
//
// @Requires w != nil And |transcript| <= 1000
// @Modifies transcript, w
// @Ensures |transcript'| = |transcript| + 4
func recordLine(w io.Writer) {
	transcript.WriteString("ok.\n")
	fmt.Fprint(w, "ok\n")
}

var scratch strings.Builder

// scratchWriter hands out the address of scratch, so a writer may hold it.
func scratchWriter() io.Writer { return &scratch }

// recordScratch loses the length of scratch across the write through w.
//
// @Requires w != nil And |scratch| <= 1000
// @Modifies scratch, w
// @Ensures |scratch'| = |scratch| + 4
func recordScratch(w io.Writer) {
	scratch.WriteString("ok.\n")
	fmt.Fprint(w, "ok\n")
} // want `^vego: postcondition may not hold: \|scratch'\| = \|scratch\| \+ 4$`

// buildPrimes makes the first primes.
//
// @Ensures |p| = 4
func buildPrimes() (p []int) {
	return []int{2, 3, 5, 7}
}

var primes = buildPrimes()

// largestPrime reads the last element, which the Ensures of buildPrimes
// bounds.
//
// @Ensures True
func largestPrime() (r int) {
	return primes[3]
}

// half halves an even number.
//
// @Requires k % 2 = 0
// @Ensures r * 2 = k
func half(k int) (r int) { return k / 2 }

var halfOfSeven = half(7) // want `^vego: precondition of half may not hold in an initialiser, where a verified function relies on it for what it writes: k % 2 = 0$`

var word = regexp.MustCompile("^[a-z]+$")

// isWord matches with a pattern that is not nil.
//
// @Requires |s| <= 100
// @Ensures True
func isWord(s string) (ok bool) {
	return word.MatchString(s)
}

// isWordHere compiles inside a function.
//
// @Requires |s| <= 100
// @Ensures True
func isWordHere(s string) (ok bool) {
	re := regexp.MustCompile("^[a-z]+$") // want `^vego: cannot verify isWordHere: MustCompile panics when it fails, and its trusted contract holds only where the initialiser of a package-level variable calls it, outside every function: a panic there stops the program, or the plugin that holds the package, before any code reads the variable; elsewhere call a function that returns an error and check it, as regexp.Compile$`
	return re.MatchString(s)
}

// @Invariant low <= high
var (
	low  int
	high int
)

// Bounds returns the bounds.
//
// @Ensures l <= h
func Bounds() (l, h int) {
	return low, high
}

// raise breaks the invariant around a call of strings.ToUpper, which runs
// no code of the package.
//
// @Requires |s| <= 100
// @Modifies low
// @Ensures True
func raise(s string) (r string) {
	if high == math.MaxInt {
		return s
	}
	low = high + 1
	r = strings.ToUpper(s)
	low = high
	return r
}

// raiseLogged breaks it around a call of log.Print, which writes to the
// output that code that is not verified set.
//
// @Modifies low
// @Ensures True
func raiseLogged() {
	if high == math.MaxInt {
		return
	}
	low = high + 1
	log.Print("raised") // want `^vego: invariant of low, high may not hold before the call to Print, which may assume it: low <= high; it was not kept from entry, since low may have changed: the assignment to low at addressed.go:156:2 may write it$`
	low = high
}
