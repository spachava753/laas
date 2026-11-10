// Package trust exercises calls to functions that are not verified: every
// such call needs a trusted contract, from the project's file or from the
// ones shipped with vego.
package trust

import (
	"math/rand"
	"os"
	"sort"
	"strings"
)

func helper(x int) int { return x + 1 }

// CallsWithoutContract calls a function that is neither verified nor trusted.
func CallsWithoutContract(x int) (y int) {
	return helper(x) // want `vego:\ cannot\ verify\ CallsWithoutContract:\ it\ calls\ helper,\ which\ has\ no\ contract;\ annotate\ helper\ with\ //@\ so\ that\ it\ is\ verified,\ or\ add\ a\ trusted\ contract\ for\ trust\.helper\ to\ vego\-trusted\.yaml`
}

//@ Ensures y = x + 1

// CallsStandardLibrary calls a standard-library function vego ships no
// contract for.
func CallsStandardLibrary() (n int) {
	return os.Getpid() // want `vego:\ cannot\ verify\ CallsStandardLibrary:\ it\ calls\ Getpid,\ which\ has\ no\ contract;\ annotate\ Getpid\ with\ //@\ so\ that\ it\ is\ verified,\ or\ add\ a\ trusted\ contract\ for\ os\.Getpid\ to\ vego\-trusted\.yaml`
}

//@ Ensures n >= 0

func readConfig(path string) (size int, err error) {
	info, err := os.Stat(path)
	if err != nil {
		return 0, err
	}
	return int(info.Size()), nil
}

// ConfigSize relies on the trusted contract of readConfig. Nothing says when
// readConfig succeeds, so ConfigSize is not asked to promise success either.
func ConfigSize(path string) (size int, err error) {
	size, err = readConfig(path)
	if err != nil {
		return 0, err
	}
	return size, nil
}

//@ Ensures err = nil -> size >= 0

func parsePort(n int) (port int, err error) {
	if n < 0 || n > 65535 {
		return 0, os.ErrInvalid
	}
	return n, nil
}

// Port relies on a trusted contract that does say when the callee succeeds,
// so it has to say when it succeeds itself.
func Port(n int) (port int, err error) { // want `vego:\ the\ contract\ of\ Port\ would\ also\ be\ met\ by\ a\ function\ that\ always\ returns\ an\ error;\ state\ when\ it\ succeeds\ with\ a\ clause\ such\ as\ "condition\ \->\ err\ =\ nil",\ where\ the\ condition\ is\ about\ the\ inputs\ and\ some\ input\ satisfies\ it`
	return parsePort(n)
}

//@ Ensures err = nil -> port = n

// PortExactly does.
func PortExactly(n int) (port int, err error) {
	return parsePort(n)
}

//@ Ensures 0 <= n <= 65535 -> err = nil
//@ Ensures err = nil -> port = n

func fill(dst []int, value int) {
	for i := range dst {
		dst[i] = value
	}
}

func readOnly(src []int) int { return len(src) }

// Filled uses what the trusted contract says about the slice afterwards.
//
// @ Requires |A| > 0
func Filled(A []int) (first int) {
	fill(A, 7)
	return A[0]
}

//@ Ensures first = 7

// Untouched keeps what it knew about a slice that a trusted function does
// not list under modifies.
//
// @ Requires |A| > 0 And A[0] = 3
func Untouched(A []int) (first int) {
	n := readOnly(A)
	if n < 0 {
		return 0
	}
	return A[0]
}

//@ Ensures first = 3

func contradictory() int { return 0 }

// UsesContradiction would prove anything from a contract that cannot hold.
func UsesContradiction() (n int) {
	return contradictory() // want `vego:\ cannot\ verify\ UsesContradiction:\ contradictory\ has\ a\ contract\ that\ could\ not\ be\ understood` `vego:\ the\ trusted\ contract\ of\ trust\.contradictory\ \(trusted\.yaml:59\)\ cannot\ be\ used:\ it\ contradicts\ itself,\ so\ anything\ could\ be\ proved\ from\ it`
}

//@ Ensures n = 42

func wrongModifies(count int) {}

// UsesWrongModifies relies on a contract whose modifies makes no sense.
func UsesWrongModifies() {
	//@ Assert True
	wrongModifies(1) // want `vego:\ cannot\ verify\ UsesWrongModifies:\ wrongModifies\ has\ a\ contract\ that\ could\ not\ be\ understood` `vego:\ the\ trusted\ contract\ of\ trust\.wrongModifies\ \(trusted\.yaml:65\)\ cannot\ be\ used:\ its\ modifies\ lists\ count,\ which\ is\ not\ a\ slice\ parameter\ of\ the\ function`
}

func wrongName(count int) int { return count }

// UsesWrongName relies on a contract that names something that is not there.
func UsesWrongName() (n int) {
	return wrongName(1) // want `vego:\ cannot\ verify\ UsesWrongName:\ wrongName\ has\ a\ contract\ that\ could\ not\ be\ understood` `vego:\ the\ trusted\ contract\ of\ trust\.wrongName\ \(trusted\.yaml:69\)\ cannot\ be\ used:\ in\ its\ ensures\ "total\ >=\ 0":\ unknown\ name\ total`
}

//@ Ensures n >= 0

func makesSlice() []int { return nil }

// UsesTrustedSlice gets a slice from a trusted function.
func UsesTrustedSlice() (n int) {
	s := makesSlice() // want `vego:\ cannot\ verify\ UsesTrustedSlice:\ makesSlice\ returns\ a\ slice;\ a\ trusted\ contract\ cannot\ yet\ say\ that\ the\ slice\ shares\ no\ storage`
	return len(s)
}

//@ Ensures n >= 0

// Verified has annotations and a trusted contract.
func Verified() int { // want `vego:\ Verified\ has\ //@\ annotations\ and\ a\ trusted\ contract;\ a\ function\ is\ either\ verified\ or\ trusted,\ not\ both`
	return 0
}

//@ Ensures result = 0

// Sorted relies on the shipped contract of sort.Ints.
//
// @ Requires |A| >= 2
func Sorted(A []int) (ordered bool) {
	sort.Ints(A)
	return A[0] <= A[1]
}

//@ Ensures ordered = True

// Roll relies on the shipped contract of rand.Intn.
func Roll() (face int) {
	return rand.Intn(6) + 1
}

//@ Ensures 1 <= face <= 6

// RollZero breaks the precondition that contract states.
func RollZero() int {
	//@ Assert True
	return rand.Intn(0) // want `vego:\ precondition\ of\ Intn\ may\ not\ hold:\ n\ >\ 0`
}

// Scheme relies on the shipped contract of strings.HasPrefix.
func Scheme(url string) (secure bool) {
	return strings.HasPrefix(url, "https://")
}

//@ Ensures secure = True -> (|url| >= 8 And url[0] = 104)

// Overridden calls a function whose shipped contract the project file
// replaces with one that says nothing.
//
// @ Requires |A| = 0
func Overridden(A []int) (ok bool) {
	return sort.IntsAreSorted(A) // want `vego:\ postcondition\ may\ not\ hold:\ ok\ =\ True`
}

//@ Ensures ok = True
