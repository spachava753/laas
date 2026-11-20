package guide

import "fmt"

// Stats is a count and a total.
type Stats struct {
	Count, Total int
}

// TallyLoses loses Count: the loop assigns s.Total, so it forgets s.
//
// @Requires |xs| <= 1000
// @Requires Forall k in [0, |xs|) : 0 <= xs[k] <= 1000
// @Ensures s.Count = |xs|
func TallyLoses(xs []int) (s Stats) {
	s.Count = len(xs)
	// @Invariant 0 <= s.Total <= 1000 * i
	for i := range xs {
		s.Total += xs[i]
	}
	return s // want `postcondition may not hold: s.Count = |xs|`
}

// TallyKeeps states Count in the invariant.
//
// @Requires |xs| <= 1000
// @Requires Forall k in [0, |xs|) : 0 <= xs[k] <= 1000
// @Ensures s.Count = |xs|
func TallyKeeps(xs []int) (s Stats) {
	s.Count = len(xs)
	// @Invariant s.Count = |xs| And 0 <= s.Total <= 1000 * i
	for i := range xs {
		s.Total += xs[i]
	}
	return s
}

// grow appends x.
//
// @Requires |s| < 1000000
// @Modifies s
// @Ensures |result| = |s| + 1
// @Ensures fresh(result) Or within(result, s)
func grow(s []int, x int) (result []int) {
	return append(s, x)
}

// CopyThrough appends through grow in a loop.
//
// @Requires |A| <= 1000
// @Ensures True
func CopyThrough(A []int) (out []int) {
	// @Invariant |out| <= i
	for i := range A {
		out = grow(out, A[i]) // want `grow may modify out, which CopyThrough may not modify`
	}
	return out
}

// CopyFresh says that out is its own.
//
// @Requires |A| <= 1000
// @Ensures |out| = |A|
func CopyFresh(A []int) (out []int) {
	// @Invariant |out| = i And fresh(out)
	for i := range A {
		out = grow(out, A[i])
	}
	return out
}

// CopyAppend appends in the loop itself.
//
// @Requires |A| <= 1000
// @Ensures |out| = |A|
func CopyAppend(A []int) (out []int) {
	// @Invariant |out| = i
	for i := range A {
		out = append(out, A[i])
	}
	return out
}

// Runs counts the runs of equal elements.
//
// @Requires |A| <= 1000
// @Ensures 0 <= runs <= |A|
func Runs(A []int) (runs int) {
	i := 0
	// @Invariant 0 <= i <= |A| And 0 <= runs <= i
	// @Variant |A| - i
	for i < len(A) {
		// @Snapshot start = i
		i++
		// @Invariant start < i <= |A| And 0 <= runs <= start
		// @Variant |A| - i
		for i < len(A) && A[i] == A[i-1] {
			i++
		}
		runs++
	}
	return runs
}

// Link holds a value of any type.
type Link struct {
	next  *Link
	Value any
}

// @Requires s != nil
// @Modifies s
// @Ensures s.next' = s And s.Value' = s.Value // want `in Ensures annotation: an interface value can only be compared with nil`
func (s *Link) Loop() {
	s.next = s
}

// Loader loads a number.
type Loader interface {
	// @Ensures True
	Load() (n int, err error)
}

// @Requires l != nil
// @Ensures True
func LoadWrapped(l Loader) (n int, err error) {
	n, err = l.Load()
	if err != nil {
		return 0, fmt.Errorf("load: %w", err) // want `cannot verify LoadWrapped: formatting err would run the methods of an error whose origin is not known`
	}
	return n, nil
}

// @Ensures True
func LocalType(n int) (r int) {
	type pair struct{ a, b int } // want `cannot verify LocalType: local type declarations are not supported`
	p := pair{a: n}
	return p.b
}

// @Ensures True
func RuneString(r rune) (s string) {
	return string(r) // want `cannot verify RuneString: converting a rune to a string is not supported`
}

// reset clears the total.
//
// @Requires s != nil
// @Modifies s.Total
// @Ensures s.Total' = 0
func (s *Stats) reset() {
	s.Total = 0
}

// TallyInMemory keeps Count: s lives in memory, since reset takes its
// address, and the loop writes only s.Total.
//
// @Requires |xs| <= 1000
// @Requires Forall k in [0, |xs|) : 0 <= xs[k] <= 1000
// @Ensures r = |xs|
func TallyInMemory(xs []int) (r int) {
	var s Stats
	s.reset()
	s.Count = len(xs)
	// @Invariant 0 <= s.Total <= 1000 * i
	for i := range xs {
		s.Total += xs[i]
	}
	return s.Count
}

// CopyListed tries to list its result.
//
// @Requires |A| <= 1000
// @Modifies out // want `in Modifies annotation: out is not a parameter`
// @Ensures True
func CopyListed(A []int) (out []int) {
	for i := range A {
		out = append(out, A[i])
	}
	return out
}

// Duplicate copies A into new memory.
//
// @Requires |A| <= 1000
// @Ensures r = A
func Duplicate(A []int) (r []int) {
	return append([]int(nil), A...)
}

// Overwrite returns A after changing an element.
//
// @Requires |A| > 0 And A[0] = 1
// @Modifies A
// @Ensures r = A
func Overwrite(A []int) (r []int) {
	A[0] = 2
	return A // want `postcondition may not hold: r = A`
}
