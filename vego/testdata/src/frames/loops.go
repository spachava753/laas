package frames

import "sync"

// Loop invariants kept by frame (step 3): a conjunct is preserved where
// nothing it reads changed since the head of the loop, and a Forall whose
// domain grows is asked of the new elements only.

// Note is a text with tags, which the invariant of its type bounds two
// quantifiers deep, as the trial's Task.
//
// @Invariant |Text| <= 1000 And |Tags| <= 10 And (Forall j in [0, |Tags|) : |Tags[j]| <= 100)
type Note struct {
	ID   int
	Text string
	Tags []string
}

// Lengths appends the length of each task's text into a result whose
// every element the loop invariant bounds: the elements appended before
// stay as they were, and only the new one is proved.
//
// @Requires st != nil And |st.tasks| <= 1000
// @Ensures Forall i in [0, |out|) : out[i] <= 1000
func (st *Store) Lengths() (out []int) {
	// @Visited done
	// @Invariant |out| <= |done| And (Forall i in [0, |out|) : out[i] <= 1000)
	for _, t := range st.tasks {
		out = append(out, len(t.Text))
	}
	return out
}

// Notes appends a note for each task under valid, which a frame compares
// through what the invariant of Note is made of.
//
// @Requires st != nil And |st.tasks| <= 1000
// @Ensures Forall i in [0, |out|) : valid(out[i])
func (st *Store) Notes() (out []Note) {
	// @Visited done
	// @Invariant |out| <= |done| And (Forall i in [0, |out|) : valid(out[i]))
	for k, t := range st.tasks {
		out = append(out, Note{ID: k, Text: t.Text, Tags: t.Tags})
	}
	return out
}

// Shrink drops elements from the end: the domain shrinks, and what is
// left is as it was.
//
// @Requires Forall i in [0, |xs|) : xs[i] > 0
// @Ensures Forall i in [0, |ys|) : ys[i] > 0
func Shrink(xs []int, n int) (ys []int) {
	ys = xs
	// @Invariant Forall i in [0, |ys|) : ys[i] > 0
	// @Variant |ys|
	for len(ys) > n && len(ys) > 0 {
		ys = ys[:len(ys)-1]
	}
	return ys
}

// AppendBad appends an element the invariant does not allow.
//
// @Ensures True
func AppendBad(x int) {
	var ys []int
	// @Invariant |ys| <= 1000 And (Forall i in [0, |ys|) : ys[i] > 0)
	// @Variant 1000 - |ys|
	for len(ys) < 1000 { // want `vego: loop invariant may not be preserved: \(Forall i in \[0, \|ys\|\) : ys\[i\] > 0\)`
		ys = append(ys, x)
	}
}

// Replace replaces the slice with another of the same length, whose
// elements the invariant does not bound.
//
// @Requires Forall i in [0, |xs|) : xs[i] > 0
// @Ensures True
func Replace(xs []int, other [][]int) {
	// @Invariant Forall i in [0, |xs|) : xs[i] > 0
	for k := range other { // want `vego: loop invariant may not be preserved: Forall i in \[0, \|xs\|\) : xs\[i\] > 0`
		if len(other[k]) == len(xs) {
			xs = other[k]
		}
	}
}

// Swap moves an element from one index to another, which the invariant,
// about each index, does not allow.
//
// @Requires |xs| > 1 And (Forall i in [0, |xs|) : xs[i] = i)
// @Modifies xs
// @Ensures True
func Swap(xs []int, n int) {
	// @Invariant |xs| > 1 And (Forall i in [0, |xs|) : xs[i] = i)
	// @Variant n - k
	for k := 0; k < n; k++ { // want `vego: loop invariant may not be preserved: \(Forall i in \[0, \|xs\|\) : xs\[i\] = i\)`
		xs[0], xs[1] = xs[1], xs[0]
	}
}

// AddKey adds keys to a map whose every value the invariant bounds.
//
// @Requires m != nil And (Forall k in m : m[k] > 0)
// @Modifies m
// @Ensures True
func AddKey(m map[int]int, n int) {
	// @Invariant m != nil And (Forall k in m : m[k] > 0)
	// @Variant n - k
	for k := 0; k < n; k++ { // want `vego: loop invariant may not be preserved: \(Forall k in m : m\[k\] > 0\)`
		m[k] = 0
	}
}

// Sorted appends to a sorted slice: the invariant of an element reads its
// neighbour, so the last of the old elements is proved again with the new
// one, which breaks it.
//
// @Ensures True
func Sorted(x int) {
	ys := []int{1}
	// @Invariant |ys| > 0 And |ys| <= 1000 And (Forall i in [0, |ys| - 1) : ys[i] <= ys[i + 1])
	// @Variant 1000 - |ys|
	for len(ys) < 1000 { // want `vego: loop invariant may not be preserved: \(Forall i in \[0, \|ys\| - 1\) : ys\[i\] <= ys\[i \+ 1\]\)`
		ys = append(ys, x)
	}
}

// Reslice grows the slice into its capacity: the element that comes into
// the domain was in memory at the head, unchanged, but no invariant said
// anything of it.
//
// @Requires Forall i in [0, |xs|) : xs[i] > 0
// @Ensures True
func Reslice(xs []int) {
	// @Invariant Forall i in [0, |xs|) : xs[i] > 0
	// @Variant cap(xs) - |xs|
	for len(xs) < cap(xs) { // want `vego: loop invariant may not be preserved: Forall i in \[0, \|xs\|\) : xs\[i\] > 0`
		xs = xs[:len(xs)+1]
	}
}

// WriteEach writes every element in the loop, which the frame must not
// keep: what a layer keeps is only what lies outside what the loop writes.
//
// @Requires Forall i in [0, |xs|) : xs[i] > 0
// @Modifies xs
// @Ensures True
func WriteEach(xs []int, x int) {
	// @Invariant Forall i in [0, |xs|) : xs[i] > 0
	for k := range xs { // want `vego: loop invariant may not be preserved: Forall i in \[0, \|xs\|\) : xs\[i\] > 0`
		xs[k] = x
	}
}

// Locked is a store of notes guarded by a mutex, as the trial's store is.
//
// @Owns notes
// @Invariant notes != nil And |notes| <= 1000 And (Forall k in notes : |notes[k].Text| <= 1000 And |notes[k].Tags| <= 10 And (Forall j in [0, |notes[k].Tags|) : |notes[k].Tags[j]| <= 100))
type Locked struct {
	sync.Mutex
	notes map[int]Note
}

// ByLength collects the notes of a length, under the lock: at the base
// the loop invariant over the result was not proved at the limit, and the
// frame asks it of the new note only.
//
// @Requires ls != nil And ~held(ls.Mutex)
// @Modifies ls.Mutex
// @Ensures ~held(ls.Mutex') And |out| <= 1000 And (Forall i in [0, |out|) : valid(out[i]))
func (ls *Locked) ByLength(n int) (out []Note) {
	ls.Lock()
	defer ls.Unlock()
	// @Visited done
	// @Invariant |out| <= |done| And (Forall i in [0, |out|) : valid(out[i]))
	for _, note := range ls.notes {
		if len(note.Text) == n {
			out = append(out, note)
		}
	}
	return out
}

// BreakThenInner breaks the outer loop's invariant before an inner loop
// whose invariant is another: the outer conjunct is framed only from a
// head where a conjunct of the same text was assumed, and none was after
// the write.
//
// @Requires |xs| > 0 And (Forall i in [0, |xs|) : xs[i] > 0)
// @Modifies xs
// @Ensures True
func BreakThenInner(xs []int, n int) {
	// @Invariant |xs| > 0 And (Forall i in [0, |xs|) : xs[i] > 0)
	// @Variant n - k
	for k := 0; k < n; k++ { // want `vego: loop invariant may not be preserved: \(Forall i in \[0, \|xs\|\) : xs\[i\] > 0\)`
		xs[0] = -1
		// @Invariant |xs| > 0
		// @Variant 3 - j
		for j := 0; j < 3; j++ {
		}
	}
}

// setFirst writes the first element.
//
// @Requires |xs| > 0
// @Modifies xs
// @Ensures True
func setFirst(xs []int, x int) {
	xs[0] = x
}

// WriteByCall writes through a call in the loop, which leaves a layer
// between the head and the end of the body: what a frame gathers of it
// under the quantifier is only what lies outside what the call writes.
//
// @Requires |xs| > 0 And (Forall i in [0, |xs|) : xs[i] > 0)
// @Modifies xs
// @Ensures True
func WriteByCall(xs []int, x, n int) {
	// @Invariant |xs| > 0 And (Forall i in [0, |xs|) : xs[i] > 0)
	// @Variant n - k
	for k := 0; k < n; k++ { // want `vego: loop invariant may not be preserved: \(Forall i in \[0, \|xs\|\) : xs\[i\] > 0\)`
		setFirst(xs, x)
	}
}
