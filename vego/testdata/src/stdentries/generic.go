package stdentries

import "slices"

// Entity is a record of the kind the trial's knowledge graph holds.
type Entity struct {
	Name         string
	Observations []string
}

// Graph holds entities.
type Graph struct {
	Entities []Entity
}

// HasName reports whether a name is among names.
//
// @Ensures r <-> Exists i in [0, |names|) : names[i] = name
func HasName(names []string, name string) (r bool) {
	return slices.Contains(names, name)
}

// HasNameWrong says it is always there.
//
// @Ensures r
func HasNameWrong(names []string, name string) (r bool) {
	return slices.Contains(names, name) // want `postcondition may not hold: r`
}

// HasEntity is the trial's check for a name among entities, with a
// literal that compares a field.
//
// @Ensures r -> |g.Entities| > 0
func HasEntity(g Graph, name string) (r bool) {
	return slices.ContainsFunc(g.Entities, func(e Entity) bool { return e.Name == name })
}

// HasEntityWhole compares whole entities, which a formula cannot do.
//
// @Ensures True
func HasEntityWhole(es []Point2, e Point2) (r bool) {
	return slices.Contains(es, e) // want `the trusted contract of slices.Contains \(slices.yaml:\d+\) cannot be used with S = \[\]Point2, E = Point2: in its ensures "result <-> Exists i in \[0, \|s\|\) : s\[i\] = v": a value of type E, which is Point2 here, is a struct, and a formula cannot compare a struct or use it as a whole; call slices.ContainsFunc instead, with a function literal that compares what you need of the elements, or write a loop`
}

// Point2 is a comparable struct.
type Point2 struct{ X, Y int }

// Observe is the trial's addObservations: an index found by a literal is
// used to read an element.
//
// @Requires |g.Entities| <= 100
// @Ensures True
func Observe(g Graph, name string) (n int) {
	i := slices.IndexFunc(g.Entities, func(e Entity) bool { return e.Name == name })
	if i == -1 {
		return 0
	}
	return len(g.Entities[i].Observations)
}

// ObserveUnchecked reads the element without checking for -1.
//
// @Ensures True
func ObserveUnchecked(g Graph, name string) (n int) {
	i := slices.IndexFunc(g.Entities, func(e Entity) bool { return e.Name == name })
	return len(g.Entities[i].Observations) // want `index may be negative`
}

// Drop is the trial's deleteEntities: the entities a map names are
// deleted from a graph the function made.
//
// @Requires |names| <= 100 And |es| <= 1000
// @Ensures |r.Entities| <= |es|
func Drop(es []Entity, names []string) (r Graph) {
	g := Graph{Entities: slices.Clone(es)}
	drop := map[string]bool{}
	// @Invariant 0 <= i And i <= |names|
	// @Variant |names| - i
	for i := 0; i < len(names); i++ {
		drop[names[i]] = true
	}
	g.Entities = slices.DeleteFunc(g.Entities, func(e Entity) bool { return drop[e.Name] })
	return g
}

// DropInPlace deletes from a slice it was given without listing it.
//
// @Ensures True
func DropInPlace(es []Entity) (r []Entity) {
	return slices.DeleteFunc(es, func(e Entity) bool { return e.Name == "" }) // want `DeleteFunc may modify es, which DropInPlace may not modify`
}

// DropNested is the trial's deleteRelations: the literal handed to
// DeleteFunc hands one to ContainsFunc.
//
// @Modifies es
// @Ensures |r| <= |es|
func DropNested(es, gone []Entity) (r []Entity) {
	return slices.DeleteFunc(es, func(e Entity) bool {
		return slices.ContainsFunc(gone, func(o Entity) bool { return o.Name == e.Name })
	})
}

// AppendEncode is the trial's hex.AppendEncode: room is made with Grow and
// written within the capacity.
//
// @Requires |dst| + 2 * |src| <= 1000000
// @Modifies dst
// @Ensures |r| = |dst| + 2 * |src|
func AppendEncode(dst, src []byte) (r []byte) {
	n := 2 * len(src)
	dst = slices.Grow(dst, n)
	out := dst[len(dst):][:n]
	// @Invariant 0 <= i And i <= |src| And |out| = 2 * |src|
	// @Variant |src| - i
	for i := 0; i < len(src); i++ {
		out[2*i] = 'a' + src[i]>>4
		out[2*i+1] = 'a' + src[i]&0x0f
	}
	return dst[:len(dst)+n]
}

// GrowTooFar grows by an amount no bound keeps within an allocation.
//
// @Requires n >= 0
// @Ensures True
func GrowTooFar(dst []int64, n int) (r []int64) {
	return slices.Grow(dst, n) // want `precondition of Grow may not hold: \|s\| \+ n <= MaxInt` `precondition of Grow may not hold: 2 \* \(\|s\| \+ n\) \* elemsize\(s\) \+ 65536 <= MaxAlloc`
}

// GrowNil may return a slice that is not nil for a nil one.
//
// @Requires s = nil
// @Ensures r = nil
func GrowNil(s []int, n int) (r []int) {
	if n < 0 || n > 10 {
		return nil
	}
	return slices.Grow(s, n) // want `postcondition may not hold: r = nil`
}

// WriteClone writes an inner slice of a shallow clone, which is the inner
// slice of what it was given.
//
// @Requires 0 < |xs| And |xs| <= 1000 And |xs[0]| > 0
// @Ensures True
func WriteClone(xs [][]int) {
	c := slices.Clone(xs)
	if len(c) > 0 && len(c[0]) > 0 {
		c[0][0] = 1 // want `c\[0\]\[0\] is assigned, which WriteClone may not modify`
	}
}

// Box is a struct behind a pointer.
type Box struct{ X int }

// WriteClonePointer writes through a pointer a clone holds.
//
// @Requires 0 < |ps| And |ps| <= 1000
// @Ensures True
func WriteClonePointer(ps []*Box) {
	c := slices.Clone(ps)
	if len(c) > 0 && c[0] != nil {
		c[0].X = 1 // want `c\[0\].X is assigned, which WriteClonePointer may not modify`
	}
}

// WriteCloneOwn writes the clone itself, which is new.
//
// @Requires |xs| <= 1000
// @Ensures |r| = |xs|
func WriteCloneOwn(xs []int) (r []int) {
	c := slices.Clone(xs)
	if len(c) > 0 {
		c[0] = 1
	}
	return c
}

// SameSlice compares a slice with itself, which slice parameters of one
// element type may not share memory for.
//
// @Ensures True
func SameSlice(a []int) (r bool) {
	return slices.Equal(a, a) // want `the slices passed to Equal as s1 and s2 may overlap`
}

// Equals compares two slices.
//
// @Ensures r -> |a| = |b|
func Equals(a, b []string) (r bool) {
	return slices.Equal(a, b)
}

// ClipThenAppend clips a slice, so that an append moves it.
//
// @Requires |s| < 1000
// @Ensures cap(r) = |s|
func ClipThenAppend(s []int) (r []int) {
	return slices.Clip(s)
}

// InsertAt inserts at an index.
//
// @Requires 0 <= i And i <= |s| And |s| < 1000
// @Modifies s
// @Ensures |r| = |s| + 2
func InsertAt(s []string, i int) (r []string) {
	return slices.Insert(s, i, "a", "b")
}

// InsertPast inserts past the end.
//
// @Requires |s| < 1000
// @Modifies s
// @Ensures True
func InsertPast(s []string) (r []string) {
	return slices.Insert(s, len(s)+1, "a") // want `precondition of Insert may not hold: i <= \|s\|`
}

// DeleteFirst deletes the first element.
//
// @Requires |s| > 0
// @Modifies s
// @Ensures |r| = |s| - 1
func DeleteFirst(s []Entity) (r []Entity) {
	return slices.Delete(s, 0, 1)
}

// Rank has a String method, which the entries claim to run none of.
type Rank int

// String names a level.
//
// @Ensures True
func (l Rank) String() (s string) { return "level" }

// SortRanks sorts ranks.
//
// @Modifies ls
// @Ensures True
func SortRanks(ls []Rank) {
	slices.Sort(ls)
}

// SortKeys sorts strings.
//
// @Modifies keys
// @Ensures |keys| = |keys|
func SortKeys(keys []string) {
	slices.Sort(keys)
	slices.Reverse(keys)
}

// Search finds an integer in a sorted slice.
//
// @Requires Forall i in [0, |xs|) : Forall j in [i, |xs|) : xs[i] <= xs[j]
// @Ensures found -> xs[i] = x
func Search(xs []int, x int) (i int, found bool) {
	return slices.BinarySearch(xs, x)
}

// SearchUnsorted searches a slice that need not be sorted.
//
// @Ensures True
func SearchUnsorted(xs []int, x int) (i int, found bool) {
	return slices.BinarySearch(xs, x) // want `precondition of BinarySearch may not hold`
}

// SearchStrings searches strings, which a formula cannot say are sorted.
//
// @Ensures True
func SearchStrings(xs []string, x string) (i int, found bool) {
	return slices.BinarySearch(xs, x) // want `cannot be used with S = \[\]string, E = string: in its requires .*a formula has no order of them; write a loop instead`
}

// Largest is at least the first element.
//
// @Requires |xs| > 0
// @Ensures r >= xs[0]
func Largest(xs []int) (r int) {
	return slices.Max(xs)
}

// Unique compacts a slice of entities, whose elements no clause compares.
//
// @Modifies s
// @Ensures |r| <= |s|
func Unique(s []Point2) (r []Point2) {
	return slices.Compact(s)
}
