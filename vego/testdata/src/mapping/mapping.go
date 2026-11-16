// Package mapping holds programs over maps, which either verify or carry the
// defect their expectation names.
package mapping

import "errors"

var errMissing = errors.New("missing")

// Lookup returns the value of a key and whether the map has it.
//
// @ Ensures ok <-> has(m, k)
// @ Ensures ok -> v = m[k]
// @ Ensures ~ok -> v = 0
func Lookup(m map[string]int, k string) (v int, ok bool) {
	v, ok = m[k]
	return v, ok
}

// Get fails for a key the map does not have.
//
// @ Ensures err = nil <-> has(m, k)
// @ Ensures err = nil -> v = m[k]
func Get(m map[string]int, k string) (v int, err error) {
	v, ok := m[k]
	if !ok {
		return 0, errMissing
	}
	return v, nil
}

// Set stores a value, which needs a map that is not nil and may be modified.
//
// @ Requires m != nil
// @ Modifies m
// @ Ensures has(m', k) And m'[k] = v
// @ Ensures |m| <= |m'| <= |m| + 1
func Set(m map[string]int, k string, v int) {
	m[k] = v
}

// SetNil writes to a map that may be nil.
//
// @ Modifies m
func SetNil(m map[string]int, k string) {
	m[k] = 1 // want `vego: map may be nil`
}

// SetUndeclared writes a map without saying so.
//
// @ Requires m != nil
func SetUndeclared(m map[int]int) {
	m[1] = 1 // want `vego: m\[1\] is assigned, which SetUndeclared may not modify; list it in a // @ Modifies clause`
}

// Fresh builds a map and knows what is in it.
//
// @ Ensures result = 32
func Fresh() (result int) {
	m := make(map[int]int)
	m[1] = 10
	m[2] = 20
	return m[1] + m[2] + m[3] + len(m)
}

// Literal does the same with a literal.
//
// @ Ensures result = 3
func Literal() (result int) {
	m := map[string]int{"a": 1, "b": 2}
	return m["a"] + m["b"] + m["c"]
}

// SameKey overwrites a key, which keeps the number of keys.
//
// @ Ensures result = 6
func SameKey() (result int) {
	m := map[string]int{"a": 1}
	m["a"] = 5
	return len(m) + m["a"]
}

// Removes deletes a key.
//
// @ Ensures result = 1
func Removes() (result int) {
	m := map[int]int{1: 1, 2: 2}
	delete(m, 1)
	return len(m) + m[1]
}

// NilRead reads a nil map, which is allowed and finds nothing.
//
// @ Ensures result = 0
func NilRead() (result int) {
	var m map[string]int
	v, ok := m["a"]
	if ok {
		return 1
	}
	return v + len(m)
}

// TwoMaps writes one map and reads another that may be the same one.
//
// @ Requires a != nil And b != nil
// @ Modifies a
// @ Ensures result = b[1]
func TwoMaps(a, b map[int]int) (result int) {
	a[1] = 1
	return b[1] // want `vego: postcondition may not hold: result = b\[1\]`
}

// TwoMapsApart says that they differ.
//
// @ Requires a != nil And b != nil And a != b
// @ Modifies a
// @ Ensures result = b[1]
func TwoMapsApart(a, b map[int]int) (result int) {
	a[1] = 1
	return b[1]
}

// CallerLoses calls a function that may change the map.
//
// @ Requires m != nil And m["x"] = 3
// @ Modifies m
// @ Ensures result = 3
func CallerLoses(m map[string]int) (result int) {
	Set(m, "y", 1)
	return m["x"] // want `vego: postcondition may not hold: result = 3`
}

// AllSmall checks every value of a map. A loop over a map cannot count its
// iterations in an invariant, so it can say something about each value it
// sees but not add them up.
//
// @ Ensures (Forall k in Z : m[k] <= 10) -> ok
func AllSmall(m map[int]int) (ok bool) {
	ok = true
	// @ Invariant (Forall k in Z : m[k] <= 10) -> ok
	for _, v := range m {
		if v > 10 {
			ok = false
		}
	}
	return ok
}

// AllSmallWrong claims the converse, which would need to know that the loop
// saw every key.
//
// @ Ensures ok -> Forall k in Z : m[k] <= 10
func AllSmallWrong(m map[int]int) (ok bool) {
	ok = true
	for _, v := range m {
		if v > 10 {
			ok = false
		}
	}
	return ok // want `vego: postcondition may not hold: ok -> Forall k in Z : m\[k\] <= 10`
}

// RangeWrites changes the map it ranges over.
//
// @ Requires m != nil
// @ Modifies m
func RangeWrites(m map[int]int) {
	for k := range m { // want `vego: cannot verify RangeWrites: the loop modifies a map of the type it ranges over, which is not supported`
		m[k] = 0
	}
}

// Registry holds a map in a struct.
//
// @ Invariant byName != nil
type Registry struct {
	byName map[string]int
	next   int
}

// Register stores the next number under a name.
//
// @ Requires r != nil And r.next < 1000
// @ Modifies r.next, r.byName
// @ Ensures has(r.byName', name) And r.byName'[name] = result And result = r.next And r.next' = r.next + 1
func (r *Registry) Register(name string) (result int) {
	id := r.next
	r.byName[name] = id
	r.next++
	return id
}

// NewRegistry has to make the map, or the invariant fails.
//
// @ Ensures fresh(result) And fresh(result.byName) And |result.byName| = 0 And result.next = 0
func NewRegistry() (result *Registry) {
	return &Registry{byName: make(map[string]int)}
}

// NoMap forgets to make it.
//
// @ Ensures fresh(result)
func NoMap() (result *Registry) {
	return &Registry{} // want `vego: invariant of Registry may not hold for the result: byName != nil`
}

// Uses registers two names.
//
// @ Ensures result = 1
func Uses() (result int) {
	r := NewRegistry()
	a := r.Register("a")
	b := r.Register("b")
	return b - a
}

// Floats has keys the verifier does not model.
//
// @ Ensures result >= 0
func Floats(m map[float64]int) (result int) { // want `vego: cannot verify Floats: parameter m has unsupported type map\[float64\]int`
	return len(m)
}

// StringKeys tells two different strings apart and two equal ones not.
//
// @ Ensures a = b -> result = 2
// @ Ensures a != b -> result = 1
func StringKeys(a, b string) (result int) {
	m := map[string]int{}
	m[a] = 1
	m[b] = 2
	return m[a]
}

// WrongStringKeys forgets that the keys may be equal.
//
// @ Ensures result = 1
func WrongStringKeys(a, b string) (result int) {
	m := map[string]int{}
	m[a] = 1
	m[b] = 2
	return m[a] // want `vego: postcondition may not hold: result = 1`
}

// Named is a map type with a name, which converts to the plain map type
// and stays the same map.
type Named map[int]int

// NamedShares writes through one type and reads through the other.
//
// @ Ensures result = 0
func NamedShares() (result int) {
	a := Named{0: 0}
	b := map[int]int(a)
	b[0] = 1
	return a[0] // want `vego: postcondition may not hold: result = 0`
}

// NamedAssigned does the same without writing the conversion.
//
// @ Ensures result = 1
func NamedAssigned() (result int) {
	a := Named{0: 0}
	var b map[int]int = a
	b[0] = 1
	return a[0]
}

type wrapped struct{ e error }

func (wrapped) Error() string { return "wrapped" }

// BoxesValue lets a struct read from a map become an error.
//
// @ Ensures result = True
func BoxesValue() (result bool) {
	var m map[int]wrapped
	var e error
	e, _ = m[0] // want `vego: cannot verify BoxesValue: converting a mapping.wrapped to a error is not supported here`
	return e == nil
}

// SkippedLiteral builds a map on the right of &&, where the value it stores
// was only checked on condition that it is evaluated.
//
// @ Requires x = MaxInt
// @ Ensures result = 0
func SkippedLiteral(x int) (result int) {
	_ = false && map[int]int{0: x + 1}[0] == 0
	return 1 // want `vego: postcondition may not hold: result = 0`
}

// SkippedSlice does the same with a slice.
//
// @ Requires x = MaxInt
// @ Ensures result = 0
func SkippedSlice(x int) (result int) {
	_ = false && []int{x + 1}[0] == 0
	return 1 // want `vego: postcondition may not hold: result = 0`
}

// Tree is a map type that has itself as its value type.
type Tree map[int]Tree

// Depth reads such a map.
//
// @ Ensures 1 <= result <= 2
func Depth(t Tree) (result int) {
	if len(t[0]) > 0 {
		return 2
	}
	return 1
}

func readyBytes(m map[int]byte) error { return nil }

// @ Ensures result != nil And |result| = 2
func twoBytes() (result map[int]byte) {
	return map[int]byte{0: 0, 1: 0}
}

// AlwaysFailsAfterReadyBytes calls a function that succeeds whenever every
// value of its map is a byte, which is always.
//
// @ Ensures True
func AlwaysFailsAfterReadyBytes() (result error) { // want `vego: the contract of AlwaysFailsAfterReadyBytes may also be met by a function that always returns an error`
	m := twoBytes()
	_ = readyBytes(m)
	return errMissing
}

// GrowsWhileRanging changes the map it ranges over through another name for
// its type.
//
// @ Requires m != nil
// @ Modifies m
// @ Ensures 0 <= result <= 10
func GrowsWhileRanging(m map[int]int) (result int) {
	alias := Named(m)
	n := 0
	// @ Invariant 0 <= n <= 10
	for k := range m { // want `vego: cannot verify GrowsWhileRanging: the loop modifies a map of the type it ranges over, which is not supported`
		if 0 <= k && k < 2 {
			alias[k+1] = 0
		}
		if n < 10 {
			n++
		}
	}
	return n
}

// NilDelete removes a key from a map that may be nil, which does nothing
// then.
//
// @ Modifies m
// @ Ensures result = |m'| And ~has(m', 1) And (m = nil -> result = 0)
func NilDelete(m map[int]int) (result int) {
	delete(m, 1)
	return len(m)
}

// NilDeleteOnly removes a key from the nil map and needs no permission.
//
// @ Ensures result = 0
func NilDeleteOnly() (result int) {
	var m map[string]int
	delete(m, "a")
	return len(m)
}

// NilDeleteWrong claims the nil map lost a key.
//
// @ Requires m = nil
// @ Modifies m
// @ Ensures result = -1
func NilDeleteWrong(m map[int]int) (result int) {
	delete(m, 1)
	return len(m) // want `vego: postcondition may not hold: result = -1`
}

// DeleteUnlisted removes a key from a map it may not change.
//
// @ Ensures True
func DeleteUnlisted(m map[int]int) {
	delete(m, 1) // want `vego: m is modified, which DeleteUnlisted may not modify; list it in a // @ Modifies clause`
}

// removeZero removes a key.
//
// @ Modifies m
// @ Ensures ~has(m', 0)
func removeZero(m map[int]int) {
	delete(m, 0)
}

// RemoveFromNil passes the nil map, which cannot change, to a function
// that modifies its map.
//
// @ Ensures result = 0
func RemoveFromNil() (result int) {
	var m map[int]int
	removeZero(m)
	return len(m)
}

// RemoveFromOther passes a map it may not change.
//
// @ Ensures True
func RemoveFromOther(m map[int]int) {
	removeZero(m) // want `vego: removeZero may modify m, which RemoveFromOther may not modify; list it in a // @ Modifies clause`
}

// ClearsSlices writes a map whose values are slices in a loop.
//
// @ Requires m != nil And n >= 0
// @ Modifies m
// @ Ensures result = 0
func ClearsSlices(m map[int][]int, n int) (result int) {
	// @ Invariant 0 <= i <= n And (i > 0 -> has(m, 0) And |m[0]| = 0)
	// @ Variant n - i
	for i := 0; i < n; i++ {
		m[0] = nil
	}
	if n > 0 {
		return len(m[0])
	}
	return 0
}

// ClearsSlicesWrong claims the loop left a value in place.
//
// @ Requires m != nil And n > 0 And has(m, 0) And |m[0]| = 3
// @ Modifies m
// @ Ensures result = 3
func ClearsSlicesWrong(m map[int][]int, n int) (result int) {
	// @ Invariant 0 <= i <= n
	// @ Variant n - i
	for i := 0; i < n; i++ {
		m[0] = nil
	}
	return len(m[0]) // want `vego: postcondition may not hold: result = 3`
}

type entry struct{ qty int }

// ClearsOne writes the struct that one string key leads to.
//
// @ Requires m[sku] != nil
// @ Modifies m[sku]
// @ Ensures m[sku].qty' = 0
func ClearsOne(m map[string]*entry, sku string) {
	m[sku].qty = 0
}

// ClearsAnother may write only what its own key leads to.
//
// @ Requires m[sku] != nil And m[other] != nil
// @ Modifies m[sku]
func ClearsAnother(m map[string]*entry, sku, other string) {
	m[other].qty = 0 // want `m\[other\].qty is assigned, which ClearsAnother may not modify: nothing its // @ Modifies clauses list is known to cover it`
}

// KeyOfWrongKind indexes a map of strings with a number.
//
// @ Requires m[sku] != nil
// @ Modifies m[0] // want `a map\[string\]\*mapping.entry is indexed by a string: expected a slice or a string but 0 has type int`
func KeyOfWrongKind(m map[string]*entry, sku string) {
	m[sku].qty = 0
}
