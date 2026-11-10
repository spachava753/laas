// Package mapping holds programs over maps, which either verify or carry the
// defect their expectation names.
package mapping

import "errors"

var errMissing = errors.New("missing")

// Lookup returns the value of a key and whether the map has it.
func Lookup(m map[string]int, k string) (v int, ok bool) {
	v, ok = m[k]
	return v, ok
}

//@ Ensures ok <-> has(m, k)
//@ Ensures ok -> v = m[k]
//@ Ensures ~ok -> v = 0

// Get fails for a key the map does not have.
func Get(m map[string]int, k string) (v int, err error) {
	v, ok := m[k]
	if !ok {
		return 0, errMissing
	}
	return v, nil
}

//@ Ensures err = nil <-> has(m, k)
//@ Ensures err = nil -> v = m[k]

// Set stores a value, which needs a map that is not nil and may be modified.
//
// @ Requires m != nil
// @ Modifies m
func Set(m map[string]int, k string, v int) {
	m[k] = v
}

//@ Ensures has(m', k) And m'[k] = v
//@ Ensures |m| <= |m'| <= |m| + 1

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
	m[1] = 1 // want `vego: m\[1\] is assigned, which SetUndeclared may not modify; list it in a //@ Modifies clause`
}

// Fresh builds a map and knows what is in it.
func Fresh() int {
	m := make(map[int]int)
	m[1] = 10
	m[2] = 20
	return m[1] + m[2] + m[3] + len(m)
}

//@ Ensures result = 32

// Literal does the same with a literal.
func Literal() int {
	m := map[string]int{"a": 1, "b": 2}
	return m["a"] + m["b"] + m["c"]
}

//@ Ensures result = 3

// SameKey overwrites a key, which keeps the number of keys.
func SameKey() int {
	m := map[string]int{"a": 1}
	m["a"] = 5
	return len(m) + m["a"]
}

//@ Ensures result = 6

// Removes deletes a key.
func Removes() int {
	m := map[int]int{1: 1, 2: 2}
	delete(m, 1)
	return len(m) + m[1]
}

//@ Ensures result = 1

// NilRead reads a nil map, which is allowed and finds nothing.
func NilRead() int {
	var m map[string]int
	v, ok := m["a"]
	if ok {
		return 1
	}
	return v + len(m)
}

//@ Ensures result = 0

// TwoMaps writes one map and reads another that may be the same one.
//
// @ Requires a != nil And b != nil
// @ Modifies a
func TwoMaps(a, b map[int]int) int {
	a[1] = 1
	return b[1] // want `vego: postcondition may not hold: result = b\[1\]`
}

//@ Ensures result = b[1]

// TwoMapsApart says that they differ.
//
// @ Requires a != nil And b != nil And a != b
// @ Modifies a
func TwoMapsApart(a, b map[int]int) int {
	a[1] = 1
	return b[1]
}

//@ Ensures result = b[1]

// CallerLoses calls a function that may change the map.
//
// @ Requires m != nil And m["x"] = 3
// @ Modifies m
func CallerLoses(m map[string]int) int {
	Set(m, "y", 1)
	return m["x"] // want `vego: postcondition may not hold: result = 3`
}

//@ Ensures result = 3

// AllSmall checks every value of a map. A loop over a map cannot count its
// iterations in an invariant, so it can say something about each value it
// sees but not add them up.
func AllSmall(m map[int]int) (ok bool) {
	ok = true
	//@ Invariant (Forall k in Z : m[k] <= 10) -> ok
	for _, v := range m {
		if v > 10 {
			ok = false
		}
	}
	return ok
}

//@ Ensures (Forall k in Z : m[k] <= 10) -> ok

// AllSmallWrong claims the converse, which would need to know that the loop
// saw every key.
func AllSmallWrong(m map[int]int) (ok bool) {
	ok = true
	for _, v := range m {
		if v > 10 {
			ok = false
		}
	}
	return ok // want `vego: postcondition may not hold: ok -> Forall k in Z : m\[k\] <= 10`
}

//@ Ensures ok -> Forall k in Z : m[k] <= 10

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
func (r *Registry) Register(name string) int {
	id := r.next
	r.byName[name] = id
	r.next++
	return id
}

//@ Ensures has(r.byName', name) And r.byName'[name] = result And result = r.next And r.next' = r.next + 1

// NewRegistry has to make the map, or the invariant fails.
func NewRegistry() *Registry {
	return &Registry{byName: make(map[string]int)}
}

//@ Ensures fresh(result) And fresh(result.byName) And |result.byName| = 0 And result.next = 0

// NoMap forgets to make it.
func NoMap() *Registry {
	return &Registry{} // want `vego: invariant of Registry may not hold for the result: byName != nil`
}

//@ Ensures fresh(result)

// Uses registers two names.
func Uses() int {
	r := NewRegistry()
	a := r.Register("a")
	b := r.Register("b")
	return b - a
}

//@ Ensures result = 1

// Floats has keys the verifier does not model.
func Floats(m map[float64]int) int { // want `vego: cannot verify Floats: parameter m has unsupported type map\[float64\]int`
	return len(m)
}

//@ Ensures result >= 0

// StringKeys tells two different strings apart and two equal ones not.
func StringKeys(a, b string) int {
	m := map[string]int{}
	m[a] = 1
	m[b] = 2
	return m[a]
}

//@ Ensures a = b -> result = 2
//@ Ensures a != b -> result = 1

// WrongStringKeys forgets that the keys may be equal.
func WrongStringKeys(a, b string) int {
	m := map[string]int{}
	m[a] = 1
	m[b] = 2
	return m[a] // want `vego: postcondition may not hold: result = 1`
}

//@ Ensures result = 1
