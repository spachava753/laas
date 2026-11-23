package jsonenc

import (
	"encoding/json"
	"sync"
)

// What is refused, each with its message.

// Unbounded encodes a value nothing bounds.
//
// @Ensures True
func Unbounded(l Loose) (n int) {
	js, _ := json.Marshal(l) // want `what Marshal builds from l may be more than can be allocated; bound what it encodes, as in // @Requires \|l\.Name\| <= 1000000 And \|l\.Tags\| <= 1000000 And \(Forall `
	return len(js)
}

// UnboundedSlice encodes a slice nothing bounds.
//
// @Ensures True
func UnboundedSlice(ls []Loose) (n int) {
	js, _ := json.Marshal(ls) // want `what Marshal builds from ls may be more than can be allocated; bound what it encodes, as in // @Requires \|ls\| <= 10000 And \(Forall i in \[0, \|ls\|\) : \|ls\[i\]\.Name\|`
	return len(js)
}

// EmbedsUnbounded bounds the outer field only; inner.Text is encoded too.
//
// @Requires |o.Name| <= 100
// @Ensures True
func EmbedsUnbounded(o Outer) (n int) {
	js, _ := json.Marshal(o) // want `what Marshal builds from o may be more than can be allocated; bound what it encodes, as in // @Requires \|o\.inner\.Text\| <= 1000000 And \|o\.Name\| <= 1000000 And \|o`
	return len(js)
}

// PointedUnguarded bounds the label only.
//
// @Requires |ns| <= 1000 And (Forall i in [0, |ns|) : |ns[i].Label| <= 1000)
// @Ensures True
func PointedUnguarded(ns []Node) (n int) {
	js, _ := json.Marshal(ns) // want `what Marshal builds from ns may be more than can be allocated; bound what it encodes, as in // @Requires \|ns\| <= 1000000 And \(Forall i in \[0, \|ns\|\) : \|ns\[i\]\.Lab`
	return len(js)
}

// Box is written by Evil's MarshalJSON.
type Box struct{ N int }

// Evil has a method that encoding/json would call, which writes memory.
type Evil struct{ B *Box }

func (e Evil) MarshalJSON() ([]byte, error) { e.B.N++; return []byte("1"), nil }

// Sneaky would keep b.N across a call that changes it.
//
// @Requires b != nil
// @Ensures b.N' = b.N
func Sneaky(b *Box) {
	_, _ = json.Marshal(Evil{B: b}) // want `cannot verify Sneaky: Marshal encodes Evil\{…\}, and Evil\{…\} is of type Evil, which has the method MarshalJSON, and encoding/json would call it; no method of a va`
}

// PtrEvil has the method on its pointer, which encoding/json calls on a
// value it reaches through a pointer or a slice.
type PtrEvil struct{ B *Box }

func (e *PtrEvil) MarshalText() ([]byte, error) { e.B.N++; return nil, nil }

// SneakyElements hands over values whose pointer method encoding/json
// would call.
//
// @Requires |es| <= 10
// @Ensures True
func SneakyElements(es []PtrEvil) {
	_, _ = json.Marshal(es) // want `cannot verify SneakyElements: Marshal encodes es, and es\[i\] is of type PtrEvil, which has the method MarshalText, and encoding/json would call it; no method of `
}

// Zeroable has IsZero, which encoding/json calls for a field with the
// option omitzero (F1 of the review).
type Zeroable struct{ B *Box }

func (z Zeroable) IsZero() bool { z.B.N++; return false }

// WithZero has such a field.
type WithZero struct {
	Z Zeroable `json:",omitzero"`
}

// OmitZero encodes it.
//
// @Ensures True
func OmitZero(w WithZero) {
	_, _ = json.Marshal(w) // want `cannot verify OmitZero: Marshal encodes w, and w\.Z has the option omitzero, and its type Zeroable has the method IsZero, which encoding/json would call; remove `
}

// WithAny holds an interface value.
type WithAny struct{ X any }

// Anys encodes it.
//
// @Ensures True
func Anys(x WithAny) {
	_, _ = json.Marshal(x) // want `cannot verify Anys: Marshal encodes x, and x\.X is an interface value of type any, whose dynamic type vego does not know; encode a value of a concrete type`
}

// Forwards hands on a value of type any.
//
// @Ensures True
func Forwards(v any) {
	_, _ = json.Marshal(v) // want `cannot verify Forwards: Marshal encodes v, and v is an interface value of type any, whose dynamic type vego does not know; encode a value of a concrete type`
}

// Chain holds itself.
type Chain struct {
	Next *Chain
}

// Recursive encodes it.
//
// @Ensures True
func Recursive(c Chain) {
	_, _ = json.Marshal(c) // want `cannot verify Recursive: Marshal encodes c, and c\.Next is of type Chain, which holds itself, so a value of it can be nested without end or refer to itself`
}

// BadName has a name the builds read differently (F7 of the review).
type BadName struct {
	A int `json:"a'b"`
}

// Named encodes it.
//
// @Ensures True
func Named(b BadName) {
	_, _ = json.Marshal(b) // want `cannot verify Named: Marshal encodes b, and b\.A: its json tag names it "a'b", which the builds of encoding/json read differently; use letters, digits, and the p`
}

// BadOption has an option the builds treat differently.
type BadOption struct {
	A int `json:",inline"`
}

// Optioned encodes it.
//
// @Ensures True
func Optioned(b BadOption) {
	_, _ = json.Marshal(b) // want `cannot verify Optioned: Marshal encodes b, and b\.A: its json tag has the option "inline", which the builds of encoding/json treat differently; only omitempty, o`
}

// Locked holds a mutex.
type Locked struct {
	Mu sync.Mutex
	N  int
}

// LockedPtr encodes what a pointer to one points to.
//
// @Requires l != nil
// @Ensures True
func LockedPtr(l *Locked) {
	_, _ = json.Marshal(l) // want `cannot verify LockedPtr: Marshal encodes l, and l\.Mu holds sync\.Mutex, which holds a state, which is not data that encoding/json can see`
}

// StructKeys has a map with keys json cannot encode.
type StructKeys struct {
	M map[bool]int
}

// Keys encodes it.
//
// @Ensures True
func Keys(s StructKeys) {
	_, _ = json.Marshal(s) // want `cannot verify Keys: Marshal encodes s, and s\.M is a map with keys of type bool; encoding/json encodes maps with keys that are strings or integers`
}

// Deferred loses what it would return.
//
// @Ensures True
func Deferred() {
	defer json.Marshal(1) // want `cannot verify Deferred: deferring a call of Marshal is not supported: what it returns would be lost, and what it encodes is checked where it is called`
}

// Encoder is a function type with a contract.
//
// @Ensures True
type Encoder func(v any) (b []byte, err error)

// AsValue makes json.Marshal a value.
//
// @Ensures True
func AsValue() {
	var f Encoder = json.Marshal // want `cannot verify AsValue: Marshal encodes what it is given as encoding/json does, and cannot be used as a value: what it is given is checked at each call written o`
	_, _ = f(1)
}

// ownMarshal is a function of the project with an entry that lists
// encodes, which only the shipped entries may (F13 of the review).
func ownMarshal(v any) ([]byte, error) {
	return json.Marshal(v)
}

// Own calls it.
//
// @Ensures True
func Own() {
	_, _ = ownMarshal(1) // want `the trusted contract of jsonenc\.ownMarshal \(trusted\.yaml:2189\) cannot be used: it lists encodes, which only the entries that come with vego can list; a function`
}
