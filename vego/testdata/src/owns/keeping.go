package owns

import (
	"bytes"
	"slices"
	"sort"
)

// The rules that keep what an owner owns referred to only through it
// (F27, step 3a).

// Keeper holds what it is given, without owning it.
type Keeper struct {
	kept []int
	ptr  *Config
}

// StoreElsewhere keeps what s owns in another struct (R2).
//
// @Requires s != nil And k != nil
// @Modifies k
// @Ensures True
func StoreElsewhere(s *Stack, k *Keeper) {
	k.kept = s.items // want `vego: s.items is memory that s owns, stored into memory at keeping.go:[0-9:]+; it may be read and written here, but not kept elsewhere: copy it, or do not declare the field owned`
}

// Alias keeps the struct a server owns in another (F21 of the review of
// step 2).
//
// @Requires s != nil And k != nil
// @Modifies k
// @Ensures True
func Alias(s *Server, k *Keeper) {
	k.ptr = s.cfg // want `vego: s.cfg is memory that s owns, stored into memory at keeping.go:[0-9:]+`
}

// newKept makes a Config and keeps it in k too.
//
// @Requires k != nil
// @Modifies k
// @Ensures fresh(c)
func newKept(k *Keeper) (c *Config) {
	c = &Config{}
	k.ptr = c
	return c
}

// FromKeeping stores what newKept returns, which it also kept in k (F21).
//
// @Requires s != nil And k != nil
// @Modifies s, k
// @Ensures True
func FromKeeping(s *Server, k *Keeper) {
	s.cfg = newKept(k) // want `vego: what is stored into s.cfg is new memory that something else may refer to: it comes from the call of newKept`
}

// Constructed stores a store it made, held in a variable first.
//
// @Ensures r != nil
func Constructed() (r *Server) {
	cfg := &Config{port: 80}
	return &Server{cfg: cfg}
}

// Filled fills a map before it is owned.
//
// @Requires c != nil
// @Modifies c
// @Ensures True
func Filled(c *Cache) {
	m := make(map[string]int)
	fill(m)
	c.m = m
}

// fill writes a map it is handed and keeps nothing of it.
//
// @Requires m != nil
// @Modifies m
// @Ensures True
func fill(m map[string]int) {
	m["a"] = 1
}

// Sorted sorts what s owns in place, with a function that keeps nothing.
//
// @Requires s != nil
// @Modifies s
// @Ensures True
func Sorted(s *Stack) {
	sort.Ints(s.items)
	slices.Reverse(s.items)
}

// Items returns what s owns, as its contract says.
//
// @Requires s != nil
// @Ensures within(r, s) And |r| = |s.items|
func (s *Stack) Items() (r []int) {
	return s.items
}

// ItemsUnsaid returns what s owns without saying so (R5).
//
// @Requires s != nil
// @Ensures |r| = |s.items|
func (s *Stack) ItemsUnsaid() (r []int) {
	return s.items // want `vego: ItemsUnsaid returns memory that s owns; say so with within\(r, s\) in an Ensures, or return a copy`
}

// Built returns what a stack it made owns, which nothing else refers to
// (F9 (b)).
//
// @Ensures fresh(r) And |r| = 2
func Built() (r []int) {
	s := &Stack{}
	s.Push(1)
	s.Push(2)
	return s.items
}

// Leak returns what a stack owns that it has also handed to a server
// (F12).
//
// @Requires p != nil
// @Modifies p
// @Ensures True
func Leak(p *Pair) (r []int) {
	s := &Stack{}
	s.Push(1)
	p.p = s
	return s.items // want `vego: Leak returns memory that p owns; say so with within\(r, p\) in an Ensures, or return a copy`
}

// Both returns what a stack owns beside the stack (F12).
//
// @Ensures True
func Both() (r []int, s *Stack) {
	s = &Stack{}
	s.Push(1)
	return s.items, s // want `vego: Both returns memory that the Stack made at keeping.go:[0-9:]+ owns, which something else may refer to`
}

// two returns two results that are one slice.
//
// @Ensures fresh(a) And fresh(b) And |a| = 1 And |b| = 1
func two() (a, b []int) {
	x := make([]int, 1)
	return x, x
}

// Shares stores both results of one call into two stacks (F20).
//
// @Ensures True
func Shares() {
	s := &Stack{}
	t := &Stack{}
	s.items, t.items = two() // want `vego: what is stored into t.items is new memory that something else may refer to: it is memory that the Stack made at keeping.go:[0-9:]+ owns`
}

// Doc owns its bytes.
//
// @Owns buf
type Doc struct {
	buf []byte
}

// Bytes holds bytes it does not own.
type Bytes struct {
	data []byte
}

// Trimmed keeps what TrimFunc returns of what d owns, which lies within it
// (F14 of the review of step 1).
//
// @Requires d != nil And h != nil And |d.buf| <= 1000
// @Modifies h
// @Ensures True
func TrimmedInto(d *Doc, h *Bytes) {
	h.data = bytes.TrimFunc(d.buf, func(c rune) bool { return c == ' ' }) // want `vego: bytes.TrimFunc\(d.buf, .*\) is memory that d owns, stored into memory`
}

// Fields keeps a field FieldsFunc cut from what d owns (F15).
//
// @Requires d != nil And h != nil And |d.buf| <= 1000
// @Modifies h
// @Ensures True
func Fields(d *Doc, h *Bytes) {
	parts := bytes.FieldsFunc(d.buf, func(c rune) bool { return c == ' ' }) // want `vego: what is handed to bytes.FieldsFunc as s is memory that d owns, and what bytes.FieldsFunc returns may hold parts of it that its entry does not place`
	if len(parts) > 0 {
		h.data = parts[0]
	}
}

// Sink is an interface of the project whose method may keep what it is
// handed.
type Sink interface {
	// @Requires True
	// @Ensures True
	Put(p []int)
}

// ToSink hands what s owns to a method of an interface declared in source.
//
// @Requires s != nil And k != nil
// @Ensures True
func ToSink(s *Stack, k Sink) {
	k.Put(s.items) // want `vego: what is handed to k.Put as p is memory that s owns, and a method of an interface declared in source may keep what it is handed`
}

// Linked points a struct at itself through a field it does not own.
type Linked struct {
	self *Linked
}

// Link keeps its receiver in its own field.
//
// @Requires t != nil
// @Modifies t
// @Ensures True
func (t *Linked) Link() {
	t.self = t
}

// Chain owns a Linked.
//
// @Owns l
type Chain struct {
	l *Linked
}

// LinkOwned hands what c owns to a method that keeps it (F5).
//
// @Requires c != nil And c.l != nil
// @Modifies c
// @Ensures True
func LinkOwned(c *Chain) {
	c.l.Link() // want `vego: what is handed to c.l.Link as t is memory that c owns, and it may keep what it is handed`
}

// Captured captures what s owns in a literal it returns.
//
// @Requires s != nil
// @Ensures True
func Captured(s *Stack) (f func() int) {
	xs := s.items
	return func() int { return len(xs) } // want `vego: the function literal at keeping.go:[0-9:]+ captures xs, which is memory that s owns` `vego: cannot verify Captured: the function literal is used as a value`
}

// InPlace reads what s owns in a literal called where it stands (F9 (c)).
//
// @Requires s != nil
// @Ensures True
func InPlace(s *Stack) (n int) {
	xs := s.items
	n = func() int { return len(xs) }()
	return n
}

// Ptrs owns a slice of pointers, whose elements it does not own.
//
// @Owns ptrs
type Ptrs struct {
	ptrs []*Config
}

// remember keeps an element of what it is handed.
//
// @Requires k != nil And |ps| > 0
// @Modifies k
// @Ensures True
func remember(k *Keeper, ps []*Config) {
	k.ptr = ps[0]
}

// Remembered hands what p owns to a function that keeps an element of it,
// not the slice (F13).
//
// @Requires p != nil And k != nil And |p.ptrs| > 0
// @Modifies k
// @Ensures True
func Remembered(p *Ptrs, k *Keeper) {
	remember(k, p.ptrs)
}

// Refill makes a new buffer for each stack it made, in a loop: each
// iteration's make is new (F7 of the design review).
//
// @Ensures True
func Refill() {
	cs := []*Stack{{}, {}}
	// @Invariant 0 <= i <= 2
	for i := range cs {
		b := make([]int, 4)
		cs[i].items = b
	}
}

// RefillKept keeps the buffer of the first iteration, which the first
// stack still owns, and gives it to another.
//
// @Requires t != nil
// @Modifies t
// @Ensures True
func RefillKept(t *Stack) {
	cs := []*Stack{{}, {}}
	var keep []int
	// @Invariant 0 <= i <= 2 And fresh(keep)
	for i := range cs {
		b := make([]int, 4)
		cs[i].items = b
		if i == 0 {
			keep = b
		}
	}
	t.items = keep // want `vego: what is stored into t.items is new memory that something else may refer to: it is memory that cs\[i\] owns`
}

func peek(b []byte) []byte { return b }

// Peeked keeps what a trusted function returns that its entry does not
// place, which may be what it is handed (F14).
//
// @Requires d != nil And h != nil
// @Modifies h
// @Ensures True
func Peeked(d *Doc, h *Bytes) {
	h.data = peek(d.buf) // want `vego: peek\(d.buf\) is memory that d owns, stored into memory`
}

// Configs owns an array of structs.
//
// @Owns cs
type Configs struct {
	cs []Config
}

// AddrOfPart keeps the address of an element of what c owns.
//
// @Requires c != nil And k != nil And |c.cs| > 0
// @Modifies k
// @Ensures True
func AddrOfPart(c *Configs, k *Keeper) {
	k.ptr = &c.cs[0] // want `vego: &c.cs\[0\] is memory that c owns, stored into memory`
}

// RefillPrev gives t the buffer of the previous iteration after the site
// has made the next one: what the variable holds is the earlier execution
// of the site, which the first stack owns (F7 of the review of the design).
//
// @Requires t != nil
// @Modifies t
// @Ensures True
func RefillPrev(t *Stack) {
	cs := []*Stack{{}, {}}
	var prev []int
	// @Invariant 0 <= i <= 2 And fresh(prev)
	for i := range cs {
		b := make([]int, 4)
		if i == 1 {
			t.items = prev // want `vego: what is stored into t.items is new memory that something else may refer to: it is memory that cs\[i\] owns`
		}
		cs[i].items = b
		prev = b
	}
}

// AliasLiteral puts the struct a server owns into a literal it returns
// (F29 of the review of step 3a).
//
// @Requires s != nil
// @Ensures k != nil
func AliasLiteral(s *Server) (k *Keeper) {
	return &Keeper{ptr: s.cfg} // want `vego: s.cfg is memory that s owns, stored into what the literal at keeping.go:[0-9:]+ makes`
}

// AliasValue puts it into a struct value it returns.
//
// @Requires s != nil
// @Ensures True
func AliasValue(s *Server) (k Keeper) {
	return Keeper{ptr: s.cfg} // want `vego: AliasValue returns memory that s owns, held in a Keeper, which no contract can place within s; return a copy`
}

// AliasHeld puts it into a struct value and stores the value.
//
// @Requires s != nil And b != nil
// @Modifies b
// @Ensures True
func AliasHeld(s *Server, b *Box2) {
	k := Keeper{ptr: s.cfg}
	b.k = k // want `vego: k is memory that s owns, stored into memory at keeping.go:[0-9:]+`
}

// Box2 holds a Keeper by value.
type Box2 struct {
	k Keeper
}

// AliasItems puts what a stack owns into a new Keeper it returns.
//
// @Requires s != nil
// @Ensures k != nil
func AliasItems(s *Stack) (k *Keeper) {
	k = &Keeper{kept: s.items} // want `vego: s.items is memory that s owns, stored into what the literal at keeping.go:[0-9:]+ makes`
	return k
}

// DeferredResult leaves what s owns in its result from a deferred
// literal (F30).
//
// @Requires s != nil
// @Ensures True
func DeferredResult(s *Stack) (r []int) {
	defer func() { r = s.items }()
	return nil // want `vego: DeferredResult returns memory that s owns; say so with within\(r, s\) in an Ensures, or return a copy`
}

// AliasDeferred does the same with the struct a server owns.
//
// @Requires s != nil
// @Ensures True
func AliasDeferred(s *Server) (p *Config) {
	defer func() { p = s.cfg }()
	return nil // want `vego: AliasDeferred returns memory that s owns; say so with within\(p, s\) in an Ensures, or return a copy`
}

// Owner owns a byte slice.
//
// @Owns buf
type Owner struct {
	buf []byte
}

// PrevKept keeps the previous iteration's buffer, which the previous
// stack owns, past the next execution of the site, and gives it to
// another owner after the loop (F31, the reviewer's program).
//
// @Ensures True
func PrevKept() {
	cs := []*Owner{{}, {}, {}}
	t := &Owner{}
	var keep, prev []byte
	// @Invariant 0 <= i <= |cs| And fresh(keep) And fresh(prev)
	// @Variant |cs| - i
	for i := 0; i < len(cs); i++ {
		keep = prev
		b := make([]byte, 4)
		cs[i].buf = b
		prev = b
	}
	t.buf = keep // want `vego: what is stored into t.buf is new memory that something else may refer to: it is memory that cs\[i\] owns`
}

// Elem is an element of a list held by value.
type Elem struct {
	v int
}

// Elems owns an array of nodes.
//
// @Owns items
type Elems struct {
	items []Elem
}

// Touch writes the list's first node, assuming n is not part of it.
//
// @Requires n != nil And l != nil And |l.items| > 0 And l.items[0].v < 100
// @Modifies l
// @Ensures n.v' = n.v
func (n *Elem) Touch(l *Elems) {
	l.items[0].v = l.items[0].v + 1
}

// TouchFirst calls Touch on the list's own first node, whose address Go
// takes for the pointer receiver (F35 of the review of step 3b).
//
// @Requires l != nil And |l.items| > 0 And l.items[0].v < 100
// @Modifies l
// @Ensures True
func TouchFirst(l *Elems) {
	l.items[0].Touch(l) // want `vego: l.items\[0\] is memory that l owns, and Touch is handed what reaches a Elems, which can own it`
}

// NodeHolder keeps a node.
type NodeHolder struct {
	n *Elem
}

// Keep keeps its receiver.
//
// @Requires n != nil And h != nil
// @Modifies h
// @Ensures True
func (n *Elem) Keep(h *NodeHolder) {
	h.n = n
}

// KeepFirst hands the address of the list's first node to Keep.
//
// @Requires l != nil And h != nil And |l.items| > 0
// @Modifies h
// @Ensures True
func KeepFirst(l *Elems, h *NodeHolder) {
	l.items[0].Keep(h) // want `vego: what is handed to l.items\[0\].Keep as n is memory that l owns, and it may keep what it is handed`
}

// Funcs holds a function.
type Funcs struct {
	f func(h *NodeHolder)
}

// KeepValue takes a method value of the list's first node.
//
// @Requires l != nil And b != nil And |l.items| > 0
// @Modifies b
// @Ensures True
func KeepValue(l *Elems, b *Funcs) {
	b.f = l.items[0].Keep // want `vego: the method value l.items\[0\].Keep holds memory that an owner owns` `vego: cannot verify KeepValue: l.items\[0\].Keep is used as a value`
}
