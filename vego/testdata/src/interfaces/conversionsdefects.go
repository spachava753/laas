package interfaces

import (
	"errors"
	"fmt"
)

// Greedy charges more than Pricer allows.
type Greedy struct{}

// @Ensures ok
func (Greedy) Price(sku string, qty int) (cents int, ok bool) {
	return 2000000, true
}

// @Ensures True
func FromGreedy() (p Pricer) {
	return Greedy{} // want `postcondition may not hold: ok -> 0 <= cents <= 1000000, in Greedy.Price used as a method of Pricer at conversionsdefects.go:\d+:\d+`
}

// Picky asks more of its callers than Pricer gives.
type Picky struct{}

// @Requires qty > 5
// @Ensures cents = 0
func (Picky) Price(sku string, qty int) (cents int, ok bool) {
	return 0, false
}

// @Ensures True
func FromPicky() (p Pricer) {
	return Picky{} // want `precondition of Price may not hold: qty > 5, in Picky.Price used as a method of Pricer`
}

// Deref has a value receiver, so a nil pointer in the interface panics when
// it is called.
type Deref struct{ N int }

// @Requires 0 <= qty <= 1000
// @Ensures ok -> 0 <= cents <= 1000000
func (d Deref) Price(sku string, qty int) (cents int, ok bool) {
	return 0, false
}

// @Ensures True
func FromNilDeref() (p Pricer) {
	var d *Deref
	return d // want `Deref.Price has a value receiver, and the pointer that the interface value holds may be nil, in Deref.Price used as a method of Pricer`
}

// Counting writes behind its receiver, which Pricer does not allow.
type Counting struct{ calls int }

// @Requires c != nil And 0 <= qty <= 1000 And c.calls < 1000
// @Modifies c
// @Ensures ok -> 0 <= cents <= 1000000
func (c *Counting) Price(sku string, qty int) (cents int, ok bool) {
	c.calls++
	return 0, false
}

// @Requires c != nil
// @Ensures True
func FromCounting(c *Counting) (p Pricer) {
	return c // want `precondition of Price may not hold: c.calls < 1000, in \(\*Counting\).Price used as a method of Pricer` `Price may modify c, which Pricer.Price may not modify; list it in a // @Modifies clause, in \(\*Counting\).Price used as a method of Pricer`
}

// Bounded has an invariant, which a conversion cannot show of memory it
// knows nothing about.
//
// @Invariant 0 <= Rate <= 1000
type Bounded struct{ Rate int }

// @Requires b != nil And 0 <= qty <= 1000
// @Ensures ok -> 0 <= cents <= 1000000
func (b *Bounded) Price(sku string, qty int) (cents int, ok bool) {
	return b.Rate * qty, true
}

// @Requires b != nil
// @Ensures True
func FromBounded(b *Bounded) (p Pricer) {
	return b // want `invariant of Bounded may not hold for what is passed to Price as b: 0 <= Rate <= 1000, in \(\*Bounded\).Price used as a method of Pricer`
}

type Unannotated struct{}

func (Unannotated) Price(sku string, qty int) (cents int, ok bool) { return 0, false }

// @Ensures True
func FromUnannotated() (p Pricer) {
	return Unannotated{} // want `cannot verify FromUnannotated: it uses Price as a method of Pricer, and Price has no contract`
}

// @Ensures True
func ToPlain(f Flat) (p Plain) {
	return nil
}

type Getter int

func (Getter) Get() (n int) { return 0 }

// @Ensures True
func ToUncontracted(g Getter) (p Plain) {
	return g // want `cannot verify ToUncontracted: converting a interfaces.Getter to interfaces.Plain is not supported: its method Plain.Get has no contract`
}

// Delegating gets Price from the Pricer it embeds.
type Delegating struct {
	Pricer
}

// @Ensures True
func FromDelegating(d Delegating) (p Pricer) {
	return d // want `cannot verify FromDelegating: Delegating gets Price from an embedded field that holds an interface value`
}

// Caller calls through an interface value in its method.
type Caller struct{ inner Pricer }

// @Requires c.inner != nil And 0 <= qty <= 1000
// @Ensures ok -> 0 <= cents <= 1000000
func (c Caller) Price(sku string, qty int) (cents int, ok bool) {
	return c.inner.Price(sku, qty)
}

// @Ensures True
func FromCaller(c Caller) (p Pricer) {
	return c // want `cannot verify FromCaller: Price may call through a function value or an interface value, and code that an interface value runs cannot do that yet`
}

// PriceFunc is a function type with a method, which calls the function.
//
// @Requires 0 <= qty <= 1000
// @Ensures ok -> 0 <= cents <= 1000000
type PriceFunc func(sku string, qty int) (cents int, ok bool)

// @Requires f != nil And 0 <= qty <= 1000
// @Ensures ok -> 0 <= cents <= 1000000
func (f PriceFunc) Price(sku string, qty int) (cents int, ok bool) {
	return f(sku, qty)
}

// @Ensures True
func FromFunc(f PriceFunc) (p Pricer) {
	return f // want `cannot verify FromFunc: Price may call through a function value or an interface value`
}

// Loop converts a struct whose method calls back into it.
type Looping struct{}

// @Requires 0 <= qty <= 1000
// @Ensures ok -> 0 <= cents <= 1000000
func (Looping) Price(sku string, qty int) (cents int, ok bool) {
	return LoopBack(qty) // want `recursive call needs a // @Variant annotation in the doc comment of Price to prove termination`
}

// @Requires 0 <= qty <= 1000
// @Ensures ok -> 0 <= cents <= 1000000
func LoopBack(qty int) (cents int, ok bool) {
	var p Pricer = Looping{} // want `cannot verify LoopBack: Price may call through a function value or an interface value`
	return p.Price("a", qty)
}

// @Requires p != nil
// @Ensures True
func SwitchOnConcrete(f Flat, p Pricer) (n int) {
	switch f {
	case p: // want `cannot verify SwitchOnConcrete: comparing interface values is not supported yet`
		return 1
	}
	return 0
}

type codeError int

func (codeError) Error() string { return "code" }

// @Ensures True
func SwitchOnErrorCase(err error) (n int) {
	switch err {
	case codeError(1): // want `cannot verify SwitchOnErrorCase: comparing an error with a value of type interfaces.codeError is not supported`
		return 1
	}
	return 0
}

// @Ensures True
func ComparedWithConcrete(p Pricer, f Flat) (same bool) {
	return p == f // want `cannot verify ComparedWithConcrete: comparing interface values is not supported yet`
}

// @Ensures True
func ErrorComparedWithConcrete(err error) (same bool) {
	return err == codeError(2) // want `cannot verify ErrorComparedWithConcrete: comparing an error with a value of type interfaces.codeError is not supported`
}

func two() (f Flat, t *Table) { return 0, nil }

// @Ensures True
func FromTuple() (p Pricer, q Pricer) {
	return two() // want `cannot verify FromTuple: `
}

// @Ensures True
func AssignedFromTuple() (p Pricer) {
	var q Pricer
	p, q = two() // want `cannot verify AssignedFromTuple: `
	_ = q
	return p
}

// @Ensures True
func RangeAssigned(fs []Flat) (p Pricer) {
	for _, p = range fs { // want `cannot verify RangeAssigned: `
	}
	return p
}

// @Requires m != nil
// @Ensures True
func CommaOkConverted(m map[string]Flat) (p Pricer) {
	var ok bool
	p, ok = m["a"] // want `cannot verify CommaOkConverted: `
	_ = ok
	return p
}

func pricesAll(p Pricer) (n int) { return 0 }

// @Ensures True
func ToTrusted(f Flat) (n int) {
	return pricesAll(f) // want `cannot verify ToTrusted: f is passed to pricesAll, which is trusted`
}

// @Ensures True
func ToAnyTrusted(t *Table) (n int) {
	return keepsAny(t)
}

func keepsAny(a any) (n int) { return 0 }

// @Ensures err = nil <-> n <= 0
func Formats(n int, s string) (err error) {
	if n <= 0 {
		return nil
	}
	return fmt.Errorf("bad %d %s %w", n, s, errors.New("inner"))
}
