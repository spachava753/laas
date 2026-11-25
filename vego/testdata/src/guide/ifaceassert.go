package guide

import (
	"fmt"
	"math"
)

// Asking what an interface value holds (S1 of F34).

// @Ensures holds(v, int) -> n = v.(int)
// @Ensures holds(v, string) -> n = |v.(string)|
// @Ensures v = nil -> n = 0
func Size(v any) (n int) {
	switch x := v.(type) {
	case int:
		return x
	case string:
		return len(x)
	}
	return 0
}

// @Ensures True
func MustSize(v any) (n int) {
	return v.(int) // want `vego: the type assertion v.\(int\) may panic: v may not hold an int; use the form v, ok := v.\(int\), or show that it holds one, as a contract does with holds\(x, T\)`
}

// Priced holds a Pricer, whose method has a contract.
type Priced struct{ P Pricer }

// @Ensures True
func PricedOf(v any) (ok bool) {
	p, ok := v.(Priced) // want `vego: cannot verify PricedOf: asserting an interface value to Priced is not supported: it holds in field P a value of type Pricer, whose method Price has a contract, and nothing claims that a value taken out of an interface value meets that contract: code that is not verified may have made it`
	_ = p
	return ok
}

// Assertions to interface types (S2 of F34).

// @Ensures ok And ~ok2
func PricerOrNot() (ok, ok2 bool) {
	var a any = Flat{}
	var b any = 7
	_, ok = a.(Pricer)
	_, ok2 = b.(Pricer)
	return ok, ok2
}

// @Ensures True
func Label(v any) (n int) {
	if s, ok := v.(fmt.Stringer); ok { // want `vego: cannot verify Label: using the value of v.\(fmt.Stringer\) is not supported: fmt.Stringer has the method String, which any does not have, so the value held may be one verified code made without checking it against fmt.Stringer, `
		_ = s
		return 1
	}
	return 0
}

// == on interface values (S3 of F34).

// @Requires holds(a, int) And holds(b, int)
// @Ensures r <-> a.(int) = b.(int)
func SameInt(a, b any) (r bool) {
	return a == b
}

// @Requires p != nil
// @Ensures a != b // want `vego: in Ensures annotation: a != b between two interface values that are not nil is not supported: = says that they are the same value, copied from one another, and not Go's ==, so its negation says nothing that code can observe; `
func TwoConversions(p *Link) (a, b any) {
	return p, p
}

// @Ensures a = b
func OneNaN() (a, b any, r bool) {
	a = any(math.NaN())
	b = a
	return a, b, a == b
}

// @Ensures r
func OneNaNEqual() (a, b any, r bool) {
	a = any(math.NaN())
	b = a
	return a, b, a == b // want `vego: postcondition may not hold: r`
}

// @Ensures ~r
func OneNaNUnequal() (a, b any, r bool) {
	a = any(math.NaN())
	b = a
	return a, b, a == b // want `vego: postcondition may not hold: ~r`
}
