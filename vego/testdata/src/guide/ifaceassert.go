package guide

import "fmt"

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
