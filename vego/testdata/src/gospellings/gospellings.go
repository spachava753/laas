// Package gospellings writes formulas with the operators that Go spells
// otherwise. The formula language has one spelling for each: And, Or, ~,
// =, and Z. Each Go spelling is refused with the spelling to use.
package gospellings

import "sort"

// Between is written in the formula language.
//
// @Requires 0 <= lo And lo <= hi Or hi < 0
// @Ensures r <-> ~(x < lo) And x < hi
// @Ensures r = True -> lo <= x
func Between(x, lo, hi int) (r bool) {
	return x >= lo && x < hi
}

// @Requires 0 <= lo && lo <= hi // want `vego: syntax error in Requires annotation: && is not a spelling of the formula language; write And`
// @Ensures True
func WithAnd(lo, hi int) (r bool) {
	return lo <= hi
}

// @Ensures r || True // want `vego: syntax error in Ensures annotation: \|\| is not a spelling of the formula language; write Or`
func WithOr(x int) (r bool) {
	return x > 0
}

// @Ensures r <-> !(x <= 0) // want `vego: syntax error in Ensures annotation: ! is not a spelling of the formula language; write ~`
func WithNot(x int) (r bool) {
	return x > 0
}

// @Ensures r == x // want `vego: syntax error in Ensures annotation: == is not a spelling of the formula language; write =`
func WithEquals(x int) (r int) {
	return x
}

// @Ensures Forall k in ℤ : k = k // want `vego: syntax error in Ensures annotation: ℤ is not a spelling of the formula language; write Z`
func WithBlackboardZ(x int) (r int) {
	return x
}

// ℤ is a Go identifier, which a formula may name outside a quantifier's
// domain.
//
// @Ensures r = ℤ
func NamedBlackboardZ(ℤ int) (r int) {
	return ℤ
}

// @Ensures r = x
func InBody(x int) (r int) {
	r = x
	// @Assert Forall k in [0, 3) : k >= 0 && r = x // want `vego: syntax error in Assert annotation: && is not a spelling of the formula language; write And`
	return r
}

// @Ensures c != '!' -> r = "a && b || !c == d"
func InStrings(c int) (r string) {
	if c == '!' {
		return ""
	}
	return "a && b || !c == d"
}

func positive(x int) bool { return x > 0 }

// UsesEntry calls a function whose trusted contract writes &&.
//
// @Ensures True
func UsesEntry(x int) (r bool) {
	return positive(x) // want `the trusted contract of gospellings.positive \(vego-trusted.yaml:\d+\) cannot be used: vego-trusted.yaml:\d+: syntax error in ensures of gospellings.positive: == is not a spelling of the formula language; write =` `the trusted contract of gospellings.positive \(vego-trusted.yaml:\d+\) cannot be used: vego-trusted.yaml:17: syntax error in requires of f\(i\) in calls`
}

// UsesCalls hands a function to sort.Search, whose entry in this module's
// trust file writes && in what holds when Search calls it.
//
// @Requires n >= 0
// @Ensures True
func UsesCalls(n int) (r int) {
	return sort.Search(n, func(i int) bool { return i > 2 }) // want `the trusted contract of sort.Search \(vego-trusted.yaml:\d+\) cannot be used: vego-trusted.yaml:8: syntax error in ensures`  `the trusted contract of sort.Search \(vego-trusted.yaml:\d+\) cannot be used: vego-trusted.yaml:17: syntax error in requires of f\(i\) in calls of sort.Search: && is not a spelling of the formula language; write And`
}
