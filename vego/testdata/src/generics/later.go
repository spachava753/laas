package generics

import (
	"sync/atomic"

	"genericslib"
)

// ApplyPos relies on what Apply says of the first element at E = int.
//
// @Requires |xs| > 0 And xs[0] = 5
// @Ensures r
func ApplyPos(xs []int) (r bool) {
	return genericslib.Apply(xs, func(e int) bool { return e > 0 })
}

// ApplyPosWrong expects the opposite.
//
// @Requires |xs| > 0 And xs[0] = 5
// @Ensures ~r
func ApplyPosWrong(xs []int) (r bool) {
	return genericslib.Apply(xs, func(e int) bool { return e > 0 }) // want `postcondition may not hold: ~r`
}

// ApplyString applies at E = string, which an application cannot take.
//
// @Ensures True
func ApplyString(xs []string) (r bool) {
	return genericslib.Apply(xs, func(e string) bool { return len(e) > 0 }) // want `cannot be used with S = \[\]string, E = string: in its ensures "\(\|s\| > 0 And f\(s\[0\]\)\) -> result": f takes one integer; write a loop instead` `cannot be used with S = \[\]string, E = string: its ensures applies f, whose type func\(string\) bool does not have one integer parameter and one integer or boolean result, which is all that can be applied yet; write a loop instead`
}

// HandsGeneric hands over a generic function written with its type
// argument.
//
// @Ensures True
func HandsGeneric(xs []int) (r int) {
	return genericslib.FindFunc(xs, genericslib.IsPos[int]) // want `generic functions cannot be handed over yet`
}

// HandsGenericInferred hands it over with its type argument inferred.
//
// @Ensures True
func HandsGenericInferred(xs []int) (r int) {
	return genericslib.FindFunc(xs, genericslib.IsPos) // want `generic functions cannot be handed over yet`
}

// Picker picks a value.
//
// @Ensures True
type Picker func(x int) (r int)

// MakesGeneric makes a value of a generic function written with its type
// argument.
//
// @Ensures True
func MakesGeneric() (r int) {
	var p Picker = genericslib.Same[int] // want `generic functions cannot be used as a value yet`
	return p(1)
}

// MakesGenericInferred makes it with its type argument inferred.
//
// @Ensures True
func MakesGenericInferred() (r int) {
	var p Picker = genericslib.Same // want `generic functions cannot be used as a value yet`
	return p(1)
}

// OldOf calls a function whose entry has a defect at every type argument.
//
// @Ensures True
func OldOf(n int) (r bool) {
	return genericslib.Old(n, 1) // want `cannot be used with E = int: its requires "old\(n\) > 0" uses old, which has no meaning there: a requires is read in the state of the call; the entry has this defect at every type argument, so fix the entry in trusted.yaml`
}

// GetOf calls a method of a generic type.
//
// @Requires b != nil
// @Ensures True
func GetOf(b *genericslib.Box[int]) (r int) {
	return b.Get() // want `calls of methods of generic types are not supported yet`
}

// LoadOf calls a method of a generic type of the standard library.
//
// @Requires p != nil
// @Ensures True
func LoadOf(p *atomic.Pointer[Point]) (r bool) {
	return p.Load() != nil // want `calls of methods of generic types are not supported yet`
}

// SetIt calls a function whose modifies names a field of a value of a type
// parameter.
//
// @Requires p != nil
// @Modifies p
// @Ensures True
func SetIt(p *Point) {
	genericslib.Set(p) // want `p.X names a field of a value of type E, a type parameter`
}

// HoldsIt calls a function whose ensures says fresh of a field of a value
// of a type parameter.
//
// @Ensures True
func HoldsIt(b struct{ P *Point }) (r bool) {
	return genericslib.Holds(b) // want `x.P names a field of a value of type E, a type parameter`
}

// TouchCounters hands values whose pointer type has a method, which
// Touch calls and its entry does not claim it does not.
//
// @Requires |cs| > 0 And cs[0].n = 0
// @Ensures r = 0
func TouchCounters(cs []Counter) (r int) {
	genericslib.Touch(cs) // want `genericslib.Touch is called with S = \[\]Counter, and genericslib.Touch may run the method func \(\*Counter\).Inc\(\)`
	return cs[0].n
}

// OrderTargetPure calls Same at int in the target of an assignment beside
// an append that may write in place, which its instantiation's signature,
// free of memory, allows.
//
// @Requires |u| > 3 And 0 <= i And i < 3
// @Modifies t, u
// @Ensures True
func OrderTargetPure(u [][]int, t []int, i int) {
	u[genericslib.Same(i)] = append(t[:0], 5)
}

// OrderTarget calls Find there, whose signature reads memory.
//
// @Requires |u| > |t| + 1
// @Modifies t, u
// @Ensures True
func OrderTarget(u [][]int, t []int) {
	u[genericslib.Find(t, 0)+1] = append(t[:0], 5) // want `Find is called in the target of this assignment, and Go may call it before or after append writes into the array of t\[:0\]`
}

// L is an integer type with a String method that calls back.
type L int

// String calls LoopL, which calls Show, which calls String.
//
// @Ensures True
func (l L) String() (s string) { return LoopL(l) } // want `this call may not end: L.String calls LoopL`

// LoopL hands an L to Show, after ShowInt hands it an int, which has the
// same underlying type and no method.
//
// @Ensures True
func LoopL(l L) (s string) {
	return genericslib.Show(l) // want `genericslib.Show is called with T = L, and genericslib.Show may run the method func \(L\).String\(\) \(s string\)`
}
