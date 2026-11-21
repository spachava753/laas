// Package generics calls generic functions of another package under the
// contracts the trust file of the corpus gives them, at several type
// arguments, and the calls that are refused.
package generics

import (
	"sync"

	"genericslib"
)

// Point is a struct, which a formula cannot compare as a whole.
type Point struct{ X, Y int }

// IDs is a named slice type.
type IDs []int

// Ints is an alias, which is the same type as []int.
type Ints = []int

// ShowInt calls Show at int, before LoopL calls it at L, whose underlying
// type is int (later.go).
//
// @Ensures True
func ShowInt() (s string) { return genericslib.Show(1) }

// IndexOf finds an integer.
//
// @Ensures r = -1 Or xs[r] = 3
func IndexOf(xs []int) (r int) {
	return genericslib.Find(xs, 3)
}

// IndexExplicit names the type arguments.
//
// @Ensures r = -1 Or xs[r] = 3
func IndexExplicit(xs []int) (r int) {
	return genericslib.Find[[]int, int](xs, 3)
}

// IndexNamed finds an integer in a named slice type, inferred from an
// untyped constant.
//
// @Ensures r = -1 Or ids[r] = 7
func IndexNamed(ids IDs) (r int) {
	return genericslib.Find(ids, 7)
}

// IndexAlias finds an integer in a slice of an alias type, the same
// instantiation as []int.
//
// @Ensures r = -1 Or xs[r] = 3
func IndexAlias(xs Ints) (r int) {
	return genericslib.Find(xs, 3)
}

// IndexString finds a string.
//
// @Ensures r >= 0 -> names[r] = "a"
func IndexString(names []string) (r int) {
	return genericslib.Find(names, "a")
}

// IndexWrong says more than the contract gives.
//
// @Ensures r >= 0
func IndexWrong(xs []int) (r int) {
	return genericslib.Find(xs, 3) // want `postcondition may not hold: r >= 0`
}

// IndexPoint finds a struct, which the clause s[result] = v cannot
// compare.
//
// @Ensures True
func IndexPoint(ps []Point, p Point) (r int) {
	return genericslib.Find(ps, p) // want `the trusted contract of genericslib.Find \(trusted.yaml:\d+\) cannot be used with S = \[\]Point, E = Point: in its ensures "result >= 0 -> s\[result\] = v": a value of type E, which is Point here, is a struct, and a formula cannot compare a struct or use it as a whole; call genericslib.FindFunc instead, with a function literal that compares what you need of the elements, or write a loop`
}

// IndexFunc finds a struct with a literal that compares a field.
//
// @Ensures r >= 0 -> r < |ps|
func IndexFunc(ps []Point, x int) (r int) {
	return genericslib.FindFunc(ps, func(p Point) bool { return p.X == x })
}

// IndexFuncString hands over a literal of a string.
//
// @Ensures r < |names|
func IndexFuncString(names []string) (r int) {
	return genericslib.FindFunc(names, func(s string) bool { return len(s) > 2 && s[2] == 'x' })
}

// IndexFuncUnsafe reads past the end of what its literal is given.
//
// @Ensures True
func IndexFuncUnsafe(names []string) (r int) {
	return genericslib.FindFunc(names, func(s string) bool { return s[2] == 'x' }) // want `index may be out of range, in the function literal run by genericslib.FindFunc at generics.go:\d+:\d+`
}

// TopInt orders integers.
//
// @Requires |xs| > 0
// @Ensures r >= xs[0]
func TopInt(xs []int) (r int) {
	return genericslib.Top(xs)
}

// TopString orders strings, which a formula cannot.
//
// @Requires |names| > 0
// @Ensures True
func TopString(names []string) (r string) {
	return genericslib.Top(names) // want `the trusted contract of genericslib.Top \(trusted.yaml:\d+\) cannot be used with S = \[\]string, E = string: in its ensures "Forall i in \[0, \|s\|\) : s\[i\] <= result": operator <= cannot be applied to string or slice values; a formula has no order of them; write a loop instead`
}

// TopEmpty does not meet the requires.
//
// @Ensures True
func TopEmpty(xs []int) (r int) {
	return genericslib.Top(xs) // want `precondition of Top may not hold: \|s\| > 0`
}

// FilterKeeps hands over a literal that reads the slice being filtered.
//
// @Modifies xs
// @Ensures |r| <= |xs|
func FilterKeeps(xs []int) (r []int) {
	return genericslib.Filter(xs, func(e int) bool { return e > 0 })
}

// FilterWrites hands over a literal that writes the slice that Filter
// writes.
//
// @Requires |xs| > 0
// @Modifies xs
// @Ensures True
func FilterWrites(xs []int) (r []int) {
	return genericslib.Filter(xs, func(e int) bool {
		xs[0] = e // want `xs\[0\] is assigned, which genericslib.Filter may write itself while it runs the function it is handed`
		return true
	})
}

// ResetLoop resets a slice in a loop, and keeps what it knows of another.
//
// @Requires |a| = 3 And |b| > 0 And b[0] = 5
// @Modifies a
// @Ensures b[0] = 5
func ResetLoop(a, b []int) {
	// @Invariant 0 <= i And i <= 3 And b[0] = 5
	// @Variant 3 - i
	for i := 0; i < 3; i++ {
		genericslib.Reset(a)
	}
}

// ResetLoopWrong claims the loop keeps what Reset writes.
//
// @Requires |a| = 3 And a[0] = 5
// @Modifies a
// @Ensures a'[0] = 5
func ResetLoopWrong(a []int) {
	// @Invariant 0 <= i And i <= 3
	// @Variant 3 - i
	for i := 0; i < 3; i++ {
		genericslib.Reset(a)
	}
} // want `postcondition may not hold: a'\[0\] = 5`

// FoundBoth calls on the right of &&.
//
// @Ensures r -> (|xs| > 0 And |ys| > 0)
func FoundBoth(xs, ys []int) (r bool) {
	return genericslib.Find(xs, 1) >= 0 && genericslib.Find(ys, 2) >= 0
}

// ResetLater defers a call of a generic function.
//
// @Modifies a
// @Ensures True
func ResetLater(a []int) {
	defer genericslib.Reset(a)
}

// ResetLaterUnlisted defers it without listing what it writes.
//
// @Ensures True
func ResetLaterUnlisted(a []int) {
	defer genericslib.Reset(a) // want `Reset may modify a, which ResetLaterUnlisted may not modify`
}

// GrowWide grows a slice of eight-byte elements within the bound for them.
//
// @Requires n >= 0 And |s| + n <= MaxAlloc / 32
// @Ensures cap(r) - |r| >= n
func GrowWide(s []int64, n int) (r []int64) {
	return genericslib.GrowBy(s, n)
}

// GrowWideTooFar grows it within a bound that is enough for bytes only.
//
// @Requires n >= 0 And |s| + n <= MaxAlloc / 4
// @Ensures True
func GrowWideTooFar(s []int64, n int) (r []int64) {
	return genericslib.GrowBy(s, n) // want `precondition of GrowBy may not hold: 2 \* \(\|s\| \+ n\) \* elemsize\(s\) \+ 65536 <= MaxAlloc`
}

// GrowBytes grows a slice of bytes within the same bound.
//
// @Requires n >= 0 And |s| + n <= MaxAlloc / 4
// @Ensures True
func GrowBytes(s []byte, n int) (r []byte) {
	return genericslib.GrowBy(s, n)
}

// Empty has size zero.
type Empty struct{}

// GrowEmpty grows a slice of values of size zero, which only the bound of
// an int limits.
//
// @Requires 0 <= n And n <= 10 And |s| <= 100
// @Ensures True
func GrowEmpty(s []Empty, n int) (r []Empty) {
	return genericslib.GrowBy(s, n)
}

// GrowEmptyUnbounded does not bound the length.
//
// @Requires 0 <= n
// @Ensures True
func GrowEmptyUnbounded(s []Empty, n int) (r []Empty) {
	return genericslib.GrowBy(s, n) // want `precondition of GrowBy may not hold: \|s\| \+ n <= MaxInt`
}

// SameInt returns what Same returns.
//
// @Ensures r = x
func SameInt(x int) (r int) {
	return genericslib.Same(x)
}

// SameString returns what Same returns.
//
// @Ensures r = x
func SameString(x string) (r string) {
	return genericslib.Same(x)
}

// SamePoint cannot use the contract, whose clause compares a struct.
//
// @Ensures True
func SamePoint(p Point) (r Point) {
	return genericslib.Same(p) // want `the trusted contract of genericslib.Same \(trusted.yaml:\d+\) cannot be used with E = Point: in its ensures "result = x": a value of type E, which is Point here, is a struct, and a formula cannot compare a struct or use it as a whole; write out what it does instead`
}

// SameFloat cannot use the contract, whose clause compares a float.
//
// @Ensures True
func SameFloat(x float64) (r float64) {
	return genericslib.Same(x) // want `cannot be used with E = float64: in its ensures "result = x": operator = cannot be applied to float values`
}

// BigInt relies on what Big says at an int.
//
// @Ensures r > 300
func BigInt(x int) (r int) {
	return genericslib.Big(x)
}

// BigByte cannot use it at a byte, where it contradicts what a byte can
// hold.
//
// @Ensures True
func BigByte(x uint8) (r uint8) {
	return genericslib.Big(x) // want `cannot be used with E = uint8: it contradicts itself`
}

// NameOf calls a function whose entry names a field of a type parameter.
//
// @Ensures True
func NameOf(p struct{ N int }) (r int) {
	return genericslib.Name(p) // want `in its ensures "result = x.N": x.N names a field of a value of type E, a type parameter, whose type arguments need not have that field; a contract of a generic function cannot name it`
}

// LockedOf calls a function whose entry names a state of a type parameter.
//
// @Requires m != nil
// @Ensures True
func LockedOf(m *sync.Mutex) (r bool) {
	return genericslib.Locked(m) // want `held\(x\) names a state of a value of type T, a type parameter`
}

// AddressOf calls a function whose entry takes an address of an element
// of a type parameter's type.
//
// @Ensures True
func AddressOf(ps []Point) (r bool) {
	return genericslib.Address(ps) // want `&s\[\.\.\.\] takes the address of a value of type E, a type parameter`
}

// SizedOf calls a function whose entry asks elemsize of an integer.
//
// @Ensures True
func SizedOf(n int) (r bool) {
	return genericslib.Sized(n, 1) // want `elemsize\(n\): n is not a slice`
}

// P has a String method, which Show runs.
type P struct{ n int }

// String calls Loop, which calls Show, which calls String.
//
// @Ensures True
func (p P) String() (s string) { return Loop(p) } // want `this call may not end: P.String calls Loop at generics.go:\d+:\d+, Loop calls genericslib.Show\(p\) with T = P at generics.go:\d+:\d+, which may run P.String; a generic function may run the methods of a value of its type argument T, and of what such a value holds, through its constraint, through an interface, or by reflection, so a cycle goes through code of another package, and no Variant can be checked across it; if genericslib.Show runs no method of a value of type T, add "asserts: \{T: \[\]\}" to its entry in vego-trusted.yaml, or call it with a type that has no methods`

// Loop hands a P to a generic function whose entry does not say that it
// runs none of its methods.
//
// @Ensures True
func Loop(p P) (s string) {
	return genericslib.Show(p) // want `genericslib.Show is called with T = P, and genericslib.Show may run the method func \(P\).String\(\) \(s string\), which a value of that type reaches; if it runs no method of a value of type T, claim it in the entry of genericslib.Show with asserts: \{T: \[\]\}`
}

// Counter has a method of a constraint.
type Counter struct{ n int }

// Inc counts.
//
// @Requires c != nil And c.n < 100
// @Modifies c
// @Ensures c.n' = c.n + 1
func (c *Counter) Inc() { c.n++ }

// BumpCounter hands a counter to a function that calls the method of its
// constraint.
//
// @Requires c != nil
// @Ensures True
func BumpCounter(c *Counter) {
	genericslib.Bump(c) // want `genericslib.Bump is called with T = \*Counter, and genericslib.Bump may run the method func \(\*Counter\).Inc\(\)`
}

// Level has a String method, which Order claims to run none of.
type Level int

// String names a level.
//
// @Ensures True
func (l Level) String() (s string) { return "level" }

// OrderLevels sorts levels.
//
// @Modifies ls
// @Ensures |ls| = |ls|
func OrderLevels(ls []Level) {
	genericslib.Order(ls)
}

// Guarded holds a mutex, so it is never copied.
type Guarded struct {
	mu sync.Mutex
	n  int
}

// KeepGuarded hands over a value that holds a state.
//
// @Ensures True
func KeepGuarded() (r *Guarded) {
	return genericslib.Keep(Guarded{}) // want `genericslib.Keep is called with T = Guarded, which holds a sync.Mutex; a generic function copies and overwrites values of its type arguments, and a value that holds a state is never copied or overwritten`
}

// SameError hands over an error as a type argument.
//
// @Ensures True
func SameError(err error) (r error) {
	return genericslib.Same(err) // want `genericslib.Same is called with E = error, which is or holds an error; a generic function cannot be called yet with a type argument that can hold code`
}

// ResetComplex hands over a slice of complex numbers, which vego does not
// model.
//
// @Ensures True
func ResetComplex() {
	genericslib.Reset([]complex128(nil)) // want `genericslib.Reset is called with E = complex128, a type that vego does not model`
}

// EqualAny compares two interface values, which == may do with a panic.
//
// @Ensures True
func EqualAny(a, b any) (r bool) {
	return genericslib.Equal(a, b) // want `genericslib.Equal is called with E = any, whose values == may compare with a panic; its constraint is comparable, and only a type in which no interface lies can be passed`
}

// EqualInts compares two integers.
//
// @Ensures r <-> a = b
func EqualInts(a, b int) (r bool) {
	return genericslib.Equal(a, b)
}

// CountOf calls a function whose entry lists types for a type parameter.
//
// @Ensures True
func CountOf(xs []int) (r int) {
	return genericslib.Count(xs) // want `its asserts lists types for E, a type parameter; for a type parameter only \[\] can be claimed yet`
}

// Unentered calls a generic function without a contract.
//
// @Ensures True
func Unentered(x int) (r int) {
	return genericslib.Unentered(x) // want `it calls genericslib.Unentered, a generic function, which has no trusted contract; generic functions cannot be verified yet, so a call of one needs a trusted contract: add a trusted contract for genericslib.Unentered to vego-trusted.yaml`
}

// CallsVerified calls a generic function of another package that has
// annotations, which cannot be verified.
//
// @Ensures True
func CallsVerified(x int) (r int) {
	return genericslib.Verified(x) // want `it calls genericslib.Verified, a generic function, which has no trusted contract`
}

// Local is a generic function of this package with an entry.
func Local[E any](x E) E { return x }

// CallsLocal calls it.
//
// @Ensures r = x
func CallsLocal(x int) (r int) {
	return Local(x)
}

// Annotated is a generic function of this package with annotations.
//
// @Ensures r = x
func Annotated[E any](x E) (r E) { return x } // want `generic functions are not supported yet`

// CallsAnnotated calls it.
//
// @Ensures True
func CallsAnnotated(x int) (r int) {
	return Annotated(x) // want `it calls Annotated, a generic function with annotations; generic functions cannot be verified yet`
}

// Wrap is generic and calls a generic function with its own type
// parameter, which is never verified.
//
// @Ensures True
func Wrap[T comparable](xs []T, x T) (r int) { // want `generic functions are not supported yet`
	return genericslib.Find(xs, x)
}

// Nested hands over a literal that hands over another.
//
// @Ensures r < |ps|
func Nested(ps, qs []Point) (r int) {
	return genericslib.FindFunc(ps, func(p Point) bool {
		return genericslib.FindFunc(qs, func(q Point) bool { return q.X == p.X }) >= 0
	})
}

// CallsLocalWrong says more than the entry of Local.
//
// @Ensures r = x + 1
func CallsLocalWrong(x int) (r int) {
	return Local(x) // want `postcondition may not hold: r = x \+ 1`
}

// Back is a generic function of this package with an entry, whose body
// calls back into its caller.
func Back[E any](x E) E {
	CallsBack(0)
	return x
}

// CallsBack calls Back, which calls it.
//
// @Requires n >= 0
// @Ensures True
func CallsBack(n int) {
	Back(n) // want `Back is trusted and calls back into CallsBack, so that this call ends cannot be proved; Back is generic and cannot be verified yet, so break the cycle; the cycle: CallsBack calls Back at generics.go:\d+:\d+, Back calls CallsBack at generics.go:\d+:\d+`
}

// Finder finds an element.
//
// @Ensures r < |xs|
type Finder func(xs []int) (r int)

// UseFinder makes a value of a literal that calls a generic function and
// hands one over.
//
// @Ensures r < |xs|
func UseFinder(xs []int) (r int) {
	var f Finder = func(ys []int) (r int) {
		return genericslib.FindFunc(ys, func(y int) bool { return y > genericslib.Find(ys, 1) })
	}
	return f(xs)
}

// FindWhereOf hands over a literal to a function whose entry names a field
// of what the literal is given.
//
// @Ensures True
func FindWhereOf(ps []Point) (r int) {
	return genericslib.FindWhere(ps, func(p Point) bool { return p.X > 0 }) // want `e.X names a field of a value of type E, a type parameter`
}
