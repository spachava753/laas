package funcvalues

// The contract of a function type is checked where it is declared.

// Unnamed has a contract and an unnamed result.
//
// @Ensures True
type Unnamed func(x int) int // want `vego: Unnamed has a contract, so each of its results needs a name, as in type Unnamed func\(...\) \(n int\)`

// Spread is variadic, which a type with a contract may be.
//
// @Ensures True
type Spread func(xs ...int)

// Never can be called with nothing.
//
// @Requires x > 0 And x < 0
type Never func(x int) // want `vego: nothing can satisfy the Requires clauses of Never together with what the types of its parameters guarantee, so no value of the type could be called`

// Impossible promises what nothing can.
//
// @Ensures False
type Impossible func(x int) // want `vego: the contract of Impossible contradicts itself, so a call of a value of the type would prove anything`

// Unknown names something that is not there.
//
// @Requires z > 0 // want `vego: in Requires annotation: .*z`
type Unknown func(x int)

// ByValue lists a parameter passed by value.
//
// @Modifies x // want `vego: in Modifies annotation: .*passed by value`
type ByValue func(x int)

// Kept has an annotation a function type cannot have.
//
// @Invariant x > 0 // want `vego: Invariant annotations do not belong on a function type; a function type can only have Requires, Ensures, and Modifies annotations`
type Kept func(x int)

// Alias is an alias.
//
// @Ensures True // want `vego: a contract can only be declared on a defined function type, not on an alias`
type Alias = func(x int)

// Half promises a result for every number in range, which an odd number
// cannot have. A value from outside is taken to meet the contract, so a
// call of one would teach that the number is even.
//
// @Requires 0 <= x <= 1000
// @Ensures 2 * y = x
type Half func(x int) (y int) // want `vego: the Ensures clauses of Half are not proved to be satisfiable for every call that its Requires allow, by results and a change of what Modifies lists; a value of the type is taken to meet them, so a call of one could prove something false. State in the Requires when some result exists, or weaken the Ensures`

// Counted holds a number.
type Counted struct{ n int }

// Five promises a field it may not write.
//
// @Requires c != nil
// @Ensures c.n' = 5
type Five func(c *Counted) // want `vego: the contract of Five cannot be used: its ensures "c.n' = 5" describes c.n' after the call, but nothing its modifies lists is memory that c.n' reads, so the call cannot have changed it; drop the prime or list what the function writes` `vego: the Ensures clauses of Five are not proved to be satisfiable`

// Sets5 may write the field, so it can promise it.
//
// @Requires c != nil
// @Modifies c.n
// @Ensures c.n' = 5
type Sets5 func(c *Counted)

// Even would learn from a call of a Half that its number is even.
//
// @Requires h != nil And 0 <= x <= 1000
// @Ensures True
func Even(h Half, x int) {
	h(x) // want `vego: cannot verify Even: the contract of Half could not be understood`
}

// Unbounded promises one more than a field that may already be the largest
// int, which no value can meet.
//
// @Requires c != nil
// @Modifies c.n
// @Ensures c.n' = c.n + 1
type Unbounded func(c *Counted) // want `vego: the Ensures clauses of Unbounded are not proved to be satisfiable`

// Zeroes promises to clear a slice, which the check cannot show a value can
// do: it does not choose new contents for a slice.
//
// @Modifies xs
// @Ensures Forall i in [0, |xs|) : xs'[i] = 0
type Zeroes func(xs []int) // want `vego: the Ensures clauses of Zeroes are not proved to be satisfiable`

// Picks promises a result in a range that depends on its argument.
//
// @Requires 0 <= lo <= hi
// @Ensures lo <= r <= hi
type Picks func(lo int, hi int) (r int)

// Fails promises an error when its argument is negative.
//
// @Ensures (err != nil) <-> x < 0
type Fails func(x int) (err error)

// Get reads a field, whose value is an int.
//
// @Requires s != nil
// @Ensures r = s.n
type Get func(s *Counted) (r int)

// Pair of fields, one copied into the other.
type Two struct{ n, m int }

// Copy copies one field into another.
//
// @Requires c != nil
// @Modifies c.n
// @Ensures c.n' = c.m
type Copy func(c *Two)
