package funcvalues

// The contract of a function type is checked where it is declared.

// Unnamed has a contract and an unnamed result.
//
// @Ensures True
type Unnamed func(x int) int // want `vego: Unnamed has a contract, so each of its results needs a name, as in type Unnamed func\(...\) \(n int\)`

// Spread is variadic.
//
// @Ensures True
type Spread func(xs ...int) // want `vego: a contract on a variadic function type is not supported yet`

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
