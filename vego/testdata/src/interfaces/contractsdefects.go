package interfaces

import "interfaceslib"

type Unnamed interface {
	// @Ensures True
	Count() int // want `Unnamed.Count has a contract, so each of its results needs a name, as in Count\(...\) \(n int\)`
}

type Never interface {
	// @Requires x > 0 And x < 0
	Get(x int) (y int) // want `nothing can satisfy the Requires clauses of Never.Get`
}

type Half interface {
	// @Requires 0 <= x <= 1000
	// @Ensures 2 * y = x
	Halve(x int) (y int) // want `the Ensures clauses of Half.Halve are not proved to be satisfiable for every call that its Requires allow`
}

type Contradicts interface {
	// @Ensures y > 0 And y < 0
	Get() (y int) // want `the contract of Contradicts.Get contradicts itself`
}

type Unknown interface {
	// @Ensures y = z // want `in Ensures annotation: unknown name z`
	Get() (y int)
}

type WrongKind interface {
	// @Invariant x > 0 // want `Invariant annotations do not belong on a method of an interface; it can only have Requires, Ensures, and Modifies annotations`
	Get(x int) (y int)
}

type Embedder interface {
	// @Ensures True // want `a contract cannot be written on an embedded interface`
	Pricer
}

type Aliased = interface {
	// @Ensures y > 0 // want `a contract can only be declared on a method of a defined interface type at package level without type parameters`
	Get() (y int)
}

type GenericContract[T any] interface {
	// @Ensures True // want `a contract can only be declared on a method of a defined interface type at package level without type parameters`
	Get() (t T)
}

// @Ensures True
func Literal(x interface {
	// @Ensures y > 0 // want `a contract can only be declared on a method of a defined interface type at package level without type parameters`
	Get() (y int)
}) {
}

type Variadic interface {
	// @Ensures True
	Sum(xs ...int) (n int) // want `a contract on a variadic method of an interface is not supported yet`
}

// Go keeps the first declaration of a method that two embedded interfaces
// declare, so the contract of the second would be skipped.
type SizedTwice interface { // want `the contract of Sizer.Size is not part of this interface: it has Size from Size2.Size`
	Size2
	interfaceslib.Sizer
}

type Size2 interface {
	// @Ensures n >= 0
	Size() (n int)
}

type Redeclared interface { // want `the contract of Pricer.Price is not part of this interface: it has Price from Redeclared.Price`
	Pricer
	// @Ensures True
	Price(sku string, qty int) (cents int, ok bool)
}
