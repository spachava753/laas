package interfaces

import "interfaceslib"

func loadPricer() (p Pricer) { return nil }

// A result that a trusted contract vouches for meets the contract of its
// interface.
//
// @Ensures ok -> 0 <= cents <= 1000000
func Loads() (cents int, ok bool) {
	p := loadPricer()
	if p == nil {
		return 0, false
	}
	return p.Price("a", 2)
}

func (s *Shop) reset() {}

// @Requires s != nil
// @Modifies s
// @Ensures True
func Resets(s *Shop) {
	s.reset() // want `the trusted contract of \(\*interfaces.Shop\).reset \(trusted.yaml:\d+\) cannot be used: its modifies "s" covers memory that can hold a function value or an interface value of a type with a contract` `cannot verify Resets: reset has a contract that could not be understood`
}

func priceWith(p Pricer) (n int) { return 0 }

// @Requires p != nil
// @Ensures n >= 0
func PricesWith(p Pricer) (n int) {
	return priceWith(p)
}

// A function that hands a value of an interface to a trusted function
// under runs may make a call through it, so it cannot be made into a value
// or a method of an interface value.
//
// @Ensures f != nil
func PricesWithValue() (f Mapper) {
	return pricesThrough // want `cannot verify PricesWithValue: pricesThrough may call through a function value or an interface value`
}

// @Requires 0 <= x <= 1000
// @Ensures 0 <= y <= 1000
func pricesThrough(x int) (y int) {
	priceWith(Flat(1))
	return x
}

func takesLiterals(as []interface{ Ensurer }) (n int) { return 0 }

func takesLiteralsUnclaimed(as []interface{ Ensurer }) (n int) { return 0 }

// A slice of interface literals carries code whose contract is not known,
// so a trusted function takes it only under runs.
//
// @Ensures True
func HandsLiterals(as []interface{ Ensurer }) (n int) {
	return takesLiterals(as)
}

// @Ensures True
func HandsLiteralsUnclaimed(as []interface{ Ensurer }) (n int) {
	return takesLiteralsUnclaimed(as) // want `cannot verify HandsLiteralsUnclaimed: as is passed to takesLiteralsUnclaimed, which is trusted`
}

// @Ensures True
func HandsLiteralsToValue(f LiteralsTaker, as []interface{ Ensurer }) {
	if f != nil {
		f(as) // want `cannot verify HandsLiteralsToValue: as is passed to the function value f and is a value of type \[\]interface\{interfaces.Ensurer\}, which can hold an error, or another interface`
	}
}

// LiteralsTaker is given interface literals.
//
// @Ensures True
type LiteralsTaker func(as []interface{ Ensurer })

// Measured calls a trusted function of another package that calls Size on
// what it is given, so converting it to an interfaceslib.Sizer would let
// Size reach itself.
type Measured struct{}

// @Ensures 0 <= n <= 100
func (Measured) Size() (n int) {
	return interfaceslib.Measure(Measured{}) // want `cannot verify Size: Size may call through a function value or an interface value, and code that an interface value runs cannot do that yet`
}

// @Ensures True
func FromMeasured() (s interfaceslib.Sizer) {
	return Measured{} // want `cannot verify FromMeasured: Size may call through a function value or an interface value`
}
