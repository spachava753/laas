package interfaces

// Ensurer and Denier declare a method of the same name and signature with
// contracts that differ.
type Ensurer interface {
	// @Ensures r > 0
	M() (r int)
}

type Denier interface {
	// @Ensures r < 0
	M() (r int)
}

// A defined interface that embeds Ensurer is identical only to itself, so
// it keeps Ensurer's contract.
type OnlyEnsurer interface{ Ensurer }

// @Requires x != nil
// @Ensures r > 0
func UseDefined(x OnlyEnsurer) (r int) {
	return x.M()
}

// @Requires y != nil
// @Ensures True
func DefinedFromDenier(y Denier) (r int) {
	var z OnlyEnsurer = y // want `cannot verify DefinedFromDenier: converting y, a interfaces.Denier, to interfaces.OnlyEnsurer is not supported: OnlyEnsurer has M from Ensurer.M, and Denier has M from Denier.M;`
	return UseDefined(z)
}

// An interface literal that embeds a declared interface is the same type as
// any other literal with the same methods, so it could carry either
// contract without a conversion.
//
// @Requires x != nil
// @Ensures r > 0
func UseLiteral(x interface{ Ensurer }) (r int) { // want `cannot verify UseLiteral: parameter x has unsupported type interface\{interfaces.Ensurer\}; an interface literal that embeds a declared interface is the same type`
	return x.M()
}

// @Requires y != nil
// @Ensures r > 0
func LiteralFromDenier(y Denier) (r int) {
	var z interface{ Denier } = y // want `cannot verify LiteralFromDenier: z has unsupported type interface\{interfaces.Denier\}`
	return UseLiteral(z)
}

// A slice of such values can be passed on, as before interfaces were
// modelled, but nothing in it can be taken out and called.
//
// @Ensures True
func LiteralSlices(bs []interface{ Denier }) (as []interface{ Ensurer }) {
	return bs
}

// @Requires |as| > 0
// @Ensures True
func LiteralElement(as []interface{ Ensurer }) (r int) {
	return as[0].M() // want `cannot verify LiteralElement: `
}

// @Ensures True
func LiteralRange(as []interface{ Ensurer }) (r int) {
	for _, a := range as { // want `cannot verify LiteralRange: `
		r = a.M()
	}
	return r
}

// @Requires m != nil
// @Ensures True
func LiteralMap(m map[string]interface{ Ensurer }) (r int) {
	return m["a"].M() // want `cannot verify LiteralMap: `
}

// @Ensures True
func LiteralMade() (as []interface{ Ensurer }) {
	return []interface{ Ensurer }{nil} // want `cannot verify LiteralMade: `
}

// An interface literal with methods of its own has no contracts, so its
// methods cannot be called, and it can be held.
//
// @Ensures (x = nil) <-> (y = nil)
func OwnMethods(x interface{ M() (r int) }) (y interface{ M() (r int) }) {
	return x
}

type LiteralHolder struct {
	N int
	E interface{ Ensurer }
}

// A struct with a field of such a type can be used, but not the field.
//
// @Requires h != nil
// @Ensures n = h.N
func FieldBeside(h *LiteralHolder) (n int) {
	return h.N
}

// @Requires h != nil
// @Ensures True
func FieldLiteral(h *LiteralHolder) (r int) {
	return h.E.M() // want `cannot verify FieldLiteral: `
}
