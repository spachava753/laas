// Package vouchsrcbad holds Vouches annotations that are refused.
package vouchsrcbad

// What is refused.

// Lone has a Vouches annotation and nothing else.
type Lone interface {
	// @Vouches err // want `Lone.Get has a Vouches annotation and no other clause; a Vouches annotation adds to a contract, so write one, as in // @Ensures True`
	Get() (err error)
}

// Wrong lists results that it cannot vouch for.
type Wrong interface {
	// @Ensures True
	// @Vouches n // want `in Vouches annotation: n has type int; a Vouches annotation lists results of type error, whose errors it vouches for`
	// @Vouches e // want `in Vouches annotation: e is not a result of Wrong.Get`
	// @Vouches err, err // want `in Vouches annotation: err is listed twice`
	// @Vouches err() // want `in Vouches annotation: "err\(\)" is not a name; a Vouches annotation lists error results, as in // @Vouches err`
	Get() (n int, err error)
}

// Verified vouches in the doc comment of a function.
//
// @Ensures True
// @Vouches err // want `a Vouches annotation belongs in the doc comment of a method of an interface type or of a function type, where it vouches for the errors that values of the type return; the errors of a verified function are judged from its body, and those of a trusted function are vouched for in the trust file`
func Verified() (err error) {
	// @Vouches err // want `a Vouches annotation belongs in the doc comment of a method of an interface type or of a function type`
	return nil
}

// Holder is a struct.
//
// @Vouches err // want `Vouches annotations do not belong on a type; a type can only have Invariant and Owns annotations`
type Holder struct{ n int }

// @Vochues err // want `unknown annotation "Vochues"`
// @vouches err // want `unknown annotation "vouches"`
//@Vouches err // want `an annotation is written "// @Keyword ...", with one space before the @ and none after it`
