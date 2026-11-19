package ifacestate

import "io"

// Plain has no states, so its methods cannot name a receiver.
type Plain interface {
	// @Receiver p
	// @Ensures True
	Do() // want `Plain.Do names its receiver p, but Plain has no states`
}

// Clash names the receiver as a parameter.
//
// @State ready
type Clash interface {
	// @Receiver x // want `in Receiver annotation: x already names a parameter or a result of Go`
	// @Ensures True
	Go(x int)
}

// Named names the receiver twice.
//
// @State ready
type Named interface {
	// @Receiver t
	// @Receiver u // want `in Receiver annotation: the receiver is named twice`
	// @Ensures True
	Go()
}

// @Receiver f // want `a Receiver annotation belongs in the doc comment of a method in an interface type`
// @Ensures True
func Lonely() {}

// Struct is not an interface.
//
// @State ready // want `a state can be declared only on a defined interface type that declares a method of its own; Struct is not an interface type`
type Struct struct{ n int }

// Embeds declares no method of its own.
//
// @State ready // want `a state can be declared only on a defined interface type that declares a method of its own; Embeds declares no method of its own`
type Embeds interface{ io.Closer }

// Reserved names a state with a word of formulas.
//
// @State old // want `"old" cannot name a state`
type Reserved interface{ M() }

// Repeated declares one state twice.
//
// @State ready
// @State ready // want `Repeated already has the state ready`
type Repeated interface{ M() }

// Double gets closed from io.Closer and declares a closed of its own.
//
// @State closed
type Double interface { // want `Double has two states named closed, closed of io.Closer and closed of ifacestate.Double`
	io.Closer
	M()
}

// Unnamed speaks of a state without naming the receiver.
//
// @State ready
type Unnamed interface {
	// @Ensures ready(s) // want `unknown`
	M()
}

// Glued writes the keyword against its name.
//
// @State ready
type Glued interface {
	// @Receiverg // want `unknown annotation`
	// @Ensures True
	M()
}

// Embedding documents an embedded interface.
//
// @State ready
type Embedding interface {
	// @Receiver e // want `a contract cannot be written on an embedded interface`
	io.Closer
	M()
}

// Defined is made from io.Closer and has its methods, which belong to
// io.Closer.
//
// @State gone // want `a state can be declared only on a defined interface type that declares a method of its own; Defined declares no method of its own`
type Defined io.Closer
