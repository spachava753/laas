// r29: a Stringer in an exported field of a formatted struct calls back.
package r29

import "fmt"

// T2 has a String method that calls F.
type T2 struct{}

func (T2) String() string { F(); return "" }

// S holds a T2 in an exported field.
type S struct{ T T2 }

// show formats an S; it is trusted.
func show() { _ = fmt.Sprint(S{}) }

// @Ensures True
func F() {
	show() // want `show\ is\ trusted\ and\ calls\ back\ into\ F,\ so\ that\ this\ call\ ends\ cannot\ be\ proved;\ verify\ show\ instead\ of\ trusting\ it`
}
