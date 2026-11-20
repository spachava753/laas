// r29b: verified code formats a struct whose exported field has a String method that calls back.
package r29b

import "fmt"

// T2 has a String method that calls F.
type T2 struct{}

// @Ensures True
func (T2) String() (s string) { F(); return "" } // want `this\ call\ may\ not\ end:\ T2\.String\ calls\ F\ at\ p\.go:\d+:\d+,\ F\ formats\ with\ fmt\.Sprint\(S\{\}\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ T2\.String`

// S holds a T2 in an exported field.
type S struct{ T T2 }

// @Ensures True
func F() {
	_ = fmt.Sprint(S{}) // want `cannot\ verify\ F:\ Sprint\ formats\ S\{\},\ a\ value\ of\ type\ cycles/r29b\.S,\ and\ that\ may\ run\ code\ nobody\ has\ checked:\ cycles/r29b\.T2\ has\ a\ method\ String,\ whic`
}
