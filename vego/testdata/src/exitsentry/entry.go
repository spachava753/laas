// Package exitsentry calls through a fmt.Stringer whose entry claims that
// it ends the process.
package exitsentry

import "fmt"

// Name calls String and claims what nothing could show if String ended
// the process.
//
// @Requires s != nil
// @Ensures r = 7
func Name(s fmt.Stringer) (r int) {
	_ = s.String() // want `vego: the trusted contract of \(fmt\.Stringer\)\.String \(vego-trusted\.yaml:\d+\) cannot be used: exits is allowed only in the entry of a package-level function: fmt, errors, and conversions to interfaces call methods and values of function types where no call is written, and a run that ends the process there would not be seen`
	return 8
}
