// Package globalslib declares package-level variables that other packages
// read.
package globalslib

// Limit is never changed in this package.
var Limit = 5

// Names is a slice made by a literal.
var Names = []string{"a", "b"}

// Point is a struct.
type Point struct{ X, Y int }

// Origin is a struct value.
var Origin = Point{X: 1, Y: 2}

// Version is changed by another package of the build.
var Version = "dev"

// Counter is changed here.
var Counter int

// Bump is not verified.
func Bump() { Counter++ }

// hidden is not exported.
var hidden = 7

// Hidden returns it.
//
// @Ensures r = hidden
func Hidden() (r int) { return hidden }

// AtLimit uses Limit in its contract.
//
// @Requires 0 <= n <= Limit
// @Ensures r = Limit - n
func AtLimit(n int) (r int) { return Limit - n }

// IsDev relies on Version.
//
// @Ensures r = |Version|
func IsDev() (r int) { return len(Version) }

// Table is a slice that other packages write.
var Table = []int{0, 1}

// First reads it.
//
// @Ensures r = Table[0]
func First() (r int) { return Table[0] }

// Plans is only read in this package; globalsmid writes it.
var Plans = map[string]int{"free": 10, "pro": 1000}

// FreeLimit relies on what Plans refers to being only read.
//
// @Ensures r = 10
func FreeLimit() (r int) { return Plans["free"] }
