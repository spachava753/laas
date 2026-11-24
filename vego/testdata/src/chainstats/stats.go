// Package chainstats keeps a counter that is not exported, which callers
// three calls up cover by naming the state of a package (D1 of package-level
// variables).
package chainstats

import "math"

var requests int

// Exported is a variable that importers may name one by one.
var Exported int

// Hit counts a request.
//
// @Modifies requests
// @Ensures requests < MaxInt -> requests' = requests + 1
func Hit() {
	if requests < math.MaxInt {
		requests++
	}
}

// Count reads the count.
//
// @Ensures r = requests
func Count() (r int) {
	return requests
}
