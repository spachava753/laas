// Package guidestats holds a counter for the guide's section on variables
// of other packages.
package guidestats

import "math"

var requests int

// Hit counts a request.
//
// @Modifies requests
// @Ensures requests < MaxInt -> requests' = requests + 1
func Hit() {
	if requests < math.MaxInt {
		requests++
	}
}

// Count returns the count.
//
// @Ensures r = requests
func Count() (r int) {
	return requests
}
