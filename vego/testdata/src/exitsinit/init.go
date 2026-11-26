// Package exitsinit ends the process in init and in the initialiser of a
// package-level variable, which only the runtime runs, so neither needs an
// Exits annotation (F14 of the review of step 1 of F37).
package exitsinit

import (
	"exits"
	"log"
	"os"
)

// @Ensures True
func init() {
	if len(os.Args) > 1000 {
		log.Fatal("too many arguments")
	}
}

// limit is 5 where Positive returns.
var limit = exits.Positive(5)

// UsesLimit knows what the initialiser of limit left in it.
//
// @Ensures r = 5
func UsesLimit() (r int) {
	return limit
}
