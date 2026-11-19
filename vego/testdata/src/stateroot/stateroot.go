// Package stateroot is built with three modules and has no proofs of its
// own: two declare the states of one interface differently, and the
// proofs of the third were made with none.
package stateroot // want `the trust files of this build declare the states of statelib.Conn differently, at .*statea/vego-trusted.yaml:4 and at .*statec/vego-trusted.yaml:4` `the trust files of this build declare states of statelib.Conn at .*vego-trusted.yaml:4, and the proofs of package stateb were made with none; a value whose states one proof changed can reach a proof that reads them otherwise: declare the same states in the trust file of its module`

import (
	"statea"
	"stateb"
	"statec"
	"statelib"
)

// Use hands one connection to each.
func Use(c statelib.Conn) {
	statea.Begin(c)
	stateb.End(&stateb.Holder{C: c})
	statec.Begin(c)
}
