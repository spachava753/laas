// Package statea relies on the state started that its trust file declares.
package statea

import "statelib"

// @Requires c != nil
// @Modifies c
// @Ensures err = nil -> started(c')
func Begin(c statelib.Conn) (err error) {
	return c.Start()
}
