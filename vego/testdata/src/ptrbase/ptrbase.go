// Package ptrbase holds a struct with a field that points to an int, which
// verified code reads, copies, and overwrites without following it; each
// of these verified before pointers to single values were supported, and
// verifies after (the reviewer's probes of the design of F37, F11).
package ptrbase

import (
	"encoding/json"
	"fmt"
)

// Config has a limit that may be absent.
type Config struct {
	Limit *int
	N     int
}

// Bump increments N.
//
// @Requires c != nil And c.N < 100
// @Modifies c.N
// @Ensures c.N' = c.N + 1
func Bump(c *Config) {
	c.N++
}

// Copy returns a copy of what c points to.
//
// @Requires c != nil
// @Ensures r.N = c.N
func Copy(c *Config) (r Config) {
	return *c
}

// Reset overwrites what c points to.
//
// @Requires c != nil
// @Modifies c
// @Ensures True
func Reset(c *Config) {
	*c = Config{}
}

// Print prints N.
//
// @Requires c != nil
// @Ensures True
func Print(c *Config) {
	fmt.Println(c.N)
}

// Decode decodes a number into a local variable.
//
// @Requires |data| <= 100
// @Ensures True
func Decode(data []byte) (n int, err error) {
	err = json.Unmarshal(data, &n)
	return n, err
}
