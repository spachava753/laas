// Package twoownlib declares a gauge without a contract, and has proofs
// that rest on it having none.
package twoownlib

// Gauge reads a number.
type Gauge interface {
	Read() (n int)
}

func keep(g Gauge) {}

// @Ensures True
func Keeps(g Gauge) {
	keep(g)
}
