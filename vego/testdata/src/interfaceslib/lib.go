// Package interfaceslib declares interfaces with contracts that other
// packages embed, call, and implement.
package interfaceslib

// Sizer reports a size.
type Sizer interface {
	// @Ensures 0 <= n <= 100
	Size() (n int)
}

// Pricer prices an order line.
type Pricer interface {
	// @Requires 0 <= qty <= 1000
	// @Ensures ok -> 0 <= cents <= 1000000
	Price(sku string, qty int) (cents int, ok bool)
}

// Sized is a defined type made from Sizer, which has Sizer's method and
// its contract.
type Sized Sizer

// Measure calls the Size method of what it is given. It is trusted.
func Measure(s Sizer) (n int) { return s.Size() }
