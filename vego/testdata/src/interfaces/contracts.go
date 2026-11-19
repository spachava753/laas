package interfaces

import "interfaceslib"

// Pricer prices an order line.
type Pricer interface {
	// Price returns the price of qty units of sku, if sku is known.
	//
	// @Requires 0 <= qty <= 1000
	// @Ensures ok -> 0 <= cents <= 1000000
	Price(sku string, qty int) (cents int, ok bool)
}

// Cell holds a number.
type Cell struct{ V int }

// Setter writes into what it is given.
type Setter interface {
	// @Requires c != nil And 0 <= v
	// @Modifies c.V
	// @Ensures c.V' = v
	Set(c *Cell, v int)
}

// Checker embeds Pricer, so it has Price with its contract.
type Checker interface {
	Pricer
	// @Ensures True
	Valid(sku string) (ok bool)
}

// Both embeds two interfaces of another package.
type Both interface {
	interfaceslib.Sizer
	interfaceslib.Pricer
}
