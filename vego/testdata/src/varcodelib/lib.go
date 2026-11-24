// Package varcodelib has a variable of a function type that another
// package may try to set.
package varcodelib

// Event runs when something happens.
//
// @Ensures True
type Event func()

// OnEvent is run by Fire.
var OnEvent Event

// Reset clears the hook, and is not verified.
func Reset() { OnEvent = nil }
