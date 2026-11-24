// Package varcodelib has a variable of a function type that another
// package may try to set.
package varcodelib

import (
	"context"
	"io"
	"os"
)

// Event runs when something happens.
//
// @Ensures True
type Event func()

// OnEvent is run by Fire.
var OnEvent Event

// Reset clears the hook, and is not verified.
func Reset() { OnEvent = nil }

// Root is given what a function with no contract returns, which a read in
// another package cannot rely on.
var Root = context.Background()

// Started is given a literal that meets the contract of Event.
var Started Event = func() {}

// Ping is verified, so the initialisers of the package are checked.
//
// @Ensures True
func Ping() {}

// Log holds a file, which writing through changes nothing an importer can
// see.
var Log io.Writer = os.Stderr
