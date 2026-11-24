package varcode

import (
	"encoding/json"
	"fmt"
	"io"
	"os"

	"varcodelib"
)

// Fixed variables of interface types, which nothing assigns (O1 of the
// orchestrator). What their initialiser converts decides what a write
// through them needs.

// errOut holds a file, whose Write writes nothing behind its receiver, and
// io.Writer has no states, so a print or a Write through it changes nothing
// a caller can see.
var errOut io.Writer = os.Stderr

// warn prints through it with nothing listed.
//
// @Ensures True
func warn(s string) {
	if errOut == nil {
		return
	}
	fmt.Fprintln(errOut, "x")
	errOut.Write([]byte("y"))
}

// warnJSON encodes into it, which calls only its Write.
//
// @Ensures True
func warnJSON() {
	if errOut == nil {
		return
	}
	json.NewEncoder(errOut).Encode(1)
}

// warnListed lists it, which nothing needs.
//
// @Modifies errOut // want `^vego: Modifies lists errOut, but warnListed never needs to modify it; a Modifies clause must list exactly what the function may write$`
// @Ensures True
func warnListed() {
	if errOut == nil {
		return
	}
	fmt.Fprintln(errOut, "x")
}

// counter counts the writes to it in its own struct.
type counter struct{ n int }

// @Requires c != nil
// @Modifies c
// @Ensures n = |p| And err = nil
func (c *counter) Write(p []byte) (n int, err error) {
	if c.n < 1000 {
		c.n++
	}
	return len(p), nil
}

// sink holds a value whose footprint is the struct its initialiser made.
var sink io.Writer = &counter{}

// count writes through it, listing it.
//
// @Modifies sink
// @Ensures True
func count() {
	if sink == nil {
		return
	}
	sink.Write([]byte("x"))
}

// countUnlisted does not list it.
//
// @Ensures True
func countUnlisted() {
	if sink == nil {
		return
	}
	sink.Write([]byte("x")) // want `^vego: sink.Write may modify the footprint of sink, which countUnlisted may not modify; list it in a // @Modifies clause$`
}

// closer holds a file as an io.Closer, whose Close changes its state
// closed.
var closer io.Closer = os.Stdin

// shut closes it, listing it; it cannot know it is not closed yet.
//
// @Modifies closer
// @Ensures True
func shut() {
	if closer == nil {
		return
	}
	closer.Close() // want `^vego: precondition of closer.Close may not hold: ~closed\(c\)$`
}

// shutUnlisted does not list it.
//
// @Ensures True
func shutUnlisted() {
	if closer == nil {
		return
	}
	closer.Close() // want `^vego: precondition of closer.Close may not hold: ~closed\(c\)$` `^vego: closer.Close may modify the states of closer, which shutUnlisted may not modify; list it in a // @Modifies clause$`
}

// Ticks returns a count.
//
// @Ensures t >= 0
type Ticks func() (t int)

// ticks is fixed, and a call of it is a call of the contract of Ticks.
var ticks Ticks = func() (t int) { return 0 }

// readTicks relies on the contract.
//
// @Ensures t >= 0
func readTicks(x int) (t int) {
	if ticks == nil {
		return 0
	}
	return ticks()
}

// readTicksExact claims more than the contract says.
//
// @Ensures t = 0
func readTicksExact(x int) (t int) {
	if ticks == nil {
		return 0
	}
	return ticks() // want `^vego: postcondition may not hold: t = 0$`
}

// warnLib prints through an inert variable of another package, which that
// package publishes.
//
// @Ensures True
func warnLib() {
	if varcodelib.Log == nil {
		return
	}
	fmt.Fprintln(varcodelib.Log, "x")
}

// shutter has a state that its method changes.
//
// @State shut
type shutter interface {
	// @Receiver s
	// @Requires ~shut(s)
	// @Modifies s
	// @Ensures shut(s')
	Shut()
}

// nopShut changes nothing, but a value of it as a shutter has the state
// its contract gives it.
type nopShut struct{}

// @Ensures True
func (nopShut) Shut() {}

var door shutter = nopShut{}

// shutDoor changes the state of what door holds without listing door.
//
// @Ensures True
func shutDoor() {
	if door == nil {
		return
	}
	door.Shut() // want `^vego: precondition of door.Shut may not hold: ~shut\(s\)$` `^vego: door.Shut may modify the states of door, which shutDoor may not modify; list it in a // @Modifies clause$`
}
