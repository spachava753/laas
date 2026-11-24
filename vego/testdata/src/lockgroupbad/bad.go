// Package lockgroupbad holds what a lock clause refuses: a helper that
// requires the lock and that code of another package can call, one made
// into a value, and groups whose mutex is not reached only through them.
package lockgroupbad

import (
	"math"
	"sync"
)

// @Invariant ~held(mu) And 0 <= hits
var (
	mu   sync.Mutex
	hits int
)

// Bump requires the lock, and is exported.
//
// @Requires held(mu)
// @Modifies hits
// @Ensures True
func Bump() { // want `vego: nothing can satisfy the Requires clauses of Bump together with what the types of its parameters guarantee, so verifying it would prove nothing`
	if hits < math.MaxInt {
		hits++
	}
}

// bumpValue requires the lock, and is made into a value below, so it is
// entered from outside and assumes ~held(mu) too.
//
// @Requires held(mu)
// @Modifies hits
// @Ensures True
func bumpValue() { // want `vego: nothing can satisfy the Requires clauses of bumpValue together with what the types of its parameters guarantee, so verifying it would prove nothing`
	if hits < math.MaxInt {
		hits++
	}
}

// Later holds bumpValue.
var Later = bumpValue

// @Invariant ~running(once) And 0 <= runs // want `vego: the invariant of once, runs cannot be relied on: once is a struct variable whose address is taken, and Do at bad\.go:\d+ runs a function it is handed while it has the address, which could see the invariant broken`
var (
	once sync.Once
	runs int
)

// Run runs once.
//
// @Modifies once
// @Ensures True
func Run() {
	once.Do(func() {}) // want `vego: precondition of Do may not hold: ~running\(o\)`
}

// @Invariant ~held(openMu) // want `vego: the invariant of openMu cannot be relied on: openMu is a struct variable whose address is taken, and a method value of it is made at bad\.go:\d+; one can be in a group only when its address is handed only to trusted functions that neither keep it nor run code that could be handed it`
var openMu sync.Mutex

// OpenLock is a method value of openMu's Lock.
var OpenLock = openMu.Lock

// @Invariant ~held(testMu) // want `vego: the invariant of testMu cannot be relied on: testMu is changed at bad\.go:\d+ in lockForTest, which is not verified; every change of a variable with an invariant must be made by a function of the package that is verified, which restores it, so call one`
var testMu sync.Mutex

// lockForTest locks testMu, and is not verified.
func lockForTest() { testMu.Lock() }
