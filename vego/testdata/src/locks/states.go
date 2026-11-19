// Package locks holds programs that speak of the states that the shipped
// contracts declare for sync.Mutex and sync.RWMutex.
package locks

import (
	"errors"
	"sync"
)

// Account is guarded by its mutex.
type Account struct {
	mu      sync.Mutex
	balance int
}

// Keep writes the balance, which is not the mutex, so whether the caller
// holds the mutex is as it was.
//
// @Requires a != nil And held(a.mu)
// @Modifies a.balance
// @Ensures held(a.mu') And a.balance' = 1
func Keep(a *Account) {
	a.balance = 1
}

// Lose may write all of a, so it cannot promise anything about the state.
//
// @Requires a != nil
// @Modifies a
// @Ensures held(a.mu')
func Lose(a *Account) {
	a.balance = 1
} // want `vego: postcondition may not hold: held\(a.mu'\)`

// Fresh is not held: nobody has locked a mutex that was just made.
//
// @Ensures result != nil And ~held(result.mu)
func Fresh() (result *Account) {
	a := &Account{balance: 2}
	// @Assert ~held(a.mu)
	return a
}

// Local holds a mutex of its own, which is not held.
//
// @Ensures True
func Local() {
	var mu sync.Mutex
	// @Assert ~held(mu)
	_ = &mu
}

// Pointer reads the state where a pointer points.
//
// @Requires m != nil And held(m)
// @Ensures held(m')
func Pointer(m *sync.Mutex) {
}

// Both reads the two states of a read-write mutex.
//
// @Requires rw != nil And rheld(rw) And ~held(rw)
// @Ensures rheld(rw') And ~held(rw')
func Both(rw *sync.RWMutex) {
}

// Apart knows that two accounts differ when one mutex is held and the
// other is not.
//
// @Requires a != nil And b != nil And held(a.mu) And ~held(b.mu)
// @Ensures a != b
func Apart(a, b *Account) {
}

// Same knows nothing of the mutex of an account that may be another one.
//
// @Requires a != nil And b != nil And held(a.mu)
// @Ensures held(b.mu)
func Same(a, b *Account) {
} // want `vego: postcondition may not hold: held\(b.mu\)`

// ErrShort is returned when the balance is too small.
var ErrShort = errors.New("short")

// Guarded succeeds for some input, which has the mutex held; the search for
// such an input gives the state a value.
//
// @Requires a != nil And held(a.mu) And 0 <= n
// @Ensures (err = nil) <-> n <= a.balance
func Guarded(a *Account, n int) (err error) {
	if n > a.balance {
		return ErrShort
	}
	return nil
}

// Guards holds a mutex in a struct inside a struct.
type Guards struct {
	inner Account
	n     int
}

// Nested reads the state of a mutex two structs deep, and the search for
// an input gives it a value too.
//
// @Requires g != nil And held(g.inner.mu) And 0 <= n
// @Ensures (err = nil) <-> n <= g.n
func Nested(g *Guards, n int) (err error) {
	if n > g.n {
		return ErrShort
	}
	return nil
}

// Invariant states that the mutex is free at every boundary.
//
// @Invariant ~held(mu) And 0 <= count
type Free struct {
	mu    sync.Mutex
	count int
}

// Count relies on the invariant.
//
// @Requires f != nil
// @Ensures ~held(f.mu) And result >= 0
func Count(f *Free) (result int) {
	return f.count
}

// First reads the state of a mutex in an element of a slice, and the search
// for an input gives the elements a value for it.
//
// @Requires |as| > 0 And held(as[0].mu) And 0 <= n
// @Ensures (err = nil) <-> n <= as[0].balance
func First(as []Account, n int) (err error) {
	if n > as[0].balance {
		return ErrShort
	}
	return nil
}

// Loop keeps what it knows of the state through a loop that writes the
// balance.
//
// @Requires a != nil And held(a.mu) And 0 <= n <= 10
// @Modifies a.balance
// @Ensures held(a.mu')
func Loop(a *Account, n int) {
	// @Invariant held(a.mu) And 0 <= i <= n
	// @Variant n - i
	for i := 0; i < n; i++ {
		a.balance = i
	}
}
