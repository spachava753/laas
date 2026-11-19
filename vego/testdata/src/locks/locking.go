package locks

import (
	"errors"
	"sort"
	"sync"
)

// Deposit locks the account and unlocks it at every return.
//
// @Requires a != nil And ~held(a.mu) And 0 <= n And 0 <= a.balance
// @Modifies a.mu, a.balance
// @Ensures ~held(a.mu')
// @Ensures ok -> a.balance' = a.balance + n
func (a *Account) Deposit(n int) (ok bool) {
	a.mu.Lock()
	defer a.mu.Unlock()
	if n > 1000000-a.balance {
		return false
	}
	a.balance += n
	return true
}

// ErrLow is returned when the balance is too small.
var ErrLow = errors.New("low")

// Withdraw succeeds for some input although its mutex is part of every
// input.
//
// @Requires a != nil And ~held(a.mu) And 0 <= n
// @Modifies a.mu, a.balance
// @Ensures ~held(a.mu') And ((err = nil) <-> n <= a.balance)
func (a *Account) Withdraw(n int) (err error) {
	a.mu.Lock()
	defer a.mu.Unlock()
	if n > a.balance {
		return ErrLow
	}
	a.balance -= n
	return nil
}

// add runs while its caller holds the mutex.
//
// @Requires a != nil And held(a.mu) And 0 <= n <= 100 And 0 <= a.balance <= 100
// @Modifies a.balance
// @Ensures held(a.mu') And a.balance' = a.balance + n
func (a *Account) add(n int) {
	a.balance += n
}

// AddTwice holds the mutex across two calls of a helper that requires it.
//
// @Requires a != nil And ~held(a.mu) And 0 <= a.balance <= 50
// @Modifies a.mu, a.balance
// @Ensures ~held(a.mu') And a.balance' = a.balance + 2
func (a *Account) AddTwice() {
	a.mu.Lock()
	a.add(1)
	a.add(1)
	a.mu.Unlock()
}

// Unlocked calls the helper without the mutex.
//
// @Requires a != nil And ~held(a.mu) And 0 <= a.balance <= 50
// @Modifies a.balance
// @Ensures True
func (a *Account) Unlocked() {
	a.add(1) // want `vego: precondition of add may not hold: held\(a.mu\)`
}

// Twice locks a mutex it holds, which would wait for ever.
//
// @Requires a != nil And ~held(a.mu)
// @Modifies a.mu
// @Ensures True
func Twice(a *Account) {
	a.mu.Lock()
	a.mu.Lock() // want `vego: precondition of Lock may not hold: ~held\(m\)`
}

// Release unlocks a mutex it may not hold, which is a run-time error.
//
// @Requires a != nil
// @Modifies a.mu
// @Ensures True
func Release(a *Account) {
	a.mu.Unlock() // want `vego: precondition of Unlock may not hold: held\(m\)`
}

// OnePath unlocks on one path only.
//
// @Requires a != nil And ~held(a.mu)
// @Modifies a.mu
// @Ensures ~held(a.mu')
func OnePath(a *Account, early bool) {
	a.mu.Lock()
	if early {
		return // want `vego: postcondition may not hold: ~held\(a.mu'\)`
	}
	a.mu.Unlock()
}

// Unlisted does not list the mutex, which Lock writes.
//
// @Requires a != nil And ~held(a.mu)
// @Ensures True
func Unlisted(a *Account) {
	a.mu.Lock() // want `vego: Lock may modify a.mu, which Unlisted may not modify; list it in a // @Modifies clause`
	a.mu.Unlock()
}

// Pair locks two mutexes that may be the same.
//
// @Requires a != nil And b != nil And ~held(a.mu) And ~held(b.mu)
// @Modifies a.mu, b.mu
// @Ensures True
func Pair(a, b *Account) {
	a.mu.Lock()
	b.mu.Lock() // want `vego: precondition of Lock may not hold: ~held\(m\)`
	b.mu.Unlock()
	a.mu.Unlock()
}

// Apart locks two mutexes that differ.
//
// @Requires a != nil And b != nil And a != b And ~held(a.mu) And ~held(b.mu)
// @Modifies a.mu, b.mu
// @Ensures ~held(a.mu') And ~held(b.mu')
func ApartPair(a, b *Account) {
	a.mu.Lock()
	b.mu.Lock()
	b.mu.Unlock()
	a.mu.Unlock()
}

// Nil locks through a pointer that may be nil, which panics.
//
// @Requires ~held(m)
// @Modifies m
// @Ensures True
func Nil(m *sync.Mutex) {
	m.Lock() // want `vego: precondition of Lock may not hold: m != nil`
}

// Try locks only when TryLock says so.
//
// @Requires m != nil And ~held(m)
// @Modifies m
// @Ensures ~held(m')
func Try(m *sync.Mutex) (ok bool) {
	if m.TryLock() {
		m.Unlock()
		return true
	}
	return false
}

// TryHeld cannot unlock after a TryLock that failed.
//
// @Requires m != nil And ~held(m)
// @Modifies m
// @Ensures True
func TryHeld(m *sync.Mutex) {
	ok := m.TryLock()
	if !ok {
		m.Unlock() // want `vego: precondition of Unlock may not hold: held\(m\)`
	}
}

// Read takes a read lock and gives it back.
//
// @Requires rw != nil And ~held(rw) And ~rheld(rw)
// @Modifies rw
// @Ensures ~held(rw') And ~rheld(rw')
func Read(rw *sync.RWMutex) {
	rw.RLock()
	defer rw.RUnlock()
}

// ReadTwice takes a second read lock, which may wait for a writer that
// waits for the first.
//
// @Requires rw != nil And ~held(rw) And ~rheld(rw)
// @Modifies rw
// @Ensures True
func ReadTwice(rw *sync.RWMutex) {
	rw.RLock()
	rw.RLock() // want `vego: precondition of RLock may not hold: ~rheld\(rw\)`
}

// Upgrade takes the write lock while it holds a read lock.
//
// @Requires rw != nil And ~held(rw) And ~rheld(rw)
// @Modifies rw
// @Ensures True
func Upgrade(rw *sync.RWMutex) {
	rw.RLock()
	rw.Lock() // want `vego: precondition of Lock may not hold: ~rheld\(rw\)`
}

// Write takes the write lock and gives it back.
//
// @Requires rw != nil And ~held(rw) And ~rheld(rw)
// @Modifies rw
// @Ensures ~held(rw') And ~rheld(rw')
func Write(rw *sync.RWMutex) {
	rw.Lock()
	rw.Unlock()
}

// Embedded has its mutex as an embedded field.
type Embedded struct {
	sync.Mutex
	n int
}

// Promoted calls the methods promoted from the embedded mutex.
//
// @Requires e != nil And ~held(e.Mutex) And e.n < 100
// @Modifies e.Mutex, e.n
// @Ensures ~held(e.Mutex') And e.n' = e.n + 1
func Promoted(e *Embedded) {
	e.Lock()
	e.n++
	e.Unlock()
}

// InLiteral locks inside a function literal called in place.
//
// @Requires a != nil And ~held(a.mu)
// @Modifies a.mu, a.balance
// @Ensures ~held(a.mu')
func InLiteral(a *Account) {
	func() {
		a.mu.Lock()
		defer a.mu.Unlock()
		a.balance = 0
	}()
}

// InLoop locks and unlocks in each iteration.
//
// @Requires a != nil And ~held(a.mu) And 0 <= n <= 10
// @Modifies a.mu, a.balance
// @Ensures ~held(a.mu')
func InLoop(a *Account, n int) {
	// @Invariant ~held(a.mu) And 0 <= i <= n
	// @Variant n - i
	for i := 0; i < n; i++ {
		a.mu.Lock()
		a.balance = i
		a.mu.Unlock()
	}
}

// InRun locks in a function that sort.Search calls. A run starts in a state
// that stands for every run, in which what any run writes is forgotten, so
// whether the mutex is held there is not known.
//
// @Requires a != nil And ~held(a.mu) And 0 <= n
// @Modifies a.mu
// @Ensures True
func InRun(a *Account, n int) (i int) {
	return sort.Search(n, func(k int) bool {
		a.mu.Lock() // want `vego: precondition of Lock may not hold: ~held\(m\), in the function literal run by sort.Search`
		defer a.mu.Unlock()
		return k > 3
	})
}
