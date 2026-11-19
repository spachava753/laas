package locks

import "sync"

// The private fields of a mutex differ between versions of Go, and other
// goroutines change them, so a formula outside package sync cannot name
// them.
//
// @Requires a != nil And a.mu.mu.state = 0 // want `vego: in Requires annotation: a.mu.mu: mu is an unexported field of sync.Mutex, declared in package sync, and a formula in package locks cannot name it; sync.Mutex has the state held`
// @Modifies a.balance
// @Ensures True
func Private(a *Account) {
	a.balance = 1
}

// @Requires rw != nil And rw.w.mu.state = 0 // want `rw.w: w is an unexported field of sync.RWMutex`
// @Ensures True
func PrivateRW(rw *sync.RWMutex) {
}

// @Requires a != nil And open(a.mu) // want `a.mu is a sync.Mutex; name one of its fields`
// @Ensures True
func Unknown(a *Account) {
}

// @Requires a != nil And rheld(a.mu) // want `rheld\(a.mu\): a.mu is a sync.Mutex, which has the states held`
// @Ensures True
func Other(a *Account) {
}

// @Requires held(n) // want `held\(n\): n is a int, which has no states`
// @Ensures True
func Number(n int) {
}

// @Requires held(m)
// @Ensures held(m') // want `m is passed by value`
func ByValue(m sync.Mutex) {
}
