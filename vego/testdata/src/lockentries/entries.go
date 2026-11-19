// Package lockentries uses entries of its own for methods of sync.Mutex
// and sync.RWMutex.
package lockentries

import "sync"

// A primed state reads the memory where the pointer points, so an entry
// that writes nothing cannot change it.
//
// @Requires m != nil
// @Ensures True
func Try(m *sync.Mutex) {
	m.TryLock() // want `vego: the trusted contract of \(\*sync.Mutex\).TryLock \(vego-trusted.yaml:4\) cannot be used: its ensures "held\(m'\)" describes m' after the call, but nothing its modifies lists is memory that m' reads` `cannot verify Try: TryLock has a contract that could not be understood`
}

// @Requires m != nil And ~held(m)
// @Modifies m
// @Ensures held(m')
func Take(m *sync.Mutex) {
	m.Lock()
}

// A project entry for a method of package sync may name the fields of
// package sync, not those of internal/sync.
//
// @Requires rw != nil
// @Modifies rw
// @Ensures True
func Read(rw *sync.RWMutex) {
	rw.RLock() // want `rw.w.mu.state: state is an unexported field of internal/sync.Mutex, declared in package internal/sync, and a formula in package sync cannot name it` `cannot verify Read: RLock has a contract`
}

func each(n int, held func(i int) bool) bool { return held(n) }

func both(m *sync.Mutex, held func(i int) bool) bool { return held(0) }

// A function parameter named like a state is applied as the parameter.
//
// @Requires 0 <= n
// @Ensures ok <-> n > 0
func Each(n int) (ok bool) {
	return each(n, func(i int) bool { return i > 0 })
}

// A name that is both a parameter the contract applies and a state of the
// argument cannot be read either way.
//
// @Requires m != nil
// @Ensures True
func Both(m *sync.Mutex) {
	both(m, func(i int) bool { return true }) // want `held is both a function that the contract applies and a state of m; rename the parameter` `cannot verify Both`
}
