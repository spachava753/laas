// Package lockgrouprw keeps a sync.RWMutex in a group with what it guards
// (F20 of the review of step 4 of F32).
package lockgrouprw

import "sync"

// @Invariant ~held(rw) And ~rheld(rw) And 0 <= reads
var (
	rw    sync.RWMutex
	reads int
)

// Read takes a read lock.
//
// @Modifies rw
// @Ensures r >= 0
func Read() (r int) {
	rw.RLock()
	r = reads
	rw.RUnlock()
	return r
}

// Upgrade takes the write lock while it holds the read lock, which waits
// for ever.
//
// @Modifies rw, reads
// @Ensures True
func Upgrade() {
	rw.RLock()
	rw.Lock() // want `vego: precondition of Lock may not hold: ~rheld\(rw\)`
	reads = 0
	rw.Unlock()
	rw.RUnlock()
}

// Lonely writes reads under the write lock, and its invariant names reads
// only through a helper.
//
// @Modifies rw, reads
// @Ensures True
func Lonely() {
	rw.Lock()
	reads = 0
	rw.Unlock()
}
