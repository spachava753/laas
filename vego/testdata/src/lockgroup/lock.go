// Package lockgroup keeps a counter beside the mutex that guards it, with
// ~held(mu) as a lock clause of the group's invariant (F32).
package lockgroup

import (
	"fmt"
	"io"
	"math"
	"strings"
	"sync"

	"letoutq"
)

// @Invariant ~held(mu) And 0 <= hits
var (
	mu   sync.Mutex
	hits int
)

// Hit counts a request under the lock.
//
// @Modifies mu, hits
// @Ensures True
func Hit() {
	mu.Lock()
	defer mu.Unlock()
	bump()
}

// bump runs while Hit holds the lock.
//
// @Requires held(mu)
// @Modifies hits
// @Ensures held(mu)
func bump() {
	if hits < math.MaxInt {
		hits++
	}
}

// Count reads the count, which the invariant keeps not negative.
//
// @Modifies mu
// @Ensures r >= 0
func Count() (r int) {
	mu.Lock()
	r = hits
	mu.Unlock()
	return r
}

// Unlocked calls bump without the lock.
//
// @Modifies hits
// @Ensures True
func Unlocked() {
	bump() // want `vego: precondition of bump may not hold: held\(mu\)`
}

// Notify is a hook another package may set.
//
// @Ensures True
type Notify func()

// HitNotify calls f under the lock, which may be Hit.
//
// @Requires f != nil
// @Modifies mu, hits
// @Ensures True
func HitNotify(f Notify) {
	mu.Lock()
	defer mu.Unlock()
	f() // want `vego: invariant of mu, hits may not hold before the call to f, which may assume it: ~held\(mu\)` `this call may not end: HitNotify calls f\(\) at lock.go:\d+:\d+, which may run HitTick, HitTick calls notify at lock.go:\d+:\d+, notify calls letoutq.Tick\(0\) at lock.go:\d+:\d+, which may run HitNotify; Tick reads`
}

// LeaveLocked returns with the lock held.
//
// @Modifies mu
// @Ensures True
func LeaveLocked() {
	mu.Lock()
} // want `vego: invariant of mu, hits may not hold on return: ~held\(mu\)`

// @Invariant ~held(lmu) And |log| <= 1000
var (
	lmu sync.Mutex
	log strings.Builder
)

// Note writes a word into the log under its lock, and the word through w
// outside it.
//
// @Requires w != nil
// @Modifies lmu, log, w
// @Ensures True
func Note(w io.Writer) {
	lmu.Lock()
	if log.Len() < 990 {
		log.WriteString("note ")
	}
	lmu.Unlock()
	fmt.Fprintln(w, "note")
}

// NoteUnder writes through w under the lock.
//
// @Requires w != nil
// @Modifies lmu, log, w
// @Ensures True
func NoteUnder(w io.Writer) {
	lmu.Lock()
	defer lmu.Unlock()
	fmt.Fprintln(w, "note") // want `vego: invariant of lmu, log may not hold before the call to Fprintln, which may assume it: ~held\(lmu\)`
}

// notify calls out of the package, to letoutq.Tick, which may run what
// code that is not verified kept there, as Hit.
//
// @Ensures True
func notify() { letoutq.Tick(0) } // want `this call may not end: notify calls letoutq.Tick\(0\) at lock.go:\d+:\d+, which may run HitTick, HitTick calls notify at lock.go:\d+:\d+; Tick reads`

// HitTick calls notify under the lock.
//
// @Modifies mu, hits
// @Ensures True
func HitTick() {
	mu.Lock()
	defer mu.Unlock()
	notify() // want `vego: invariant of mu, hits may not hold before the call to notify, which may assume it: ~held\(mu\)` `this call may not end: HitTick calls notify at lock.go:\d+:\d+, notify calls letoutq.Tick\(0\) at lock.go:\d+:\d+, which may run HitTick; Tick reads`
}

