// Package guidelocks holds the guide's mutex beside what it guards.
package guidelocks

import (
	"math"
	"sync"
)

// Page names a page.
type Page struct{ id int }

// @Invariant ~held(viewsMu) And 0 <= pageViews
var (
	viewsMu   sync.Mutex
	pageViews int
)

// View counts a page view under the lock.
//
// @Modifies viewsMu, pageViews
// @Ensures True
func View(p Page) {
	viewsMu.Lock()
	defer viewsMu.Unlock()
	addView()
}

// addView runs while View holds the lock.
//
// @Requires held(viewsMu)
// @Modifies pageViews
// @Ensures held(viewsMu)
func addView() {
	if pageViews < math.MaxInt {
		pageViews++
	}
}

// Views reads the count, which the invariant keeps not negative.
//
// @Modifies viewsMu
// @Ensures n >= 0
func Views(p Page) (n int) {
	viewsMu.Lock()
	n = pageViews
	viewsMu.Unlock()
	return n
}

// AddView requires the lock and is exported.
//
// @Requires held(viewsMu)
// @Modifies pageViews
// @Ensures True
func AddView(p Page) { // want `^vego: code outside the package's verified code can call AddView \(it is exported\), so it assumes ~held\(viewsMu\), a lock clause of the invariant of viewsMu, pageViews, on entry, which its Requires contradicts; keep a function that runs under the lock unexported, and do not use it as a value$`
	if pageViews < math.MaxInt {
		pageViews++
	}
}

// Hook is called with the lock held.
//
// @Ensures True
type Hook func(p Page)

// ViewThen calls h under the lock, which may be View.
//
// @Requires h != nil
// @Modifies viewsMu, pageViews
// @Ensures True
func ViewThen(h Hook, p Page) {
	viewsMu.Lock()
	defer viewsMu.Unlock()
	h(p) // want `^vego: invariant of viewsMu, pageViews may not hold before the call to h, which may assume it: ~held\(viewsMu\); it was not kept from entry, since held\(viewsMu\) may have changed: the call to viewsMu.Lock at locks.go:72:2 may write it$`
}
