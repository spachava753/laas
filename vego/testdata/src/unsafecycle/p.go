// Package unsafecycle hands code of the package to another package through
// an unsafe.Pointer, which the call graph follows as it follows an any: a
// cycle through it is found.
package unsafecycle

import (
	"unsafe"

	"unsafecycle/lib"
)

// hook holds F; nothing in t names F.
var hook func()

func init() { hook = F }

// F calls t, which hands lib the address of hook, and lib calls what hook
// holds, which is F: F never returns.
//
// @Ensures True
func F() {
	t() // want `t is trusted and calls back into F, so that this call ends cannot be proved; verify t instead of trusting it; the cycle: F calls t at p.go:\d+:\d+, t hands unsafe.Pointer\(&hook\) to lib.Run\(unsafe.Pointer\(&hook\)\) at p.go:\d+:\d+, which may run F`
}

func t() {
	lib.Run(unsafe.Pointer(&hook))
}

// G is the same with the function value handed over directly, which was
// found before.
//
// @Ensures True
func G() {
	u() // want `u is trusted and calls back into G`
}

var hook2 func()

func init() { hook2 = G }

func u() {
	lib.Call(hook2)
}

// counter is plain data.
var counter int

// count calls v, which hands lib the address of plain data. count is
// unexported and no value that anything can run, so no cycle goes through
// it, although what lib is handed can point to any value of the package.
//
// @Ensures True
func count() {
	v()
}

func v() {
	_ = lib.Read(unsafe.Pointer(&counter))
}

// Sink holds an address that code of another package reads.
type Sink struct {
	at unsafe.Pointer
}

func logTo(s *Sink, format string, args ...any) {}

// Log formats through a function that runs what s holds, which can be any
// code, after it has formatted the values, which formats claims.
//
// @Requires s != nil
// @Ensures True
func Log(s *Sink, n int) {
	logTo(s, "%d", n)
}
