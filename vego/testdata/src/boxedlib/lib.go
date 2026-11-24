// Package boxedlib keeps a mutex and a struct variable whose address is
// taken, which other packages cover through its state.
package boxedlib

import (
	"fmt"
	"io"
	"math"
	"strings"
	"sync"
)

var mu sync.Mutex

var hits int

// Hit counts under the lock, and asks its callers for what they cannot
// name.
//
// @Requires ~held(mu) // want `vego: the Requires clause ~held\(mu\) reads mu, a package-level variable that is not exported, and code of another package can call Hit, where no caller can name the condition or see it fail; test the value in the body instead`
// @Modifies mu, hits
// @Ensures True
func Hit() {
	mu.Lock()
	defer mu.Unlock()
	if hits < math.MaxInt {
		hits++
	}
}

// Config is set by Set.
type Config struct{ N int }

// Cfg is exported, and its address is taken.
var Cfg Config

// Set writes Cfg through its address.
//
// @Modifies Cfg
// @Ensures Cfg.N' = n
func Set(n int) {
	set(&Cfg, n)
}

// set writes what c points to.
//
// @Requires c != nil
// @Modifies c.N
// @Ensures c.N' = n
func set(c *Config, n int) {
	c.N = n
}

// Get reads Cfg.
//
// @Ensures r = Cfg.N
func Get() (r int) {
	return Cfg.N
}

// Buf is exported and written by its own methods, so its address is
// closed in this package.
var Buf strings.Builder

// NoteBuf keeps the length of Buf across the write through w, relying on
// no writer's footprint holding it.
//
// @Requires w != nil And |Buf| <= 100
// @Modifies Buf, w
// @Ensures |Buf'| = |Buf| + 1
func NoteBuf(w io.Writer) {
	Buf.WriteString("x")
	fmt.Fprint(w, "y")
}

// Zero reports whether c holds nothing.
//
// @Ensures r <-> c.N = 0
func (c Config) Zero() (r bool) {
	return c.N == 0
}
