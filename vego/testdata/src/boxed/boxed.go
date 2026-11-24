package boxed

import (
	"errors"
	"math"
	"strings"
	"sync"
)

var mu sync.Mutex

var hits int

// hit counts under the lock.
//
// @Requires ~held(mu)
// @Modifies mu, hits
// @Ensures ~held(mu')
func hit() {
	mu.Lock()
	defer mu.Unlock()
	if hits < math.MaxInt {
		hits++
	}
}

// Config is loaded.
type Config struct {
	n int
	m int
}

var cfg Config

// load sets n.
//
// @Requires c != nil
// @Modifies c.n
// @Ensures c.n' = 1
func load(c *Config) {
	c.n = 1
}

// setup loads cfg.
//
// @Modifies cfg
// @Ensures cfg.n' = 1
func setup() {
	load(&cfg)
}

// setM writes a field.
//
// @Modifies cfg.m
// @Ensures cfg.m' = 2 And cfg.n' = cfg.n
func setM() {
	cfg.m = 2
}

// both calls setM and keeps what load gave.
//
// @Modifies cfg
// @Ensures cfg.n' = 1 And cfg.m' = 2
func both() {
	setup()
	setM()
}

// unlisted writes without listing.
//
// @Ensures True
func unlisted() {
	cfg.n = 3 // want `vego: cfg\.n is assigned, which unlisted may not modify; list it in a // @Modifies clause`
}

// alias may write cfg through p.
//
// @Requires p != nil
// @Modifies p.n
// @Ensures cfg.m' = cfg.m
func alias(p *Config) {
	p.n = 5
}

// aliasWrong claims cfg.n is kept.
//
// @Requires p != nil
// @Modifies p.n
// @Ensures cfg.n' = cfg.n
func aliasWrong(p *Config) {
	p.n = 5
} // want `vego: postcondition may not hold: cfg\.n' = cfg\.n`

var sb strings.Builder

// note writes.
//
// @Requires |sb| <= 100
// @Modifies sb
// @Ensures |sb'| = |sb| + 1
func note() {
	sb.WriteString("x")
}

// twice locks twice.
//
// @Requires ~held(mu)
// @Modifies mu
// @Ensures True
func twice() {
	mu.Lock()
	mu.Lock() // want `vego: precondition of Lock may not hold: ~held\(m\)`
}

// loop writes cfg in a loop, which forgets what it writes.
//
// @Requires 0 <= k And k <= 100
// @Modifies cfg.n
// @Ensures cfg.m' = cfg.m
func loop(k int) {
	// @Invariant 0 <= i And i <= k
	// @Variant k - i
	for i := 0; i < k; i++ {
		cfg.n = i
	}
}

// literal writes cfg in a function literal called in place.
//
// @Modifies cfg.n
// @Ensures cfg.n' = 7
func literal() {
	func() { cfg.n = 7 }()
}

// keepsAcross reads cfg.n around a call that writes only m.
//
// @Modifies cfg.m
// @Ensures r = cfg.n
func keepsAcross() (r int) {
	r = cfg.n
	setM()
	return r
}

// lostAcross reads cfg.n around a call that may write it.
//
// @Requires p != nil
// @Modifies cfg.m, p.n
// @Ensures r = cfg.n'
func lostAcross(p *Config) (r int) {
	r = cfg.n
	alias(p)
	return r // want `vego: postcondition may not hold: r = cfg\.n'`
}

// readOld reads the value on entry in a body.
//
// @Modifies cfg.n
// @Ensures cfg.n' = 9 And r = cfg.n
func readOld() (r int) {
	r = cfg.n
	cfg.n = 9
	// @Assert old(cfg.n) = r
	return r
}

var count int

// n is an int whose address is taken.
var n int

// takeN takes the address of an int.
func takeN() *int { return &n }

// readN reads it.
//
// @Ensures True
func readN() (r int) {
	return n // want `vego: cannot verify readN: n has its address taken at boxed\.go:\d+; only a package-level variable of a struct type may have its address taken, since pointers to anything but a struct are not supported yet`
}

// Stamp is a struct with value methods.
type Stamp struct{ s int }

// Zero reports whether s is zero.
//
// @Ensures r <-> t.s = 0
func (t Stamp) Zero() (r bool) {
	return t.s == 0
}

var started = Stamp{s: 3}

// startedZero calls a value method on a fixed struct variable.
//
// @Ensures ~r
func startedZero() (r bool) {
	return started.Zero()
}

var errBusy = errors.New("busy")

// busy fails unless cfg.n is positive, which a caller can arrange: a
// sample gives cfg an allocation and its cells a value.
//
// @Modifies cfg.m
// @Ensures cfg.n > 0 -> err = nil And cfg.m' = 1
func busy() (err error) {
	if cfg.n <= 0 {
		return errBusy
	}
	cfg.m = 1
	return nil
}

// Visit is called by walk.
//
// @Ensures True
type Visit func()

// Touch writes cfg through its address, and is not verified.
func Touch() { load(&cfg) }

// walk calls f, which may be Touch.
//
// @Requires f != nil
// @Ensures True
func walk(f Visit) {
	f() // want `vego: f may modify cfg, which walk may not modify; code of this package that the call may run writes it; list it in a // @Modifies clause`
}

// walkListed lists what f may change.
//
// @Requires f != nil
// @Modifies cfg
// @Ensures True
func walkListed(f Visit) {
	f()
}

// loopKeeps claims cfg.n is left as it was, but the loop writes it.
//
// @Requires k = 3 And cfg.n = 0
// @Modifies cfg.n
// @Ensures cfg.n' = 0
func loopKeeps(k int) {
	// @Invariant 0 <= i And i <= k
	// @Variant k - i
	for i := 0; i < k; i++ {
		cfg.n = i + 1
	}
} // want `vego: postcondition may not hold: cfg\.n' = 0`
