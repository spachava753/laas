package locks

import "sync"

// Config is set up once.
type Config struct {
	once sync.Once
	size int
}

// Setup sets the size the first time it is called.
//
// @Requires c != nil And ~running(c.once)
// @Modifies c.once, c.size
// @Ensures ~running(c.once')
func (c *Config) Setup(n int) {
	c.once.Do(func() { c.size = n })
}

// Fresh sets up a Config it creates, which nobody has called Do on.
//
// @Ensures result != nil
func NewConfig(n int) (result *Config) {
	c := &Config{}
	c.once.Do(func() { c.size = n })
	return c
}

// SetupTwice calls Do twice on one Once, which waits for nothing.
//
// @Requires c != nil And ~running(c.once)
// @Modifies c.once, c.size
// @Ensures ~running(c.once')
func (c *Config) SetupTwice(n int) {
	c.Setup(n)
	c.Setup(n)
}

// Unsaid does not say that the caller is not inside Do on the Once, which
// an unverified caller could be, from the function it handed Do.
//
// @Requires c != nil
// @Modifies c.once, c.size
// @Ensures True
func (c *Config) Unsaid(n int) {
	c.once.Do(func() { c.size = n }) // want `vego: precondition of Do may not hold: ~running\(o\)`
}

// Inner calls Do on the same Once from the function Do runs, which waits
// for itself.
//
// @Requires c != nil And ~running(c.once)
// @Modifies c.once, c.size
// @Ensures True
func (c *Config) Inner(n int) {
	c.once.Do(func() {
		c.once.Do(func() { c.size = n }) // want `vego: precondition of Do may not hold: ~running\(o\), in the function literal run by c.once.Do` `vego: Do may modify c.once, which c.once.Do may write itself while it runs the function it is handed`
	})
}

// Two holds two Onces.
type Two struct {
	a, b sync.Once
	n    int
}

// Nested calls Do on another Once from the function Do runs. A run is
// verified in a state where what any run writes is forgotten, t.b among it,
// so whether the goroutine is inside Do on t.b is not known there.
//
// @Requires t != nil And ~running(t.a) And ~running(t.b)
// @Modifies t.a, t.b, t.n
// @Ensures True
func (t *Two) Nested() {
	t.a.Do(func() {
		t.b.Do(func() { t.n = 1 }) // want `vego: precondition of Do may not hold: ~running\(o\), in the function literal run by t.a.Do`
	})
}

// CopyOnce copies a Once while Do runs, and calls Do on the copy, which
// would wait for ever for the lock the copy holds.
//
// @Requires c != nil And ~running(c.once)
// @Modifies c.once
// @Ensures True
func (c *Config) CopyOnce() {
	c.once.Do(func() {
		o2 := c.once // want `cannot verify CopyOnce: c.once copies a sync.Once, which holds a state`
		o2.Do(func() {})
	})
}

// Unlisted does not list the Once that Do writes.
//
// @Requires c != nil And ~running(c.once)
// @Modifies c.size
// @Ensures True
func (c *Config) Unlisted(n int) {
	c.once.Do(func() { c.size = n }) // want `vego: Do may modify c.once, which Unlisted may not modify`
}
