// Package heldcode hands trusted functions values that hold a
// sync/atomic.Pointer, which counts as a pointer to its type argument:
// it holds code exactly when that type does.
package heldcode

import "sync/atomic"

// Plain holds data only.
type Plain struct {
	N int
}

// Callback holds a function.
type Callback struct {
	F func()
}

// Cache holds a plain value behind an atomic pointer.
type Cache struct {
	current atomic.Pointer[Plain]
}

// Hooks holds a function behind an atomic pointer.
type Hooks struct {
	current atomic.Pointer[Callback]
}

func store(c *Cache) {}

func install(h *Hooks) {}

// Refresh hands over a cache, which holds no code.
//
// @Requires c != nil
// @Modifies c
// @Ensures True
func Refresh(c *Cache) {
	store(c)
}

// Install hands over hooks, which hold a function.
//
// @Requires h != nil
// @Modifies h
// @Ensures True
func Install(h *Hooks) {
	install(h) // want `cannot verify Install: h is passed to install, which is trusted, and is a value of type \*heldcode.Hooks, which is or holds a function value; install could run code through it that nobody has seen`
}
