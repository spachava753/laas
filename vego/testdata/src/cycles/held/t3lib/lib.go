// Package t3lib keeps a hook; it is trusted.
package t3lib

// Hook runs.
//
// @Ensures True
type Hook func() (n int)

var cur Hook

// Set keeps h; not verified, and verified code cannot call it.
func Set(h Hook) { cur = h }

// Current returns what Set kept.
func Current() Hook { return cur }
