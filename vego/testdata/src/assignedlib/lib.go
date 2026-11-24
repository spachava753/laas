// Package assignedlib has an assigned variable whose address nothing in
// the package takes, so no pointer reaches it here (V1).
package assignedlib

// Config is a struct.
type Config struct{ N int }

// Cfg is assigned below.
var Cfg Config

// Reset assigns it, and is not verified.
func Reset() { Cfg = Config{} }

// Bump claims that a write through p leaves Cfg alone, which holds only
// while no pointer reaches Cfg.
//
// @Requires p != nil And Cfg.N < 100
// @Modifies p
// @Ensures r
func Bump(p *Config) (r bool) {
	a := Cfg.N
	p.N = a + 1
	return Cfg.N == a
}
