package q

import "cycles/r26/p"

// Outer implements p.I and promotes p.T's Hello.
type Outer struct{ p.T }

func (Outer) Foo() int { return 0 }

func Wire() int {
	o := &Outer{}
	o.X = o
	return p.F(o)
}
