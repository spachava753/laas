package q

import "cycles/r13c/p"

func Wire() int {
	s := p.NewS()
	s.Set(s.Hello)
	return s.Hello()
}
