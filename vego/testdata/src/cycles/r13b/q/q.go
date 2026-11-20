package q

import "cycles/r13b/p"

func Wire() int {
	x := p.New()
	x.Set(x.Hello)
	return x.Hello()
}
