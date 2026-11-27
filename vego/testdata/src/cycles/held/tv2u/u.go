// Package tv2u is not verified: its M calls tv2v.Fire.
package tv2u

import "cycles/held/tv2v"

// T calls tv2v.Fire.
type T struct{}

func (T) M() int { return tv2v.Fire(1) }
