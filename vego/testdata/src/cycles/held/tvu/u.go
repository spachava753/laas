// Package tvu is not verified: its M calls tvv.Fire.
package tvu

import "cycles/held/tvv"

// T calls tvv.Fire.
type T struct{}

func (T) M() int { return tvv.Fire(1) }
