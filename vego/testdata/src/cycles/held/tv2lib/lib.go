// Package tv2lib is trusted: Run and Run2 call M of what they are handed.
package tv2lib

import "cycles/held/tv2i"

// Run calls x.M().
func Run(x tv2i.J) int { return x.M() }

// Run2 calls x.M().
func Run2(x tv2i.J) int { return x.M() }
