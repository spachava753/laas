// Package sibtlib keeps a hook; it is trusted.
package sibtlib

import "cycles/held/sibti"

var cur sibti.Hook

// Set keeps h; not verified.
func Set(h sibti.Hook) { cur = h }

// Current returns what Set kept.
func Current() sibti.Hook { return cur }
