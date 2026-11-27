// Package replacer wraps a *strings.Replacer in a type whose Replace calls
// the Replacer's. Package strings lets a Replacer hold only its own
// replacers, so the call runs no code of this package (F6 of the review of
// the design of F43). Before, the Replacer's field r, an interface with a
// method Replace, reached every Replace of the package, Rep.Replace among
// them, and Rep.Replace was a cycle.
package replacer

import "strings"

// Rep replaces through the Replacer it holds.
type Rep struct{ r *strings.Replacer }

// @Requires m.r != nil
// @Ensures True
func (m Rep) Replace(s string) (t string) { return m.r.Replace(s) }
