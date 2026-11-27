// Package hidden calls back into app; lib, which does not import it, calls
// its F by its symbol.
package hidden

import "cycles/runs/app"

// F calls app.Exported.
func F() { app.Exported() }
