// r31: a literal made by verified code, held in an any, run by another package.
package p

import (
	"cycles/r31/q"
	"cycles/r31/t"
)

// @Ensures True
func F() (n int) {
	var x any = t.Hook(func() (m int) { return F() }) // want `cannot\ verify\ F:\ the\ function\ literal\ used\ as\ a\ value\ calls\ F,\ which\ may\ call\ through\ a\ function\ value\ or\ an\ interface\ value:\ F\ hands\ x\ to\ q\.Run\(x\),\ w`
	return q.Run(x)
}
