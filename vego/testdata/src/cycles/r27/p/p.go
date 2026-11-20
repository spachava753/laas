// r27: a function value of the package held in an any, handed to another package.
package p

import (
	"cycles/r27/q"
	"cycles/r27/t"
)

// @Variant 0
// @Ensures True
func F() (n int) {
	var x any = t.Hook(h) // want `cannot\ verify\ F:\ h\ may\ call\ through\ a\ function\ value\ or\ an\ interface\ value,\ and\ code\ that\ a\ function\ value\ runs\ cannot\ do\ that\ yet:\ no\ contract\ of\ a\ f`
	return q.Run(x)
}

// h calls F.
//
// @Variant 1
//
// @Ensures True
func h() (n int) { return 0 + F() } // want `this\ call\ may\ not\ end:\ h\ calls\ F\ at\ p\.go:\d+:\d+,\ F\ hands\ x\ to\ q\.Run\(x\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ h`
