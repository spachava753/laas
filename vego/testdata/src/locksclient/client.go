// Package locksclient calls contracts of another package that speak of the
// state of a mutex in a field it cannot name.
package locksclient

import "lockslib"

// Twice puts coins twice, holding the mutex throughout.
//
// @Requires v != nil And held(v.Mu) And 0 <= v.Coins <= 50
// @Modifies v.Coins
// @Ensures held(v.Mu') And v.Coins' = v.Coins + 2
func Twice(v *lockslib.Vault) {
	v.Put(1)
	v.Put(1)
}

// Unheld cannot put coins, since the caller may not hold the mutex.
//
// @Requires v != nil And 0 <= v.Coins <= 50
// @Modifies v.Coins
// @Ensures True
func Unheld(v *lockslib.Vault) {
	v.Put(1) // want `vego: precondition of Put may not hold: held\(v.Mu\)`
}
