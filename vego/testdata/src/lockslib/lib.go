// Package lockslib publishes contracts that speak of the state of a mutex.
package lockslib

import "sync"

// Vault is guarded by its mutex.
type Vault struct {
	Mu    sync.Mutex
	Coins int
	count int
}

// Put adds coins while the caller holds the mutex. Its contract names an
// unexported field of this package, which it may, also where it is read in
// another package.
//
// @Requires v != nil And held(v.Mu) And 0 <= n <= 100 And 0 <= v.Coins <= 100
// @Modifies v.Coins
// @Ensures held(v.Mu') And v.Coins' = v.Coins + n And v.count' = v.count
func (v *Vault) Put(n int) {
	v.Coins += n
}

// Held says whether the caller holds the mutex of the vault, as its
// contract does.
//
// @Requires v != nil
// @Ensures ok = held(v.Mu)
func Held(v *Vault) (ok bool) {
	return true // want `vego: postcondition may not hold: ok = held\(v.Mu\)`
}
