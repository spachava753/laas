// Package sentinelfarther imports neither sentinellib nor io, and uses a
// contract that names sentinellib.ErrGone.
package sentinelfarther

import "sentinelclient"

// Look fails when sentinelclient.Look does.
//
// @Ensures err = nil <-> k >= 0
func Look(k int) (err error) {
	_, err = sentinelclient.Look(k)
	return err
}
