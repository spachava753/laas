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

// Short knows from the contract of sentinelclient.Short, which names
// io.EOF, that its error is not nil when ok is false.
//
// @Ensures err = nil <-> ok
func Short(ok bool) (err error) {
	return sentinelclient.Short(ok)
}
