// Package optionalwc imports nothing, so io is not in its build. The corpus
// trust file declares a state of WC and gives its methods entries; with a
// state, WC is no interface of O (F17 of the review of S1 of F35).
package optionalwc

// WC is written to and closed.
type WC interface {
	Write(p []byte) (n int, err error)
	Close() (err error)
}
