// r19: a call of a method of an interface of another package with a shipped entry.
package r19

import "io"

// @Requires w != nil And |p| < 10
// @Ensures True
func F(w io.Writer, p []byte) (err error) {
	_, err = w.Write(p) // want `this\ call\ may\ not\ end:\ F\ calls\ w\.Write\(p\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ W\.Write,\ W\.Write\ calls\ F\ at\ p\.go:\d+:\d+`
	return err
}

type W struct{}

func (W) Write(p []byte) (int, error) { return 0, F(W{}, p) }
