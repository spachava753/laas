// Package stateover declares states for io.Closer in its trust file, which
// is refused; the shipped state closed stands.
package stateover

import "io"

// @Requires c != nil And ~closed(c)
// @Modifies c
// @Ensures closed(c')
func Shut(c io.Closer) {
	c.Close()
}

// @Requires c != nil And ~shut(c) // want `shut\(c\): c has type io.Closer, which has the states closed`
// @Ensures True
func Other(c io.Closer) {
}
