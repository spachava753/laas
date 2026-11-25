// Package optlib declares a writer interface in a package whose build has
// optlibx, so that a member of O from optlibx is in its O when a trust file
// gives Sizer an entry.
package optlib

import (
	"io"

	"optlibx"
)

// W is an io.Writer.
type W interface {
	io.Writer
}

// Sizer is optlibx's, named so that the build holds it.
type Sizer = optlibx.Sizer
