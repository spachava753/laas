package guide

import (
	"io"
	"os"
)

// The states of what a pointer points to (S0b of F34).

// @Requires f != nil
// @Modifies f
// @Ensures True
func CloseFile(f *os.File) {
	var c io.Closer = f
	c.Close() // want `precondition of c.Close may not hold: ~closed\(c\)`
}

// @Requires f != nil And ~closed(f)
// @Modifies f
// @Ensures closed(f')
func CloseOpenFile(f *os.File) {
	var c io.Closer = f
	c.Close()
}

// @Requires 0 < |name| <= 1000
// @Ensures True
func OpenThenCloseTwice(name string) {
	f, err := os.Open(name)
	if err != nil {
		return
	}
	var c io.Closer = f
	f.Close()
	c.Close() // want `precondition of c.Close may not hold: ~closed\(c\)`
}

// @Requires f != nil
// @Ensures True
func CopyFile(f *os.File) {
	g := *f // want `cannot verify CopyFile: Go copies a value of type os.File, here \(\*f\); the states of an os.File are changed by trusted methods and are about what it refers to, which a copy would share, so an os.File is never copied; hold it by pointer`
	_ = g
}
