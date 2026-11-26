// Package inputsrewound holds proofs that rest on a false entry, which
// rewinds a file and does not say so (see vego-trusted.yaml).
package inputsrewound

import (
	"errors"
	"io"
	"os"
)

// RewoundTwo reads a file through one conversion and rewinds it through
// another: the loop is proved to end only because the entry of rewindFile
// claims that it rewinds nothing.
//
// @Requires |name| <= 4096
// @Modifies rewound
// @Ensures True
func RewoundTwo(name string) {
	f, err := os.Open(name)
	if err != nil {
		return
	}
	r1, r2 := io.Reader(f), io.Reader(f)
	buf := make([]byte, 512)
	// @Invariant ends(r1)
	// @Variant unread(r1)
	for {
		if _, err := r1.Read(buf); err != nil {
			return
		}
		rewindFile(r2)
	}
}

// Inner reads r and rewinds x after each read.
//
// @Requires r != nil And x != nil And ends(r)
// @Modifies r, x, rewound
// @Ensures True
func Inner(r, x io.Reader) {
	buf := make([]byte, 512)
	// @Variant unread(r)
	for {
		if _, err := r.Read(buf); err != nil {
			return
		}
		rewindFile(x)
	}
}

// Outer hands Inner two conversions of one file.
//
// @Requires |name| <= 4096
// @Modifies rewound
// @Ensures True
func Outer(name string) {
	f, err := os.Open(name)
	if err != nil {
		return
	}
	Inner(io.Reader(f), io.Reader(f))
}

// errEndless is what rewindFile panics with once it has rewound more often
// than any file of the test could need, so that the test ends.
var errEndless = errors.New("rewound 1000 times: the loop does not end")

// rewound counts the calls of rewindFile.
var rewound int

func rewindFile(r io.Reader) {
	if rewound++; rewound > 1000 {
		panic(errEndless)
	}
	if f, ok := r.(*os.File); ok {
		_, _ = f.Seek(0, io.SeekStart)
	}
}
