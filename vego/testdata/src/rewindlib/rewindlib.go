// Package rewindlib stands for a module of another project whose values
// read a source and can rewind it (F17 of the review of step 5 of F39).
package rewindlib

// Rewinder makes a source yield again what it yielded.
type Rewinder interface {
	Rewind()
}

// Resetter has a method of the same name as Rewinder's, declared apart.
type Resetter interface {
	Rewind()
}

// File reads a slice of bytes.
type File struct {
	data []byte
	at   int
}

// Read reads what is left.
func (f *File) Read(p []byte) (n int, err error) {
	n = copy(p, f.data[f.at:])
	f.at += n
	return n, nil
}

// Rewind starts the reading again.
func (f *File) Rewind() { f.at = 0 }

// Restart starts the reading of f again.
func Restart(f *File) { f.at = 0 }
