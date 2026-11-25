// Package replacedc replaces the shipped entry of (io.Reader).Read alone by
// one that says nothing of n. The replacement is reported at the trust
// file, whatever the package looks up, and the shipped entry is used in
// its place, so no shipped entry rests on it unseen (ReadOne) and no other
// shipped entry draws a defect from it (Tee).
package replacedc

import (
	"bufio"
	"io"
)

// ReadOne reads a byte through a bufio.Reader over a reader its caller
// hands it. bufio panics on a negative count from Read, which the
// replacement allows and the shipped entry does not.
//
// @Requires r != nil
// @Modifies r
// @Ensures True
func ReadOne(r io.Reader) (b byte, err error) {
	return bufio.NewReader(r).ReadByte()
}

// Tee reads through a tee. With the replacement in force, io.Reader would
// have no usable contract, and the shipped entry of io.TeeReader would draw
// defects that blame its keeps and its asserts (F12).
//
// @Requires r != nil And w != nil
// @Modifies r, w
// @Ensures 0 <= n
func Tee(r io.Reader, w io.Writer) (n int, err error) {
	return io.TeeReader(r, w).Read(make([]byte, 8))
}
