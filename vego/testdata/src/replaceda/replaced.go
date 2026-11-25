// Package replaceda replaces two shipped entries that other shipped entries
// rest on: (io.Writer).Write by the same entry, which is accepted, and
// (io.Reader).Read by one that promises more, which is reported at the
// trust file, and the shipped entry is used in its place.
package replaceda

import (
	"bufio"
	"io"
)

// WriteBoth writes through a buffered writer over w under the replacement
// of Write that is the shipped entry.
//
// @Requires w != nil
// @Modifies w
// @Ensures True
func WriteBoth(w io.Writer) (err error) {
	bw := bufio.NewWriter(w)
	if _, err = bw.Write([]byte("a\n")); err != nil {
		return err
	}
	return bw.Flush()
}

// ReadTen reads ten bytes through a reader limited to one. The replacement
// of Read says that a read fills its buffer or fails, and the result of
// io.LimitReader cuts the buffer, so its Read does not meet it, while the
// shipped entry of LimitReader vouches that it does. Under the shipped
// entry of Read, which stands, its contract is not proved.
//
// @Requires r != nil
// @Modifies r
// @Ensures n = 10 Or err != nil
func ReadTen(r io.Reader) (n int, err error) {
	lr := io.LimitReader(r, 1)
	return lr.Read(make([]byte, 10)) // want `postcondition may not hold: n = 10 Or err != nil`
}
