// Package third reads from what it is handed; lib hands it on.
package third

import "io"

// @Requires r != nil
// @Modifies r
// @Ensures True
func Use(r io.Reader) {
	buf := make([]byte, 1)
	_, _ = r.Read(buf)
}
