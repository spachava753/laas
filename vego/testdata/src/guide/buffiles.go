package guide

import (
	"bufio"
	"fmt"
	"os"
)

// The program of the section "Reading and writing files" that writes
// through a buffer.

// @Requires |name| <= 4096
// @Ensures True
func BufferToFile(name string, line []byte) (err error) {
	f, cerr := os.Create(name)
	if cerr != nil {
		return fmt.Errorf("create %s: %w", name, cerr)
	}
	bw := bufio.NewWriter(f)
	if _, werr := bw.Write(line); werr != nil {
		f.Close()
		return werr
	}
	if ferr := bw.Flush(); ferr != nil {
		f.Close()
		return ferr
	}
	return f.Close()
}
