// Package guideinputs holds the programs of the guide's section Inputs that
// end, under a trust file that declares them.
package guideinputs

import (
	"bufio"
	"fmt"
	"io"
	"os"
)

// LoadConfig reads a whole file.
//
// @Requires |name| <= 4096
// @Ensures True
func LoadConfig(name string) (data []byte, err error) {
	data, err = os.ReadFile(name)
	if err != nil {
		return nil, fmt.Errorf("load %s: %w", name, err)
	}
	return data, nil
}

// CountLines prints and counts the lines of standard input.
//
// @Ensures n >= 0
func CountLines() (n int) {
	sc := bufio.NewScanner(os.Stdin)
	// @Snapshot start = unread(sc)
	// @Invariant ready(sc) And ends(sc) And 0 <= n And n <= start - unread(sc)
	// @Variant unread(sc)
	for sc.Scan() {
		fmt.Println(sc.Text())
		n++
	}
	return n
}

// ScanAll prints every line of standard input, without the declaration's
// measure.
//
// @Ensures True
func ScanAll() {
	sc := bufio.NewScanner(os.Stdin)
	// @Invariant ready(sc)
	for sc.Scan() { // want `loop needs a // @Variant annotation to prove that it terminates`
		fmt.Println(sc.Text())
	}
}

// Words counts the words of a reader its caller hands it, separated by
// spaces.
//
// @Requires r != nil And ends(r)
// @Modifies r
// @Ensures n >= 0
func Words(r io.Reader) (n int, err error) {
	in := bufio.NewReader(r)
	// @Snapshot start = unread(in)
	// @Invariant ready(in) And ends(in) And 0 <= n And n <= start - unread(in)
	// @Variant unread(in)
	for {
		word, err := in.ReadString(' ')
		if len(word) > 1 {
			n++
		}
		if err == io.EOF {
			return n, nil
		}
		if err != nil {
			return n, err
		}
	}
}

// WordsOfStdin hands standard input to Words.
//
// @Ensures True
func WordsOfStdin() (n int) {
	n, _ = Words(os.Stdin)
	return n
}

// Slurp reads all of a reader.
//
// @Requires r != nil And ends(r)
// @Modifies r
// @Ensures True
func Slurp(r io.Reader) (n int, err error) {
	data, err := io.ReadAll(r)
	return len(data), err
}

// Append reads a file and writes a line to it through the same value.
//
// @Requires |name| <= 4096
// @Ensures True
func Append(name string) (err error) {
	f, err := os.Open(name)
	if err != nil {
		return err
	}
	defer f.Close()
	if _, err := io.ReadAll(f); err != nil {
		return err
	}
	_, err = f.WriteString("done\n") // want `WriteString may write a file that is read under the declaration that inputs end`
	return err
}

// Log writes a line to a file its caller says is not read under the
// declaration.
//
// @Requires f != nil And ~ends(f)
// @Ensures True
func Log(f *os.File, line string) (err error) {
	_, err = f.WriteString(line)
	return err
}

// Results counts the directories of a directory.
//
// @Requires |dir| <= 4096
// @Ensures n >= 0
func Results(dir string) (n int, err error) {
	entries, err := os.ReadDir(dir)
	if err != nil {
		return 0, err
	}
	// @Invariant 0 <= n And n <= i
	for i := range entries {
		if entries[i].IsDir() {
			n++
		}
	}
	return n, nil
}

// Copy copies a reader that ends to a writer.
//
// @Requires dst != nil And src != nil And ends(src)
// @Modifies dst, src
// @Ensures written >= 0
func Copy(dst io.Writer, src io.Reader) (written int, err error) {
	buf := make([]byte, 4096)
	// @Snapshot start = unread(src)
	// @Invariant 0 <= written And written <= start - unread(src)
	// @Variant unread(src)
	for {
		n, rerr := src.Read(buf)
		if n > 0 {
			m, werr := dst.Write(buf[:n])
			written += m
			if werr != nil {
				return written, werr
			}
		}
		if rerr == io.EOF {
			return written, nil
		}
		if rerr != nil {
			return written, rerr
		}
	}
}

// CopyOver hands Copy one value as the reader and the writer.
//
// @Requires rw != nil And ends(rw)
// @Modifies rw
// @Ensures True
func CopyOver(rw io.ReadWriter) {
	_, _ = Copy(rw, rw) // want `what is passed to Copy as src, a reader it requires to end, and as dst may be one value`
}

// ReadTwice reads a file, seeks it back to its start, and reads it again.
//
// @Requires |name| <= 4096
// @Ensures True
func ReadTwice(name string) (first, second []byte, err error) {
	f, err := os.Open(name)
	if err != nil {
		return nil, nil, err
	}
	if first, err = io.ReadAll(f); err != nil {
		return nil, nil, err
	}
	rewind(f) // want `the trusted contract of guideinputs.rewind .*cannot be used: it may make a reader yield again what it already yielded, through f`
	second, err = io.ReadAll(f)
	return first, second, err
}

func rewind(f *os.File) {
	_, _ = f.Seek(0, io.SeekStart)
}

// ones is a reader of the program that never ends.
type ones struct{}

// Read fills one byte.
//
// @Requires |p| > 0
// @Modifies p
// @Ensures n = 1 And err = nil
func (ones) Read(p []byte) (n int, err error) {
	p[0] = 1
	return 1, nil
}

// WordsOfOnes hands Words a reader of its own type.
//
// @Ensures True
func WordsOfOnes() (n int) {
	n, _ = Words(ones{}) // want `precondition of Words may not hold: ends\(r\)`
	return n
}
