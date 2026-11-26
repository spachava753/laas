package vego

import (
	"bufio"
	"bytes"
	"errors"
	"io"
	"math/rand/v2"
	"strings"
	"testing"
)

// countingReader yields a text in pieces of at most step bytes, counting
// what it yields, and can return its last bytes with io.EOF together.
type countingReader struct {
	text    []byte
	step    int
	withEOF bool
	read    int
}

func (r *countingReader) Read(p []byte) (int, error) {
	if r.read == len(r.text) {
		return 0, io.EOF
	}
	n := min(len(p), r.step, len(r.text)-r.read)
	copy(p, r.text[r.read:r.read+n])
	r.read += n
	if r.withEOF && r.read == len(r.text) {
		return n, io.EOF
	}
	return n, nil
}

// readerInputs returns the texts the harnesses of the inputs clauses read:
// empty lines, carriage returns, a last line without a newline, lines
// around the sizes of bufio's buffers, a token longer than a Scanner's
// buffer, and random texts.
func readerInputs() [][]byte {
	inputs := [][]byte{nil, []byte("\n"), []byte("\n\n\n"), []byte("a"), []byte("a\n"), []byte("a\r\nb\r\n"), []byte("a\nb"), []byte("\r\n\r")}
	for _, n := range []int{4095, 4096, 4097, 65535, 65536, 65537, 200000} {
		inputs = append(inputs, bytes.Repeat([]byte("x"), n), append(bytes.Repeat([]byte("y"), n), '\n', 'z'))
	}
	rng := rand.New(rand.NewPCG(39, 2))
	for range 200 {
		var b strings.Builder
		for range rng.IntN(300) {
			switch rng.IntN(5) {
			case 0:
				b.WriteByte('\n')
			case 1:
				b.WriteString("\r\n")
			default:
				b.WriteString(strings.Repeat("w", rng.IntN(50)))
			}
		}
		inputs = append(inputs, []byte(b.String()))
	}
	return inputs
}

// TestBufioConsumes holds the inputs clauses of the shipped entries of
// bufio (F39) against the real types. Scan: every Scan that returns true has
// consumed at least one more byte of what the reader yields, so after k true
// Scans the reader has yielded at least k bytes, and a Scanner over a reader
// of n bytes returns true at most n times, a token too long for its buffer
// included. ReadByte: a ReadByte with a nil error has read a byte more of
// what the reader yields.
func TestBufioConsumes(t *testing.T) {
	parallel(t)
	t.Run("Scan", func(t *testing.T) {
		for _, text := range readerInputs() {
			for _, step := range []int{1, 7, 4096, 1 << 20} {
				for _, withEOF := range []bool{false, true} {
					r := &countingReader{text: text, step: step, withEOF: withEOF}
					sc := bufio.NewScanner(r)
					k := 0
					for sc.Scan() {
						k++
						if r.read < k {
							t.Fatalf("%d bytes in steps of %d: after %d true Scans the reader yielded %d bytes", len(text), step, k, r.read)
						}
					}
					if k > len(text) {
						t.Fatalf("%d bytes in steps of %d: %d true Scans", len(text), step, k)
					}
					if err := sc.Err(); err != nil && !errors.Is(err, bufio.ErrTooLong) {
						t.Fatalf("%d bytes in steps of %d: %v", len(text), step, err)
					}
				}
			}
		}
	})
	t.Run("ReadByte", func(t *testing.T) {
		for _, text := range readerInputs() {
			for _, step := range []int{1, 7, 4096} {
				r := &countingReader{text: text, step: step, withEOF: step == 7}
				br := bufio.NewReader(r)
				k := 0
				for {
					if _, err := br.ReadByte(); err != nil {
						break
					}
					k++
					if r.read < k {
						t.Fatalf("%d bytes in steps of %d: after %d bytes read the reader yielded %d", len(text), step, k, r.read)
					}
				}
				if k != len(text) {
					t.Fatalf("%d bytes in steps of %d: ReadByte returned %d bytes", len(text), step, k)
				}
			}
		}
	})
}
