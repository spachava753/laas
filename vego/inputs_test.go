package vego

import (
	"bufio"
	"bytes"
	"errors"
	"fmt"
	"go/types"
	"io"
	"io/fs"
	"math/rand/v2"
	"os"
	"path/filepath"
	"slices"
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

// TestReadersEnd holds the entries of the functions that read until an
// input ends (F39) against the real functions: what io.ReadAll returns is
// what the reader yielded; each line of ReadString and ReadBytes with a nil
// error ends with the delimiter and is not empty, and the lines together
// are what the Reader consumed; os.ReadFile returns what a file holds, at
// most its size, gives a *PathError for a directory and for a name that
// does not exist, and reads a file whose size Stat reports as 0.
func TestReadersEnd(t *testing.T) {
	parallel(t)
	t.Run("ReadAll", func(t *testing.T) {
		for _, text := range readerInputs() {
			for _, step := range []int{1, 7, 4096, 1 << 20} {
				r := &countingReader{text: text, step: step, withEOF: step == 7}
				data, err := io.ReadAll(r)
				if err != nil || !bytes.Equal(data, text) || len(data) > r.read {
					t.Fatalf("%d bytes in steps of %d: %d bytes, %v", len(text), step, len(data), err)
				}
			}
		}
	})
	t.Run("ReadString", func(t *testing.T) {
		for _, text := range readerInputs() {
			for _, step := range []int{1, 7, 4096} {
				for _, size := range []int{16, 4096} {
					r := &countingReader{text: text, step: step, withEOF: step == 7}
					br := bufio.NewReaderSize(r, size)
					var got []byte
					for {
						line, err := br.ReadString('\n')
						got = append(got, line...)
						if err == nil && (len(line) == 0 || line[len(line)-1] != '\n') {
							t.Fatalf("%d bytes: a line %q with a nil error", len(text), line)
						}
						if len(got) > r.read {
							t.Fatalf("%d bytes: %d returned, %d yielded", len(text), len(got), r.read)
						}
						if err != nil {
							break
						}
					}
					if !bytes.Equal(got, text) {
						t.Fatalf("%d bytes in steps of %d: the lines are not the text", len(text), step)
					}
				}
			}
		}
	})
	t.Run("ReadBytes", func(t *testing.T) {
		for _, text := range readerInputs() {
			r := &countingReader{text: text, step: 7}
			br := bufio.NewReaderSize(r, 16)
			var got []byte
			for {
				word, err := br.ReadBytes(' ')
				got = append(got, word...)
				if err == nil && (len(word) == 0 || word[len(word)-1] != ' ') {
					t.Fatalf("%d bytes: a word %q with a nil error", len(text), word)
				}
				if err != nil {
					break
				}
			}
			if !bytes.Equal(got, text) {
				t.Fatalf("%d bytes: the words are not the text", len(text))
			}
		}
	})
	t.Run("Probed", func(t *testing.T) {
		// What io.ReadAll, ReadString, and ReadBytes run of the reader is
		// its Read alone, during the call: a keptReader refuses every
		// other method of lookedFor.
		for _, text := range readerInputs()[:60] {
			k := &keptLog{}
			done := k.enter()
			data, err := io.ReadAll(&keptReader{log: k, inner: bytes.NewReader(text)})
			br := bufio.NewReaderSize(&keptReader{log: k, inner: bytes.NewReader(text)}, 16)
			for err == nil {
				_, err = br.ReadString('\n')
			}
			br = bufio.NewReaderSize(&keptReader{log: k, inner: bytes.NewReader(text)}, 16)
			for err = nil; err == nil; {
				_, err = br.ReadBytes('\n')
			}
			done()
			k.check()
			if !bytes.Equal(data, text) {
				t.Fatalf("%d bytes: ReadAll of a kept reader returned %d", len(text), len(data))
			}
		}
	})
	t.Run("ReadFile", func(t *testing.T) {
		dir := t.TempDir()
		for i, text := range readerInputs()[:40] {
			path := filepath.Join(dir, fmt.Sprintf("f%d", i))
			if err := os.WriteFile(path, text, 0o600); err != nil {
				t.Fatal(err)
			}
			data, err := os.ReadFile(path)
			if err != nil || !bytes.Equal(data, text) {
				t.Fatalf("%d bytes: %d read, %v", len(text), len(data), err)
			}
		}
		for _, name := range []string{dir, filepath.Join(dir, "absent")} {
			_, err := os.ReadFile(name)
			var pathErr *fs.PathError
			if err == nil || !errors.As(err, &pathErr) {
				t.Fatalf("ReadFile(%s): %v, not a *PathError", name, err)
			}
		}
		if data, err := os.ReadFile("/proc/self/status"); err != nil || len(data) == 0 {
			t.Fatalf("ReadFile of a file whose size is 0: %d bytes, %v", len(data), err)
		}
	})
}

// inputsEntries are the shipped entries that speak of inputs that end, with
// the test that holds each against the real function: the harnesses of
// TestShippedContracts evaluate an entry on ground values, which ends and
// unread are not.
var inputsEntries = map[string]string{
	"os.ReadFile":                "TestReadersEnd/ReadFile",
	"io.ReadAll":                 "TestReadersEnd/ReadAll",
	"(*bufio.Reader).ReadString": "TestReadersEnd/ReadString",
	"(*bufio.Reader).ReadBytes":  "TestReadersEnd/ReadBytes",
}

// checkInputsEntry reads an entry of inputsEntries as a package that
// declares inputs reads it, and fails if it cannot be used there, or if it
// can be used where nothing is declared.
func checkInputsEntry(t *testing.T, pv *pkgVerifier, pkg *types.Package, key string) {
	if fn := contractOfKeyQuiet(pv, pkg, key); fn == nil || !slices.ContainsFunc(fn.defects, func(d string) bool { return strings.Contains(d, "returns only for an input that ends") }) {
		t.Errorf("the entry of %s can be used without the declaration that inputs end", key)
	}
	declared, _ := shippedVerifier(t)
	declared.projectTrust = parseTrustFile("vego-trusted.yaml", []byte("version: 1\ninputs:\n  bytes: 1TB\n  reason: a test\n"), false)
	if problems := declared.projectTrust.problems; len(problems) > 0 {
		t.Fatalf("the declaration of the test cannot be read: %v", problems)
	}
	contractOfKey(t, declared, pkg, key)
}

// contractOfKeyQuiet returns the shipped contract of a key, or nil.
func contractOfKeyQuiet(pv *pkgVerifier, pkg *types.Package, key string) *funcInfo {
	_, name, _ := splitFuncName(key)
	callee, ok := pkg.Scope().Lookup(name).(*types.Func)
	if receiver, method, isMethod := strings.Cut(strings.TrimPrefix(name, "(*"), ")."); isMethod {
		typeName := pkg.Scope().Lookup(receiver).(*types.TypeName)
		found, _, _ := types.LookupFieldOrMethod(types.NewPointer(typeName.Type()), true, pkg, method)
		callee, ok = found.(*types.Func)
	}
	if !ok {
		return nil
	}
	return pv.trustedContract(callee)
}
