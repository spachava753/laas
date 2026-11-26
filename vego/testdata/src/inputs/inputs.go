// Package inputs reads until its inputs end, under the declaration of its
// trust file that they do (F39, part B).
package inputs

import (
	"bufio"
	"fmt"
	"io"
	"net/http"
	"os"
)

// CountLines counts and prints the lines of standard input.
//
// @Ensures n >= 0
func CountLines() (n int) {
	sc := bufio.NewScanner(os.Stdin)
	// @Snapshot l0 = unread(sc)
	// @Invariant ready(sc) And ends(sc) And 0 <= n And n <= l0 - unread(sc)
	// @Variant unread(sc)
	for sc.Scan() {
		fmt.Println(sc.Text())
		n++
	}
	return n
}

// CopyLines copies the lines of one file to another.
//
// @Requires |from| <= 4096 And |to| <= 4096
// @Ensures True
func CopyLines(from, to string) (err error) {
	in, err := os.Open(from)
	if err != nil {
		return err
	}
	defer in.Close()
	out, err := os.Create(to)
	if err != nil {
		return err
	}
	defer out.Close()
	sc := bufio.NewScanner(in)
	// @Invariant ready(sc) And ends(sc)
	// @Variant unread(sc)
	for sc.Scan() {
		if _, err := out.WriteString(sc.Text()); err != nil {
			return err
		}
	}
	return nil
}

// Drain reads a reader to its end.
//
// @Requires r != nil And ends(r)
// @Modifies r
// @Ensures total >= 0
func Drain(r io.Reader) (total int) {
	buf := make([]byte, 512)
	// @Snapshot l0 = unread(r)
	// @Invariant 0 <= total And total <= l0 - unread(r)
	// @Variant unread(r)
	for {
		n, err := r.Read(buf)
		total += n
		if err != nil {
			return total
		}
	}
}

// DrainBytes reads a reader to its end a byte at a time.
//
// @Requires r != nil And ends(r)
// @Modifies r
// @Ensures True
func DrainBytes(r io.Reader) {
	br := bufio.NewReader(r)
	// @Invariant ready(br) And ends(br)
	// @Variant unread(br)
	for {
		if _, err := br.ReadByte(); err != nil {
			return
		}
	}
}

// DrainStdin hands standard input to Drain.
//
// @Ensures True
func DrainStdin() {
	_ = Drain(os.Stdin)
}

// Skipped reads a byte and hands the Reader to skip, a verified function
// that lists it and says nothing of what it reads: the call forgets what
// is known of how much is left to read, as one that unreads would need.
//
// @Requires r != nil And ends(r)
// @Modifies r
// @Ensures True
func Skipped(r io.Reader) {
	br := bufio.NewReader(r)
	// @Invariant ready(br) And ends(br)
	// @Variant unread(br)
	for { // want `loop invariant may not be preserved: ends\(br\)` `loop variant may not decrease: unread\(br\)`
		if _, err := br.ReadByte(); err != nil {
			return
		}
		skip(br)
	}
}

// skip reads a byte.
//
// @Requires br != nil And ready(br)
// @Modifies br
// @Ensures ready(br')
func skip(br *bufio.Reader) {
	_, _ = br.ReadByte()
}

// Empty reads a file into an empty buffer, which may return no byte and no
// error (F3 of the design review).
//
// @Requires |path| <= 4096
// @Modifies buf
// @Ensures k = 0
func Empty(path string, buf []byte) (k int) {
	f, err := os.Open(path)
	if err != nil {
		return 0
	}
	defer f.Close()
	if _, err := f.Read(buf[:0]); err == nil {
		return 1 // want `postcondition may not hold: k = 0`
	}
	return 0
}

// SameFile reads a file and writes it through the same value.
//
// @Requires |path| <= 4096
// @Ensures True
func SameFile(path string) {
	f, err := os.Open(path)
	if err != nil {
		return
	}
	defer f.Close()
	sc := bufio.NewScanner(f)
	// @Invariant ready(sc) And ends(sc)
	// @Variant unread(sc)
	for sc.Scan() {
		_, _ = f.WriteString("x") // want `WriteString may write a file that is read under the declaration that inputs end`
	}
}

// AsWriter converts a file it reads to a writer.
//
// @Requires |path| <= 4096
// @Ensures True
func AsWriter(path string) {
	f, err := os.Open(path)
	if err != nil {
		return
	}
	defer f.Close()
	fmt.Fprintln(f, "x") // want `converting f to io.Writer, whose Write may write a file that is read under the declaration that inputs end`
}

// Poke writes through what it is handed, if it is a writer, which it may
// since its caller says the reader is not read under the declaration.
//
// @Requires r != nil And ~ends(r)
// @Modifies r
// @Ensures True
func Poke(r io.Reader) {
	if w, ok := r.(io.Writer); ok {
		_, _ = w.Write([]byte("x"))
	}
}

// PokeRead writes through a reader it reads, if it is a writer.
//
// @Requires r != nil And ends(r)
// @Modifies r
// @Ensures True
func PokeRead(r io.Reader) {
	if w, ok := r.(io.Writer); ok { // want `using the value of r.\(io.Writer\), whose Write, may write a file that is read under the declaration`
		_, _ = w.Write([]byte("x"))
	}
}

// DrainPoked reads a reader and hands it to Poke after each read.
//
// @Requires r != nil And ends(r)
// @Modifies r
// @Ensures True
func DrainPoked(r io.Reader) {
	buf := make([]byte, 512)
	// @Variant unread(r)
	for {
		_, err := r.Read(buf)
		if err != nil {
			return
		}
		Poke(r) // want `precondition of Poke may not hold: ~ends\(r\)`
	}
}

// AsFile takes the file out of a reader it reads and writes it.
//
// @Requires r != nil And ends(r)
// @Modifies r
// @Ensures True
func AsFile(r io.Reader) {
	if f, ok := r.(*os.File); ok {
		_, _ = f.Write([]byte("x")) // want `Write may write a file that is read under the declaration that inputs end`
	}
}

// AsFileUnread does the same with a reader that its caller says is not
// read under the declaration.
//
// @Requires r != nil And ~ends(r)
// @Ensures True
func AsFileUnread(r io.Reader) {
	if f, ok := r.(*os.File); ok {
		_, _ = f.Write([]byte("x"))
	}
}

// ones is a reader of the project that never ends: every Read returns a
// byte.
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

// Endless reads a reader of the project, which the declaration does not
// cover.
//
// @Ensures True
func Endless() {
	var r io.Reader = ones{}
	buf := make([]byte, 1)
	// @Variant unread(r)
	for { // want `loop variant may not decrease: unread\(r\)` `loop variant may be negative: unread\(r\)`
		if _, err := r.Read(buf); err != nil {
			return
		}
	}
}

// Zero scans with a Scanner that has no reader.
//
// @Ensures True
func Zero() {
	var sc bufio.Scanner
	sc.Scan() // want `precondition of Scan may not hold: ready\(s\)`
}

// Words keeps a field and a variable named as the words are.
type Words struct {
	unread int
	ends   bool
}

// Fields reads them.
//
// @Requires w != nil
// @Ensures r = w.unread
func Fields(w *Words) (r int) {
	ends := w.ends
	if ends {
		return w.unread
	}
	return w.unread
}

// Rewound reads a reader and has rewind seek it back after each read: a
// call that lists the reader forgets how much is left to read through it.
//
// @Requires r != nil And ends(r)
// @Modifies r
// @Ensures True
func Rewound(r io.Reader) {
	buf := make([]byte, 512)
	// @Variant unread(r)
	for { // want `loop variant may not decrease: unread\(r\)`
		if _, err := r.Read(buf); err != nil {
			return
		}
		rewind(r)
	}
}

func rewind(r io.Reader) {}

// Appended scans a file and hands it to appendTo, which writes it, after
// each line: a write to a file writes no memory, so only appendTo's
// requirement that the file is not read under the declaration refuses it.
//
// @Requires |path| <= 4096
// @Ensures True
func Appended(path string) {
	f, err := os.Open(path)
	if err != nil {
		return
	}
	defer f.Close()
	sc := bufio.NewScanner(f)
	// @Invariant ready(sc) And ends(sc)
	// @Variant unread(sc)
	for sc.Scan() {
		appendTo(f) // want `precondition of appendTo may not hold: ~ends\(f\)`
	}
}

// appendTo writes a byte to a file it is handed, which is not read under
// the declaration.
//
// @Requires f != nil And ~ends(f)
// @Ensures True
func appendTo(f *os.File) {
	_, _ = f.WriteString("x")
}

// Count reads the body of a request to its end and counts its bytes.
//
// @Requires w != nil And req != nil And req.Body != nil
// @Modifies w, req.Body
// @Ensures True
func Count(w http.ResponseWriter, req *http.Request) {
	body := req.Body
	buf := make([]byte, 512)
	total := 0
	// @Snapshot l0 = unread(body)
	// @Invariant 0 <= total And total <= l0 - unread(body)
	// @Variant unread(body)
	for {
		n, err := body.Read(buf)
		total += n
		if err != nil {
			break
		}
	}
	fmt.Fprintf(w, "%d\n", total)
}

// Fetched reads the body of a response, which the declaration does not
// cover in this feature.
//
// @Requires resp != nil And resp.Body != nil
// @Modifies resp.Body
// @Ensures True
func Fetched(resp *http.Response) {
	body := resp.Body
	buf := make([]byte, 512)
	// @Variant unread(body)
	for { // want `loop variant may not decrease: unread\(body\)` `loop variant may be negative: unread\(body\)`
		if _, err := body.Read(buf); err != nil {
			return
		}
	}
}

// DrainLimited drains at most a kilobyte of standard input.
//
// @Ensures True
func DrainLimited() {
	_ = Drain(io.LimitReader(os.Stdin, 1024))
}

// Config reads a whole file.
//
// @Requires |path| <= 4096
// @Ensures err = nil -> |data| <= 1000000000000
func Config(path string) (data []byte, err error) {
	data, err = os.ReadFile(path)
	if err != nil {
		return nil, fmt.Errorf("read %s: %w", path, err)
	}
	return data, nil
}

// All reads all of standard input.
//
// @Ensures True
func All() (n int, err error) {
	data, err := io.ReadAll(os.Stdin)
	return len(data), err
}

// AllOf reads all of a reader it is handed that ends.
//
// @Requires r != nil And ends(r)
// @Modifies r
// @Ensures err = nil -> |data| <= 1000000000000
func AllOf(r io.Reader) (data []byte, err error) {
	return io.ReadAll(r)
}

// Lines counts the lines of a reader with ReadString until io.EOF.
//
// @Requires rd != nil And ends(rd)
// @Modifies rd
// @Ensures n >= 0
func Lines(rd io.Reader) (n int, err error) {
	in := bufio.NewReader(rd)
	// @Snapshot l0 = unread(in)
	// @Invariant ready(in) And ends(in) And 0 <= n And n <= l0 - unread(in)
	// @Variant unread(in)
	for {
		line, err := in.ReadString('\n')
		if err == io.EOF {
			return n, nil
		}
		if err != nil {
			return n, err
		}
		if len(line) > 1 {
			n++
		}
	}
}

// Words reads words separated by spaces with ReadBytes.
//
// @Requires rd != nil And ends(rd)
// @Modifies rd
// @Ensures True
func Fields2(rd io.Reader) (total int) {
	in := bufio.NewReader(rd)
	// @Snapshot l0 = unread(in)
	// @Invariant ready(in) And ends(in) And 0 <= total And total <= l0 - unread(in)
	// @Variant unread(in)
	for {
		word, err := in.ReadBytes(' ')
		total += len(word)
		if err != nil {
			return total
		}
	}
}

// AllBuffer reads all of a reader the declaration does not cover.
//
// @Ensures True
func AllBuffer() {
	var r io.Reader = ones{}
	_, _ = io.ReadAll(r) // want `precondition of ReadAll may not hold: ends\(r\)`
}

// IsStdin says whether f is standard input (F11 of the review of step 2).
//
// @Requires f != nil
// @Ensures ~r
func IsStdin(f *os.File) (r bool) {
	return f == os.Stdin // want `postcondition may not hold: ~r`
}

// BothNil looks at a request's body and a reader.
//
// @Requires req != nil
// @Ensures x = 0
func BothNil(req *http.Request, r io.Reader) (x int) {
	if req.Body == nil && r == nil {
		return 1 // want `postcondition may not hold: x = 0`
	}
	return 0
}

// FromStdin asks whether a reader holds standard input.
//
// @Requires r != nil
// @Ensures x = 0
func FromStdin(r io.Reader) (x int) {
	if f, ok := r.(*os.File); ok && f == os.Stdin {
		return 1 // want `postcondition may not hold: x = 0`
	}
	return 0
}

// Sink holds a writer.
type Sink struct{ W io.Writer }

// put writes a byte to a writer it is handed.
//
// @Requires w != nil
// @Modifies w
// @Ensures True
func put(w io.Writer) (err error) {
	_, err = w.Write([]byte("x"))
	return err
}

// ToBoth writes to two writers through MultiWriter.
//
// @Requires a != nil And b != nil
// @Modifies a, b
// @Ensures True
func ToBoth(a, b io.Writer) (err error) {
	return put(io.MultiWriter(a, b))
}

// ToField writes to the writer of a sink.
//
// @Requires s != nil And s.W != nil
// @Modifies s.W
// @Ensures True
func ToField(s *Sink) (err error) {
	return put(s.W)
}

// maybe takes a writer that may be nil.
//
// @Ensures True
func maybe(w io.Writer) {
}

// ToNil hands it nil.
//
// @Ensures True
func ToNil() {
	maybe(nil)
}

// RewoundFile reads a file through an io.Reader and has rewindFile seek it
// back after each read (F12 of the review of step 2): a call that lists a
// value forgets what it has left, by its footprint.
//
// @Requires |name| <= 4096
// @Ensures True
func RewoundFile(name string) {
	f, err := os.Open(name)
	if err != nil {
		return
	}
	r := io.Reader(f)
	buf := make([]byte, 512)
	// @Invariant ends(r)
	// @Variant unread(r)
	for { // want `loop variant may not decrease: unread\(r\)`
		if _, err := r.Read(buf); err != nil {
			return
		}
		rewindFile(r)
	}
}

func rewindFile(r io.Reader) {
	if f, ok := r.(*os.File); ok {
		_, _ = f.Seek(0, io.SeekStart)
	}
}
