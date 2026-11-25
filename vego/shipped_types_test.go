package vego

import (
	"bufio"
	"bytes"
	"compress/gzip"
	"context"
	"crypto/sha256"
	"errors"
	"go/types"
	"io"
	"math/rand"
	"net/http/httptest"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"sync"
	"testing"
	"testing/iotest"
	"text/tabwriter"
	"time"
)

// implementation is one type that a shipped entry for an interface method
// or a function type is tested against: a harness that makes a value of it
// and calls it on random arguments.
type implementation struct {
	name    string
	harness func(rng *rand.Rand) sample
}

// typeHarnesses lists, for each shipped entry of a type, implementations
// from the standard library. An entry for a type is a claim about every
// value of it, which no test can cover; several implementations each are
// what the test can do.
var typeHarnesses = map[string][]implementation{
	"(io.Writer).Write": {
		{"*bytes.Buffer", writerHarness(func() io.Writer { return new(bytes.Buffer) })},
		{"*strings.Builder", writerHarness(func() io.Writer { return new(strings.Builder) })},
		{"io.Discard", writerHarness(func() io.Writer { return io.Discard })},
		{"sha256", writerHarness(func() io.Writer { return sha256.New() })},
		{"*bufio.Writer of 16 bytes over a closed file", writerHarness(func() io.Writer { return bufio.NewWriterSize(closedFile(), 16) })},
		{"*os.File", writerHarness(func() io.Writer { return scratchFile() })},
		{"closed *os.File", writerHarness(func() io.Writer { return closedFile() })},
		{"iotest.TruncateWriter", writerHarness(func() io.Writer { return iotest.TruncateWriter(new(bytes.Buffer), 20) })},
		{"*tabwriter.Writer", writerHarness(func() io.Writer { return tabwriter.NewWriter(new(bytes.Buffer), 4, 8, 1, ' ', 0) })},
		{"io.MultiWriter", writerHarness(func() io.Writer { return io.MultiWriter(new(bytes.Buffer), sha256.New()) })},
		{"*io.PipeWriter with its reader closed", writerHarness(func() io.Writer {
			r, w := io.Pipe()
			r.Close()
			return w
		})},
		{"*gzip.Writer", writerHarness(func() io.Writer { return gzip.NewWriter(new(bytes.Buffer)) })},
		{"any writer the documentation allows", func(rng *rand.Rand) sample {
			return writerHarness(func() io.Writer { return anyWriter{rng} })(rng)
		}},
	},
	"(io.StringWriter).WriteString": {
		{"*bytes.Buffer", stringWriterHarness(func() io.StringWriter { return new(bytes.Buffer) })},
		{"*strings.Builder", stringWriterHarness(func() io.StringWriter { return new(strings.Builder) })},
		{"*bufio.Writer of 16 bytes over a closed file", stringWriterHarness(func() io.StringWriter { return bufio.NewWriterSize(closedFile(), 16) })},
		{"*bufio.Writer of 16 bytes over a buffer", stringWriterHarness(func() io.StringWriter { return bufio.NewWriterSize(new(bytes.Buffer), 16) })},
		{"*bufio.Writer of 16 bytes over a truncating writer", stringWriterHarness(func() io.StringWriter {
			return bufio.NewWriterSize(iotest.TruncateWriter(new(bytes.Buffer), 20), 16)
		})},
		{"*os.File", stringWriterHarness(func() io.StringWriter { return scratchFile() })},
		{"closed *os.File", stringWriterHarness(func() io.StringWriter { return closedFile() })},
		{"io.MultiWriter", stringWriterHarness(func() io.StringWriter {
			return io.MultiWriter(new(bytes.Buffer), sha256.New()).(io.StringWriter)
		})},
		{"io.MultiWriter over a closed file", stringWriterHarness(func() io.StringWriter {
			return io.MultiWriter(new(strings.Builder), closedFile()).(io.StringWriter)
		})},
		{"*httptest.ResponseRecorder", stringWriterHarness(func() io.StringWriter { return httptest.NewRecorder() })},
		{"any string writer the entry allows", func(rng *rand.Rand) sample {
			return stringWriterHarness(func() io.StringWriter { return anyWriter{rng} })(rng)
		}},
	},
	"(io.Reader).Read": {
		{"*bytes.Reader", readerHarness(func(data []byte) io.Reader { return bytes.NewReader(data) })},
		{"*strings.Reader", readerHarness(func(data []byte) io.Reader { return strings.NewReader(string(data)) })},
		{"*bufio.Reader", readerHarness(func(data []byte) io.Reader { return bufio.NewReaderSize(bytes.NewReader(data), 16) })},
		{"io.LimitReader", readerHarness(func(data []byte) io.Reader { return io.LimitReader(bytes.NewReader(data), int64(len(data)/2)) })},
		{"io.MultiReader", readerHarness(func(data []byte) io.Reader {
			return io.MultiReader(bytes.NewReader(data[:len(data)/2]), bytes.NewReader(data[len(data)/2:]))
		})},
		{"iotest.OneByteReader", readerHarness(func(data []byte) io.Reader { return iotest.OneByteReader(bytes.NewReader(data)) })},
		{"iotest.HalfReader", readerHarness(func(data []byte) io.Reader { return iotest.HalfReader(bytes.NewReader(data)) })},
		{"iotest.DataErrReader", readerHarness(func(data []byte) io.Reader { return iotest.DataErrReader(bytes.NewReader(data)) })},
		{"iotest.TimeoutReader", readerHarness(func(data []byte) io.Reader { return iotest.TimeoutReader(bytes.NewReader(data)) })},
		{"iotest.ErrReader", readerHarness(func([]byte) io.Reader { return iotest.ErrReader(errors.New("broken")) })},
		{"*os.File", readerHarness(func(data []byte) io.Reader {
			f := scratchFile()
			if _, err := f.Write(data); err != nil {
				panic(err)
			}
			if _, err := f.Seek(0, io.SeekStart); err != nil {
				panic(err)
			}
			return f
		})},
		{"*gzip.Reader", readerHarness(func(data []byte) io.Reader {
			var packed bytes.Buffer
			w := gzip.NewWriter(&packed)
			w.Write(data)
			w.Close()
			r, err := gzip.NewReader(&packed)
			if err != nil {
				panic(err)
			}
			return r
		})},
		{"any reader the documentation allows", func(rng *rand.Rand) sample {
			return readerHarness(func([]byte) io.Reader { return anyReader{rng} })(rng)
		}},
	},
	"(context.Context).Err": {
		{"context.Background", contextHarness(func(*rand.Rand) (context.Context, func()) { return context.Background(), func() {} })},
		{"context.TODO", contextHarness(func(*rand.Rand) (context.Context, func()) { return context.TODO(), func() {} })},
		{"context.WithCancel", contextHarness(func(rng *rand.Rand) (context.Context, func()) {
			ctx, cancel := context.WithCancel(randomParent(rng))
			if rng.Intn(2) == 0 {
				cancel()
			}
			return ctx, cancel
		})},
		{"context.WithTimeout", contextHarness(func(rng *rand.Rand) (context.Context, func()) {
			timeout := time.Hour
			if rng.Intn(2) == 0 {
				timeout = 0
			}
			return context.WithTimeout(randomParent(rng), timeout)
		})},
		{"context.WithDeadline in the past", contextHarness(func(rng *rand.Rand) (context.Context, func()) {
			return context.WithDeadline(randomParent(rng), time.Now().Add(-time.Second))
		})},
		{"context.WithValue", contextHarness(func(rng *rand.Rand) (context.Context, func()) {
			return context.WithValue(randomParent(rng), contextKey{}, 1), func() {}
		})},
		{"context.WithoutCancel", contextHarness(func(rng *rand.Rand) (context.Context, func()) {
			return context.WithoutCancel(randomParent(rng)), func() {}
		})},
		{"context.WithCancelCause", contextHarness(func(rng *rand.Rand) (context.Context, func()) {
			ctx, cancel := context.WithCancelCause(randomParent(rng))
			if rng.Intn(2) == 0 {
				cancel(errors.New("cause"))
			}
			return ctx, func() { cancel(nil) }
		})},
		{"context.WithTimeoutCause", contextHarness(func(rng *rand.Rand) (context.Context, func()) {
			return context.WithTimeoutCause(randomParent(rng), 0, errors.New("cause"))
		})},
		{"any context the documentation allows", contextHarness(func(rng *rand.Rand) (context.Context, func()) {
			return anyContext{rng}, func() {}
		})},
	},
	"context.CancelFunc": {
		{"of context.WithCancel", cancelHarness(func(parent context.Context) context.CancelFunc {
			_, cancel := context.WithCancel(parent)
			return cancel
		})},
		{"of context.WithTimeout", cancelHarness(func(parent context.Context) context.CancelFunc {
			_, cancel := context.WithTimeout(parent, time.Hour)
			return cancel
		})},
		{"of context.WithDeadline", cancelHarness(func(parent context.Context) context.CancelFunc {
			_, cancel := context.WithDeadline(parent, time.Now().Add(-time.Second))
			return cancel
		})},
		{"of context.WithTimeoutCause", cancelHarness(func(parent context.Context) context.CancelFunc {
			_, cancel := context.WithTimeoutCause(parent, time.Hour, errors.New("cause"))
			return cancel
		})},
		{"of context.WithDeadlineCause", cancelHarness(func(parent context.Context) context.CancelFunc {
			_, cancel := context.WithDeadlineCause(parent, time.Now().Add(time.Hour), errors.New("cause"))
			return cancel
		})},
		{"one that does nothing", cancelHarness(func(context.Context) context.CancelFunc { return func() {} })},
	},
}

// The implementations below do, at random, everything the documentation
// of their interface allows, so that an entry that claims more than the
// documentation fails even where the standard library happens to meet it.

// oddError is an error of a type of its own.
type oddError struct{ n int }

func (e oddError) Error() string { return "odd" }

// anyWriter writes nothing of p and reports any count, with an error of
// any type whenever the count is short, and sometimes when it is not.
type anyWriter struct{ rng *rand.Rand }

func (w anyWriter) Write(p []byte) (n int, err error) {
	n = w.rng.Intn(len(p) + 1)
	switch {
	case n == len(p) && w.rng.Intn(2) == 0:
		return n, nil
	case w.rng.Intn(2) == 0:
		return n, oddError{n}
	}
	return n, io.ErrShortWrite
}

// WriteString does what Write does: any count up to |s|, with an error
// whenever it is short, which is what the entry of (io.StringWriter).
// WriteString allows (D1 of F35).
func (w anyWriter) WriteString(s string) (n int, err error) {
	return w.Write(make([]byte, len(s)))
}

// anyReader uses all of p as scratch and reads any count, 0 with no error
// included, with or without an error of any type.
type anyReader struct{ rng *rand.Rand }

func (r anyReader) Read(p []byte) (n int, err error) {
	r.rng.Read(p)
	n = r.rng.Intn(len(p) + 1)
	switch r.rng.Intn(4) {
	case 0:
		return n, io.EOF
	case 1:
		return n, oddError{n}
	case 2:
		return n, errors.New("broken")
	}
	return n, nil
}

// anyContext is done or not at random, and says why with either error.
type anyContext struct{ rng *rand.Rand }

func (c anyContext) Deadline() (time.Time, bool) { return time.Time{}, false }

func (c anyContext) Done() <-chan struct{} { return nil }

func (c anyContext) Value(key any) any { return nil }

func (c anyContext) Err() error {
	return []error{nil, context.Canceled, context.DeadlineExceeded}[c.rng.Intn(3)]
}

// randomBytes returns up to 64 random bytes.
func randomBytes(rng *rand.Rand) []byte {
	data := make([]byte, rng.Intn(65))
	rng.Read(data)
	return data
}

// writerHarness calls Write of a new writer on random bytes, after up to
// three earlier writes, so that a writer that buffers or fails late is
// reached in each state.
func writerHarness(open func() io.Writer) func(rng *rand.Rand) sample {
	return func(rng *rand.Rand) sample {
		w := open()
		for range rng.Intn(4) {
			w.Write(randomBytes(rng))
		}
		p := randomBytes(rng)
		before := snapshot(p)
		n, err := w.Write(p)
		if f, ok := w.(*os.File); ok {
			f.Close()
		}
		return sample{before: before, after: []any{p}, results: []any{n, err}}
	}
}

// stringWriterHarness calls WriteString of a new string writer with a
// random string, after up to three earlier writes. The servers' writers of
// net/http are run by the harness of io.WriteString (shipped_http_test.go).
func stringWriterHarness(open func() io.StringWriter) func(rng *rand.Rand) sample {
	return func(rng *rand.Rand) sample {
		w := open()
		for range rng.Intn(4) {
			w.WriteString(string(randomBytes(rng)))
		}
		s := string(randomBytes(rng))
		n, err := w.WriteString(s)
		if f, ok := w.(*os.File); ok {
			f.Close()
		}
		return sample{before: []any{s}, after: []any{s}, results: []any{n, err}}
	}
}

// readerHarness calls Read of a new reader over random data on a slice of
// random length, after up to three earlier reads. The slices are never
// empty: the entry requires that, and iotest.DataErrReader does not return
// from a read into an empty slice while it holds data.
func readerHarness(open func(data []byte) io.Reader) func(rng *rand.Rand) sample {
	return func(rng *rand.Rand) sample {
		r := open(randomBytes(rng))
		for range rng.Intn(4) {
			r.Read(make([]byte, 1+rng.Intn(16)))
		}
		p := make([]byte, 1+rng.Intn(64))
		rng.Read(p)
		before := slices.Clone(p)
		n, err := r.Read(p)
		if f, ok := r.(*os.File); ok {
			f.Close()
		}
		return sample{before: []any{before}, after: []any{p}, results: []any{n, err}}
	}
}

type contextKey struct{}

// randomParent returns a context to derive one from: one that is never
// done, one that was canceled, or one whose deadline has passed.
func randomParent(rng *rand.Rand) context.Context {
	switch rng.Intn(3) {
	case 0:
		ctx, cancel := context.WithCancel(context.Background())
		cancel()
		return ctx
	case 1:
		ctx, cancel := context.WithDeadline(context.Background(), time.Now().Add(-time.Second))
		cancel()
		return ctx
	}
	return context.Background()
}

// contextHarness calls Err of a new context, and then releases it.
func contextHarness(open func(rng *rand.Rand) (context.Context, func())) func(rng *rand.Rand) sample {
	return func(rng *rand.Rand) sample {
		ctx, release := open(rng)
		err := ctx.Err()
		release()
		return sample{results: []any{err}}
	}
}

// cancelHarness calls a new CancelFunc twice at once from two goroutines,
// and once more after that, which must do nothing.
func cancelHarness(open func(parent context.Context) context.CancelFunc) func(rng *rand.Rand) sample {
	return func(rng *rand.Rand) sample {
		cancel := open(randomParent(rng))
		var both sync.WaitGroup
		for range 2 {
			both.Go(cancel)
		}
		both.Wait()
		cancel()
		return sample{}
	}
}

// scratchFile returns a new file in the scratch directory.
func scratchFile() *os.File {
	f, err := os.CreateTemp(scratch, "w")
	if err != nil {
		panic(err)
	}
	return f
}

// closedFile returns a file that is closed, so that writing to it fails.
func closedFile() *os.File {
	f, err := os.Create(filepath.Join(scratch, "closed"))
	if err != nil {
		panic(err)
	}
	f.Close()
	return f
}

// shippedTypeContract returns the contract that a shipped entry gives the
// method of an interface or the function type that name, as splitFuncName
// gives it, names in pkg, or nil if it names neither.
func shippedTypeContract(pv *pkgVerifier, pkg *types.Package, name string) *funcInfo {
	receiver, method, isMethod := strings.Cut(strings.TrimPrefix(name, "("), ").")
	if !isMethod {
		if typeName, ok := pkg.Scope().Lookup(name).(*types.TypeName); ok {
			return pv.entryFuncType(typeName)
		}
		return nil
	}
	typeName, ok := pkg.Scope().Lookup(receiver).(*types.TypeName)
	if !ok || !types.IsInterface(typeName.Type()) {
		return nil
	}
	found, _, _ := types.LookupFieldOrMethod(typeName.Type(), false, pkg, method)
	if declared, ok := found.(*types.Func); ok {
		return pv.entryMethod(declared)
	}
	return nil
}

// checkTypeContract runs the shipped entry of a type against each of its
// implementations.
func checkTypeContract(t *testing.T, pv *pkgVerifier, key string, fn *funcInfo) {
	implementations := typeHarnesses[key]
	if len(implementations) < 3 {
		t.Fatalf("%s is tested against %d implementations; add at least three to typeHarnesses", key, len(implementations))
	}
	for _, defect := range fn.defects {
		t.Errorf("contract cannot be used: %s", defect)
	}
	// A condition needs a call that meets it among all the
	// implementations, not in each: context.Background is never canceled.
	met := coverage{}
	for _, impl := range implementations {
		t.Run(impl.name, func(t *testing.T) {
			checkContract(t, pv, key, fn, impl.harness, met)
		})
	}
	met.require(t, fn)
}
