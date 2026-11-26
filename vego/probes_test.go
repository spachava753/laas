package vego

import (
	"context"
	"fmt"
	"io"
	"net/http"
	"os"
	"path/filepath"
	"reflect"
	"slices"
	"strings"
	"testing"
	"time"
)

// An entry that lists a parameter under runs or keeps claims that the
// function calls through an interface value nothing that the parameter
// holds but the methods of the interfaces its type reaches, and what it
// lists under asserts (asserts.go). The harnesses of the shipped entries
// hold that claim by handing each function values that also have every
// method the standard library is known to look for by a type assertion,
// lookedFor, and the methods that a search of the function's source for
// assertions shows; each of them fails the test when it is called, unless
// the entry declares it. An entry that asserts and does not say so then
// fails in the run everybody makes.

// lookedFor are the methods that the standard library finds by a type
// assertion on a value it is handed: those of fmt.Stringer, error,
// fmt.Formatter, fmt.GoStringer, io.StringWriter, io.ReaderFrom,
// io.WriterTo, the Unwrap, Is, and As of package errors, the Timeout and
// Temporary of net and os, io.Closer, and the Flush of bufio and
// http.Flusher.
var lookedFor = []string{
	"String", "Error", "Format", "GoString", "WriteString", "ReadFrom", "WriteTo",
	"Unwrap", "Is", "As", "Timeout", "Temporary", "Close", "Flush",
}

// probedBy names, for each shipped entry that lists under runs or keeps a
// parameter that is not a function, the harness whose values have the
// methods of lookedFor. The entries whose parameters under runs are
// functions, with a contract under calls, need none: a function value has
// no methods, and converted to an interface its dynamic type is the
// parameter's unnamed function type, so no assertion finds anything on it.
// Their type parameters, under asserts, are held by TestGenericEntries.
var probedBy = map[string]string{
	"bufio.NewScanner":                "checkScannerEntries, with a keptReader",
	"(*bufio.Scanner).Scan":           "checkScannerEntries, with a keptReader",
	"(*bufio.Scanner).Text":           "checkScannerEntries, with a keptReader",
	"(*bufio.Scanner).Err":            "checkScannerEntries, with a keptReader",
	"bufio.NewReader":                 "checkReaderEntries, with a keptReader",
	"(*bufio.Reader).ReadByte":        "checkReaderEntries, with a keptReader",
	"(*bufio.Reader).ReadString":      "TestReadersEnd/Probed, with a keptReader",
	"(*bufio.Reader).ReadBytes":       "TestReadersEnd/Probed, with a keptReader",
	"io.ReadAll":                      "TestReadersEnd/Probed, with a keptReader",
	"bufio.NewWriter":                 "checkWriterEntries, with a keptWriter",
	"(*bufio.Writer).Write":           "checkWriterEntries, with a keptWriter",
	"(*bufio.Writer).WriteByte":       "checkWriterEntries, with a keptWriter",
	"(*bufio.Writer).Flush":           "checkWriterEntries, with a keptWriter",
	"(*bufio.Writer).WriteString":     "checkWriterEntries, with a keptWriter",
	"io.WriteString":                  "checkHTTPEntries, with a probedWriter whose WriteString is the writer's",
	"(*encoding/json.Encoder).Encode": "TestJSONEntries, with the recorder of testdata/jsonharness",
	"fmt.Fprintf":                     "keptFormatting, with a keptWriter",
	"fmt.Fprint":                      "keptFormatting, with a keptWriter",
	"fmt.Fprintln":                    "keptFormatting, with a keptWriter",
	"io.NopCloser":                    "checkIOEntries, with a keptReader",
	"io.LimitReader":                  "checkIOEntries, with a keptReader",
	"io.TeeReader":                    "checkIOEntries, with a keptReader and a keptWriter",
	"io.MultiReader":                  "checkIOEntries, with keptReaders",
	"io.MultiWriter":                  "checkIOEntries, with keptWriters",
	"log.New":                         "checkLoggerEntries, with a keptWriter",
	"(*log.Logger).Printf":            "checkLoggerEntries, with a keptWriter",
	"(*log.Logger).Print":             "checkLoggerEntries, with a keptWriter",
	"(*log.Logger).Println":           "checkLoggerEntries, with a keptWriter",
	"(*net/http.Request).PathValue":   "the sample of PathValue, with a probedBody and a probedContext",
	"net/http.Error":                  "checkHTTPEntries, with a probedWriter",
	"net/http.NotFound":               "checkHTTPEntries, with a probedWriter and a request with a probedBody and a probedContext",
	"os.IsExist":                      "osPredicate, with a recordingError",
	"os.IsNotExist":                   "osPredicate, with a recordingError",
	"os.IsPermission":                 "osPredicate, with a recordingError",
	"os.IsTimeout":                    "osPredicate, with a recordingError whose Timeout it may call",
}

// TestRunsProbed fails when a shipped entry lists under runs or keeps a
// parameter that is not a function and no harness of probedBy hands it
// values that have the methods of lookedFor, and when a probe lacks one of
// them.
func TestRunsProbed(t *testing.T) {
	parallel(t)
	found := map[string]bool{}
	for _, file := range shippedContracts() {
		for key, entry := range file.entries {
			functions := map[string]bool{}
			for _, call := range entry.calls {
				functions[call.name] = true
			}
			var params []string
			for _, run := range entry.runs {
				params = append(params, run.text)
			}
			for _, keep := range entry.keeps {
				params = append(params, keep.name)
			}
			if !slices.ContainsFunc(params, func(name string) bool { return !functions[name] }) {
				continue
			}
			found[key] = true
			if probedBy[key] == "" {
				t.Errorf("%s lists a parameter that is not a function under runs or keeps, and no harness of probedBy hands it values with the methods of lookedFor", key)
			}
		}
	}
	for key := range probedBy {
		if !found[key] {
			t.Errorf("%s is in probedBy, but is no shipped entry that lists a parameter that is not a function under runs or keeps", key)
		}
	}
	// The recorder of the JSON harness is in a program of its own.
	harness, err := os.ReadFile(filepath.Join("testdata", "jsonharness", "main.go"))
	if err != nil {
		t.Fatal(err)
	}
	for _, method := range lookedFor {
		if !strings.Contains(string(harness), "func (r *recorder) "+method+"(") {
			t.Errorf("the recorder of testdata/jsonharness has no method %s", method)
		}
	}
	for _, probe := range []any{&keptReader{}, &keptWriter{}, recordingError{}, probedWriter{}, probedBody{}, probedContext{}} {
		for _, method := range lookedFor {
			if _, ok := reflect.TypeOf(probe).MethodByName(method); !ok {
				t.Errorf("%T has no method %s", probe, method)
			}
		}
	}
}

// probedBody is the body of a request handed to a function whose entry
// claims that it calls nothing of what the request holds: each of its
// methods records a problem while the call is active. It reaches the log
// through a function value, which the walks of what a request reaches do
// not follow, so that marking the call active changes nothing they see.
type probedBody struct{ report func(string) }

func (b probedBody) hit(method string) { b.report(method + " of the request's body") }

func (b probedBody) Read([]byte) (int, error)          { b.hit("Read"); return 0, io.EOF }
func (b probedBody) String() string                    { b.hit("String"); return "" }
func (b probedBody) Error() string                     { b.hit("Error"); return "" }
func (b probedBody) Format(fmt.State, rune)            { b.hit("Format") }
func (b probedBody) GoString() string                  { b.hit("GoString"); return "" }
func (b probedBody) WriteString(string) (int, error)   { b.hit("WriteString"); return 0, nil }
func (b probedBody) ReadFrom(io.Reader) (int64, error) { b.hit("ReadFrom"); return 0, nil }
func (b probedBody) WriteTo(io.Writer) (int64, error)  { b.hit("WriteTo"); return 0, nil }
func (b probedBody) Unwrap() error                     { b.hit("Unwrap"); return nil }
func (b probedBody) Is(error) bool                     { b.hit("Is"); return false }
func (b probedBody) As(any) bool                       { b.hit("As"); return false }
func (b probedBody) Timeout() bool                     { b.hit("Timeout"); return false }
func (b probedBody) Temporary() bool                   { b.hit("Temporary"); return false }
func (b probedBody) Close() error                      { b.hit("Close"); return nil }
func (b probedBody) Flush() error                      { b.hit("Flush"); return nil }

// probedContext is the context of such a request.
type probedContext struct{ report func(string) }

func (c probedContext) hit(method string) { c.report(method + " of the request's context") }

func (c probedContext) Deadline() (time.Time, bool)       { c.hit("Deadline"); return time.Time{}, false }
func (c probedContext) Done() <-chan struct{}             { c.hit("Done"); return nil }
func (c probedContext) Err() error                        { c.hit("Err"); return nil }
func (c probedContext) Value(any) any                     { c.hit("Value"); return nil }
func (c probedContext) String() string                    { c.hit("String"); return "" }
func (c probedContext) Error() string                     { c.hit("Error"); return "" }
func (c probedContext) Format(fmt.State, rune)            { c.hit("Format") }
func (c probedContext) GoString() string                  { c.hit("GoString"); return "" }
func (c probedContext) WriteString(string) (int, error)   { c.hit("WriteString"); return 0, nil }
func (c probedContext) ReadFrom(io.Reader) (int64, error) { c.hit("ReadFrom"); return 0, nil }
func (c probedContext) WriteTo(io.Writer) (int64, error)  { c.hit("WriteTo"); return 0, nil }
func (c probedContext) Unwrap() error                     { c.hit("Unwrap"); return nil }
func (c probedContext) Is(error) bool                     { c.hit("Is"); return false }
func (c probedContext) As(any) bool                       { c.hit("As"); return false }
func (c probedContext) Timeout() bool                     { c.hit("Timeout"); return false }
func (c probedContext) Temporary() bool                   { c.hit("Temporary"); return false }
func (c probedContext) Close() error                      { c.hit("Close"); return nil }
func (c probedContext) Flush() error                      { c.hit("Flush"); return nil }

var _ context.Context = probedContext{}

// probedRequest returns a shallow copy of a request whose body, GetBody,
// and context record a problem when called while k is active.
func probedRequest(r *http.Request, k *keptLog) *http.Request {
	report := func(what string) { k.called(what) }
	probed := r.WithContext(probedContext{report: report})
	probed.Body = probedBody{report: report}
	probed.GetBody = func() (io.ReadCloser, error) {
		report("GetBody of the request")
		return probedBody{report: report}, nil
	}
	return probed
}
