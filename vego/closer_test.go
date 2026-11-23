package vego

import (
	"bytes"
	"compress/flate"
	"compress/gzip"
	"compress/zlib"
	"errors"
	"fmt"
	"go/types"
	"io"
	"math/big"
	"math/rand"
	"net"
	"net/http"
	"net/http/httptest"
	"os"
	"strings"
	"testing"
	"time"

	"github.com/spachava753/laas/vego/internal/logic"
)

// closable is one value of a type that implements io.Closer, with its Read
// and Write where it has them, and how to let go of what it needs besides.
type closable struct {
	c       io.Closer
	r       io.Reader
	w       io.Writer
	release func()
	// held is memory the harness holds besides, which a Close may write
	// only where the closer reaches it, as the buffer a gzip writer
	// flushes into.
	held []any
}

// closers lists implementations of io.Closer in the standard library, and
// one that does at random all the documentation allows: a first Close
// returns any error, and a second one panics.
var closers = []struct {
	name string
	open func(rng *rand.Rand) closable
}{
	{"*os.File", func(rng *rand.Rand) closable {
		f := scratchFile()
		f.Write(randomBytes(rng))
		f.Seek(0, io.SeekStart)
		return closable{c: f, r: f, w: f}
	}},
	{"*io.PipeReader", func(rng *rand.Rand) closable {
		r, w := io.Pipe()
		local := rand.New(rand.NewSource(rng.Int63()))
		go func() {
			for {
				if _, err := w.Write(randomBytes(local)); err != nil {
					return
				}
			}
		}()
		return closable{c: r, r: r, release: func() { w.Close() }}
	}},
	{"*io.PipeWriter", func(rng *rand.Rand) closable {
		r, w := io.Pipe()
		go io.Copy(io.Discard, r)
		return closable{c: w, w: w, release: func() { r.Close() }}
	}},
	{"net.Pipe", func(rng *rand.Rand) closable {
		a, b := net.Pipe()
		local := rand.New(rand.NewSource(rng.Int63()))
		go io.Copy(io.Discard, b)
		go func() {
			for {
				if _, err := b.Write(randomBytes(local)); err != nil {
					return
				}
			}
		}()
		return closable{c: a, r: a, w: a, release: func() { b.Close() }}
	}},
	{"*os.File of os.Pipe", func(rng *rand.Rand) closable {
		r, w, err := os.Pipe()
		if err != nil {
			panic(err)
		}
		go io.Copy(io.Discard, r)
		return closable{c: w, w: w, release: func() { r.Close() }}
	}},
	{"*gzip.Reader", func(rng *rand.Rand) closable {
		var packed bytes.Buffer
		w := gzip.NewWriter(&packed)
		w.Write(randomBytes(rng))
		w.Close()
		r, err := gzip.NewReader(&packed)
		if err != nil {
			panic(err)
		}
		return closable{c: r, r: r}
	}},
	{"*gzip.Writer", func(*rand.Rand) closable {
		b := new(bytes.Buffer)
		w := gzip.NewWriter(b)
		return closable{c: w, w: w, held: []any{b}}
	}},
	{"zlib writer", func(*rand.Rand) closable {
		b := new(bytes.Buffer)
		w := zlib.NewWriter(b)
		return closable{c: w, w: w, held: []any{b}}
	}},
	{"flate reader", func(rng *rand.Rand) closable {
		var packed bytes.Buffer
		w, _ := flate.NewWriter(&packed, flate.DefaultCompression)
		w.Write(randomBytes(rng))
		w.Close()
		r := flate.NewReader(&packed)
		return closable{c: r, r: r}
	}},
	{"*flate.Writer", func(*rand.Rand) closable {
		b := new(bytes.Buffer)
		w, _ := flate.NewWriter(b, flate.BestSpeed)
		return closable{c: w, w: w, held: []any{b}}
	}},
	{"io.NopCloser", func(rng *rand.Rand) closable {
		r := io.NopCloser(bytes.NewReader(randomBytes(rng)))
		return closable{c: r, r: r}
	}},
	{"body of an http.Response", func(rng *rand.Rand) closable {
		resp, err := http.Get(closerServer.URL)
		if err != nil {
			panic(err)
		}
		return closable{c: resp.Body, r: resp.Body}
	}},
	{"any closer the documentation allows", func(rng *rand.Rand) closable {
		c := &anyCloser{rng: rng}
		return closable{c: c, r: c, w: c}
	}},
}

// closerServer answers every request with random bytes.
var closerServer *httptest.Server

// anyCloser returns any error from a first Close and panics on a second,
// which the documentation of io.Closer allows. Its Read and Write behave
// after Close as before.
type anyCloser struct {
	rng    *rand.Rand
	closed bool
}

func (c *anyCloser) Close() error {
	if c.closed {
		panic("closed twice")
	}
	c.closed = true
	if c.rng.Intn(2) == 0 {
		return errors.New("close failed")
	}
	return nil
}

func (c *anyCloser) Read(p []byte) (int, error)  { return anyReader{c.rng}.Read(p) }
func (c *anyCloser) Write(p []byte) (int, error) { return anyWriter{c.rng}.Write(p) }

// checkCloseEntry runs the entry of (io.Closer).Close against each closer:
// random sequences of Read, Write, and Close on one value, Close only while
// what the harness knows says the value is not closed, which is the
// requires. Every call must return within 5s, the ensures must hold of what
// the harness knows after Close, and Read and Write, before and after
// Close, must meet their own entries. That they never close the value is
// what declaring the state claims of them; a Close after them is checked
// as a first Close. What a second Close does is logged, since the
// documentation leaves it undefined.
func checkCloseEntry(t *testing.T, pv *pkgVerifier, fn *funcInfo) {
	for _, defect := range fn.defects {
		t.Errorf("contract cannot be used: %s", defect)
	}
	if fn.receiver == nil {
		t.Fatal("the entry names no receiver")
	}
	closerServer = httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		w.Write(bytes.Repeat([]byte("x"), 1000))
	}))
	defer closerServer.Close()
	ghost := func(closed bool) func(*types.Var, string, logic.When) *logic.Term {
		return func(param *types.Var, name string, _ logic.When) *logic.Term {
			if param != fn.receiver || name != "closed" {
				t.Fatalf("the entry speaks of the state %s of %s", name, param.Name())
			}
			return map[bool]*logic.Term{true: logic.True(), false: logic.False()}[closed]
		}
	}
	holds := func(clauses []*clause, env *specEnv) bool {
		for _, c := range clauses {
			formula, err := pv.res.Formula(c.node, env)
			if err != nil {
				t.Fatalf("%q: %v", c.text, err)
			}
			if !(&evaluator{bindings: map[string]*big.Int{}}).holds(formula) {
				return false
			}
		}
		return true
	}
	bounded := func(t *testing.T, what string, call func()) {
		done := make(chan struct{})
		go func() {
			defer close(done)
			call()
		}()
		select {
		case <-done:
		case <-time.After(5 * time.Second):
			t.Fatalf("%s did not return within 5s", what)
		}
	}
	for _, impl := range closers {
		t.Run(impl.name, func(t *testing.T) {
			rng := rand.New(rand.NewSource(1))
			checked := 0
			var second []string
			for range 80 {
				value := impl.open(rng)
				closed := false
				for range 1 + rng.Intn(6) {
					switch op := rng.Intn(3); {
					case op == 0 && value.r != nil:
						p := make([]byte, 1+rng.Intn(64))
						var n int
						bounded(t, "Read", func() { n, _ = value.r.Read(p) })
						if n < 0 || n > len(p) {
							t.Fatalf("Read returned %d for %d bytes, closed %v", n, len(p), closed)
						}
					case op == 1 && value.w != nil:
						p := randomBytes(rng)
						var n int
						var err error
						bounded(t, "Write", func() { n, err = value.w.Write(p) })
						if n < 0 || n > len(p) || (n < len(p) && err == nil) {
							t.Fatalf("Write returned %d, %v for %d bytes, closed %v", n, err, len(p), closed)
						}
					case op == 2 && !closed:
						env := &specEnv{v: &fnVerifier{pkgVerifier: pv, fn: fn}, fn: fn, givenState: ghost(closed)}
						if !holds(fn.requires, env) {
							t.Fatal("the requires does not hold of a value that is not closed")
						}
						bystander := &struct {
							n int
							b []byte
						}{7, []byte("kept")}
						if err := closeWrites(value.c, append(value.held, bystander), func() { bounded(t, "Close", func() { value.c.Close() }) }); err != nil {
							t.Fatal(err)
						}
						closed = true
						checked++
						env.givenState = func(p *types.Var, s string, when logic.When) *logic.Term {
							if when == logic.Primed {
								return ghost(true)(p, s, when)
							}
							return ghost(false)(p, s, when)
						}
						if !holds(fn.ensures, env) {
							t.Fatal("the ensures is false after Close returned")
						}
					}
				}
				if closed && len(second) < 3 {
					bounded(t, "a second Close", func() {
						defer func() {
							if r := recover(); r != nil {
								second = append(second, fmt.Sprintf("panics: %v", r))
							}
						}()
						second = append(second, fmt.Sprintf("returns %v", value.c.Close()))
					})
				}
				if !closed {
					bounded(t, "Close", func() { value.c.Close() })
				}
				if value.release != nil {
					value.release()
				}
			}
			if checked < 20 {
				t.Fatalf("only %d calls of Close were checked", checked)
			}
			t.Logf("a second Close %s", strings.Join(second, "; "))
		})
	}
}

// closeWrites makes a Close and reports what the entry of Close does not
// allow it: a change to memory the harness holds that the closer does not
// reach, and a reference after the call to memory the harness held that
// the closer did not reach before. Close may write behind its receiver,
// which is what the closer reaches, as a gzip writer writes the buffer it
// flushes into (F3 of the review of F28).
func closeWrites(c io.Closer, held []any, call func()) error {
	behind := func() map[uintptr]bool {
		return walkFrom(&memoryWalk{stop: walkStop, readHidden: true, through: true, objects: map[uintptr]bool{}}, c).objects
	}
	before := behind()
	prints := make([]string, len(held))
	reached := make([]bool, len(held))
	heldObjects := newWalk(nil, true, held...).objects
	for i, h := range held {
		w := newWalk(nil, true, h)
		prints[i] = w.print.String()
		for at := range w.objects {
			reached[i] = reached[i] || before[at]
		}
	}
	call()
	for i, h := range held {
		if !reached[i] && newWalk(nil, true, h).print.String() != prints[i] {
			return fmt.Errorf("Close wrote memory the harness holds and the closer does not reach: %T", h)
		}
	}
	for at := range behind() {
		if !before[at] && heldObjects[at] {
			return fmt.Errorf("Close made the closer reach memory the harness held")
		}
	}
	return nil
}

// victim is memory that a closer which breaks the entry writes.
var victim = &struct{ n int }{}

type victimCloser struct{}

func (victimCloser) Close() error { victim.n++; return nil }

// TestCloseHarnessCatches shows closeWrites failing on a closer that writes
// memory it does not reach, and passing a gzip writer that writes the
// buffer it holds.
func TestCloseHarnessCatches(t *testing.T) {
	alone(t)
	if closeWrites(victimCloser{}, []any{victim}, func() { victimCloser{}.Close() }) == nil {
		t.Errorf("a closer that writes memory it does not reach passes the harness")
	}
	b := new(bytes.Buffer)
	w := gzip.NewWriter(b)
	if err := closeWrites(w, []any{b}, func() { w.Close() }); err != nil {
		t.Errorf("a gzip writer over a buffer it holds fails the harness: %v", err)
	}
}
