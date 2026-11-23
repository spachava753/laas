package vego

import (
	"bufio"
	"bytes"
	"fmt"
	"go/types"
	"io"
	"log"
	"math/big"
	"math/rand"
	"reflect"
	"runtime"
	"slices"
	"strconv"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/spachava753/laas/vego/internal/logic"
)

// The entries of functions that keep what they are given, and of the
// methods that later run it, are tested by sequences: a wrapper is made
// over readers and writers that record when they are called, the methods of
// the wrapper are called at random, each only when its requires holds of
// what the harness knows, and the kept code must run only while a call of
// a method of the wrapper is active, on the goroutine that made it, and
// only through the methods that the entries of io.Reader and io.Writer
// cover. The readers and writers also have the methods of io.StringWriter,
// io.ReaderFrom, and io.WriterTo, and a call of one of those fails the
// test: an entry that is handed a reader or a writer claims only what Read
// and Write do, so a later Go whose wrapper type-asserts to one of them and
// calls it fails here rather than unseen.

// keptLog records how kept readers and writers are called.
type keptLog struct {
	mu        sync.Mutex
	active    bool
	goroutine uint64
	problems  []string
	// written holds the length of what each call of Write was given.
	written []int
}

// enter marks a call of a method of the wrapper as active on the calling
// goroutine, until the function it returns is called.
func (k *keptLog) enter() func() {
	k.mu.Lock()
	k.active, k.goroutine = true, goroutineID()
	k.mu.Unlock()
	return func() {
		k.mu.Lock()
		k.active = false
		k.mu.Unlock()
	}
}

// ran records a call of kept code, and a problem if no call of the wrapper
// is active or it runs on another goroutine.
func (k *keptLog) ran(what string) {
	k.mu.Lock()
	defer k.mu.Unlock()
	switch {
	case !k.active:
		k.problems = append(k.problems, what+" ran while no call that is handed what keeps it was active")
	case goroutineID() != k.goroutine:
		k.problems = append(k.problems, what+" ran on another goroutine than the call that is handed what keeps it")
	}
}

// refuse records a call of a method that no entry covers.
func (k *keptLog) refuse(what string) {
	k.mu.Lock()
	defer k.mu.Unlock()
	k.problems = append(k.problems, what+" was called, which no entry covers")
}

// check panics with what went wrong, for a harness of TestShippedContracts,
// which has no testing.T; and returns the problems for one that has.
func (k *keptLog) check() {
	k.mu.Lock()
	defer k.mu.Unlock()
	if len(k.problems) > 0 {
		panic(strings.Join(k.problems, "; "))
	}
}

// goroutineID reads the number of the calling goroutine from its stack.
func goroutineID() uint64 {
	var buf [64]byte
	text := string(buf[:runtime.Stack(buf[:], false)])
	text = strings.TrimPrefix(text, "goroutine ")
	id, _ := strconv.ParseUint(text[:strings.IndexByte(text, ' ')], 10, 64)
	return id
}

// keptWriter writes to inner, which meets the entry of (io.Writer).Write,
// and records each call in log.
type keptWriter struct {
	log   *keptLog
	inner io.Writer
}

func (w *keptWriter) Write(p []byte) (int, error) {
	w.log.ran("Write")
	w.log.mu.Lock()
	w.log.written = append(w.log.written, len(p))
	w.log.mu.Unlock()
	n, err := w.inner.Write(p)
	return n, w.log.wrap(err)
}

func (w *keptWriter) WriteString(s string) (int, error) {
	w.log.refuse("WriteString of a kept writer")
	return w.inner.Write([]byte(s))
}

func (w *keptWriter) ReadFrom(r io.Reader) (int64, error) {
	w.log.refuse("ReadFrom of a kept writer")
	return 0, nil
}

func (w *keptWriter) WriteTo(io.Writer) (int64, error) {
	w.log.refuse("WriteTo of a kept writer")
	return 0, nil
}

// keptReader reads from inner, which meets the entry of (io.Reader).Read,
// and records each call in log, with a problem for an empty p, which that
// entry rules out.
type keptReader struct {
	log   *keptLog
	inner io.Reader
}

func (r *keptReader) Read(p []byte) (int, error) {
	r.log.ran("Read")
	if len(p) == 0 {
		r.log.refuse("Read into an empty slice")
	}
	n, err := r.inner.Read(p)
	return n, r.log.wrap(err)
}

func (r *keptReader) WriteTo(io.Writer) (int64, error) {
	r.log.refuse("WriteTo of a kept reader")
	return 0, nil
}

func (r *keptReader) ReadFrom(io.Reader) (int64, error) {
	r.log.refuse("ReadFrom of a kept reader")
	return 0, nil
}

func (r *keptReader) WriteString(string) (int, error) {
	r.log.refuse("WriteString of a kept reader")
	return 0, nil
}

// Close would close what a wrapper keeps, which no entry of a wrapper
// claims.
func (r *keptReader) Close() error {
	r.log.refuse("Close of a kept reader")
	return nil
}

// The methods of the other optional interfaces of io and fmt: an entry
// whose asserts lists none of them claims that the function finds none of
// them by a type assertion, so a call of one fails the test. The harness
// catches only the interfaces it has methods of; see asserts.go.
func (r *keptReader) ReadByte() (byte, error) {
	r.log.refuse("ReadByte of a kept reader")
	return 0, io.EOF
}
func (r *keptReader) UnreadByte() error { r.log.refuse("UnreadByte of a kept reader"); return nil }
func (r *keptReader) ReadRune() (rune, int, error) {
	r.log.refuse("ReadRune of a kept reader")
	return 0, 0, io.EOF
}
func (r *keptReader) UnreadRune() error { r.log.refuse("UnreadRune of a kept reader"); return nil }
func (r *keptReader) ReadAt([]byte, int64) (int, error) {
	r.log.refuse("ReadAt of a kept reader")
	return 0, io.EOF
}
func (r *keptReader) Seek(int64, int) (int64, error) {
	r.log.refuse("Seek of a kept reader")
	return 0, nil
}
func (r *keptReader) String() string         { r.log.refuse("String of a kept reader"); return "" }
func (r *keptReader) GoString() string       { r.log.refuse("GoString of a kept reader"); return "" }
func (r *keptReader) Format(fmt.State, rune) { r.log.refuse("Format of a kept reader") }
func (r *keptReader) Flush() error           { r.log.refuse("Flush of a kept reader"); return nil }

func (w *keptWriter) Close() error { w.log.refuse("Close of a kept writer"); return nil }
func (w *keptWriter) WriteByte(byte) error {
	w.log.refuse("WriteByte of a kept writer")
	return nil
}
func (w *keptWriter) WriteRune(rune) (int, error) {
	w.log.refuse("WriteRune of a kept writer")
	return 0, nil
}
func (w *keptWriter) WriteAt([]byte, int64) (int, error) {
	w.log.refuse("WriteAt of a kept writer")
	return 0, nil
}
func (w *keptWriter) Seek(int64, int) (int64, error) {
	w.log.refuse("Seek of a kept writer")
	return 0, nil
}
func (w *keptWriter) String() string         { w.log.refuse("String of a kept writer"); return "" }
func (w *keptWriter) GoString() string       { w.log.refuse("GoString of a kept writer"); return "" }
func (w *keptWriter) Format(fmt.State, rune) { w.log.refuse("Format of a kept writer") }
func (w *keptWriter) Flush() error           { w.log.refuse("Flush of a kept writer"); return nil }

// keptError is an error that kept code returned. A function whose asserts
// lists nothing claims that it calls no method of it either, while the
// call lasts; it may compare it, store it, and return it.
type keptError struct {
	log   *keptLog
	inner error
}

func (e keptError) Error() string {
	e.log.called("Error of an error that kept code returned")
	return e.inner.Error()
}

func (e keptError) Unwrap() error {
	e.log.called("Unwrap of an error that kept code returned")
	return e.inner
}

func (e keptError) Is(target error) bool {
	e.log.called("Is of an error that kept code returned")
	return false
}

// wrap gives an error that kept code returns methods that record their
// calls. io.EOF and nil stay as they are: wrappers compare them with ==.
func (k *keptLog) wrap(err error) error {
	if err == nil || err == io.EOF || err == io.ErrUnexpectedEOF {
		return err
	}
	return keptError{log: k, inner: err}
}

// called records a call of a method of a value that kept code returned, as
// a problem while a call that is handed what keeps it is active.
func (k *keptLog) called(what string) {
	k.mu.Lock()
	defer k.mu.Unlock()
	if k.active {
		k.problems = append(k.problems, what+" was called while the call was active, which its asserts does not allow")
	}
}

// poisoned is put into a slice after it was handed to a function that keeps
// what the slice holds: the function must have copied the slice, so any
// call fails the test.
type poisoned struct{ log *keptLog }

func (p poisoned) Read([]byte) (int, error) {
	p.log.refuse("Read of a reader put into the slice after the call")
	return 0, io.EOF
}

func (p poisoned) Write(q []byte) (int, error) {
	p.log.refuse("Write of a writer put into the slice after the call")
	return len(q), nil
}

// randomKeptWriter returns a writer that keptWriter wraps around one of
// randomWriter's or one that does at random all the documentation allows.
func randomKeptWriter(rng *rand.Rand, k *keptLog) *keptWriter {
	if rng.Intn(3) == 0 {
		return &keptWriter{log: k, inner: anyWriter{rng}}
	}
	return &keptWriter{log: k, inner: randomWriter(rng)}
}

// keptFormatting runs a function of fmt or log that is handed a writer, as
// a call of the wrapper that keeps it, and fails if the writer was run
// otherwise or through another method than Write.
func keptFormatting(rng *rand.Rand, call func(w io.Writer)) io.Writer {
	k := &keptLog{}
	w := randomKeptWriter(rng, k)
	done := k.enter()
	call(w)
	done()
	k.check()
	return w
}

// sequenceCheck evaluates the clauses of one entry for a call that a
// sequence harness made, with what the harness knows: the values of the
// parameters and results, the states of the objects they refer to, and
// which results are new.
type sequenceCheck struct {
	t  *testing.T
	pv *pkgVerifier
	fn *funcInfo
	// given holds the terms of the parameters and results; a reference is
	// 0 for nil and 1 otherwise.
	given   map[*types.Var]*logic.Term
	results []*logic.Term
	// before and after give the states, by parameter or result and name,
	// before and after the call.
	before, after map[*types.Var]map[string]bool
	// fresh holds the results that the call made new, and kept those
	// that are what the value the call was given holds, as a large enough
	// Writer handed to bufio.NewWriter: fresh(result, w) holds of either.
	fresh, kept map[*types.Var]bool
	// length gives |b| of an owner before and after the call, by the
	// formula its declaration gives; see buffers_test.go.
	length func(v *types.Var, when logic.When) *logic.Term
	// within holds the results that lie in what the receiver owns, which
	// within(result, b) asks.
	within map[*types.Var]bool
}

func (c *sequenceCheck) env() *specEnv {
	env := &specEnv{
		v: &fnVerifier{pkgVerifier: c.pv, fn: c.fn}, fn: c.fn,
		given: c.given, givenPost: c.given, givenResults: c.results,
	}
	env.givenState = func(v *types.Var, name string, when logic.When) *logic.Term {
		// A result is read in the state after the call.
		states := c.before
		if when == logic.Primed || slices.Contains(c.fn.results, v) {
			states = c.after
		}
		value, known := states[v][name]
		if !known {
			c.t.Fatalf("the harness does not know the state %s of %s", name, v.Name())
		}
		return logic.BoolLit(value)
	}
	env.givenLength = c.length
	env.givenRelation = func(name string, paths []logic.Path) (*logic.Term, error) {
		index, isResult := c.fn.resultNames[paths[0].Root]
		if name == "within" && c.within != nil && isResult && len(paths) == 2 && len(paths[0].Steps) == 0 && len(paths[1].Steps) == 0 &&
			paths[1].Root == c.fn.params[0].Name() {
			return logic.BoolLit(c.within[c.fn.results[index]]), nil
		}
		if name != "fresh" || len(paths[0].Steps) > 0 || !isResult {
			return nil, fmt.Errorf("the harness can tell only whether a result is fresh, not %s(%s)", name, paths[0].Root)
		}
		result := c.fn.results[index]
		if len(paths) > 1 {
			return logic.BoolLit(c.fresh[result] || c.kept[result]), nil
		}
		return logic.BoolLit(c.fresh[result]), nil
	}
	return env
}

// holds reports whether every clause holds.
func (c *sequenceCheck) holds(clauses []*clause) bool {
	env := c.env()
	eval := &evaluator{bindings: map[string]*big.Int{}, errors: standIn}
	for _, cl := range clauses {
		formula, err := c.pv.res.Formula(cl.node, env)
		if err != nil {
			c.t.Fatalf("%s %q: %v", cl.kind, cl.text, err)
		}
		if !eval.holds(formula) {
			return false
		}
	}
	return true
}

// ensure fails the test unless every ensures holds.
func (c *sequenceCheck) ensure(what string) {
	env := c.env()
	eval := &evaluator{bindings: map[string]*big.Int{}, errors: standIn}
	for _, cl := range c.fn.ensures {
		formula, err := c.pv.res.Formula(cl.node, env)
		if err != nil {
			c.t.Fatalf("ensures %q: %v", cl.text, err)
		}
		if !eval.holds(formula) {
			c.t.Fatalf("ensures %q is false after %s", cl.text, what)
		}
	}
}

// reference grounds a value that formulas only compare with nil.
func reference(isNil bool) *logic.Term {
	if isNil {
		return logic.RefLit(0)
	}
	return logic.RefLit(1)
}

// contractOfKey returns the shipped contract of a function or method of a
// package by its key.
func contractOfKey(t *testing.T, pv *pkgVerifier, pkg *types.Package, key string) *funcInfo {
	_, name, _ := splitFuncName(key)
	callee, ok := pkg.Scope().Lookup(name).(*types.Func)
	if receiver, method, isMethod := strings.Cut(strings.TrimPrefix(name, "(*"), ")."); isMethod {
		typeName := pkg.Scope().Lookup(receiver).(*types.TypeName)
		found, _, _ := types.LookupFieldOrMethod(types.NewPointer(typeName.Type()), true, pkg, method)
		callee, ok = found.(*types.Func)
	}
	if !ok {
		t.Fatalf("package %s has no function %s", pkg.Path(), name)
	}
	fn := pv.trustedContract(callee)
	if fn == nil {
		t.Fatalf("%s has no shipped contract", key)
	}
	for _, defect := range fn.defects {
		t.Errorf("the contract of %s cannot be used: %s", key, defect)
	}
	return fn
}

// loggerMethods prints with a method of a logger, by the key of its entry,
// and returns the length of what fmt prints of the same operands.
var loggerMethods = map[string]func(l *log.Logger, rng *rand.Rand) int{
	"(*log.Logger).Printf": func(l *log.Logger, rng *rand.Rand) int {
		format, v := randomFormat(rng), randomOperands(rng)
		l.Printf(format, v...)
		return len(fmt.Sprintf(format, v...))
	},
	"(*log.Logger).Print": func(l *log.Logger, rng *rand.Rand) int {
		v := randomOperands(rng)
		l.Print(v...)
		return len(fmt.Sprint(v...))
	},
	"(*log.Logger).Println": func(l *log.Logger, rng *rand.Rand) int {
		v := randomOperands(rng)
		l.Println(v...)
		return len(fmt.Sprintln(v...))
	},
}

// loggerGhost is what the harness knows of a logger: what its output and
// its prefix were set to last, from which ready follows by its meaning.
type loggerGhost struct {
	output io.Writer
	prefix string
}

func (g loggerGhost) ready() bool { return g.output != nil && len(g.prefix) <= 4096 }

// randomPrefix returns a prefix of a length about the bound of ready.
func randomPrefix(rng *rand.Rand) string {
	return strings.Repeat("p", []int{0, 3, 4096, 4097}[rng.Intn(4)])
}

// checkLoggerEntries runs the entries of log.New and of the methods of a
// logger that print. Each round makes a logger with New over a writer that
// records how it is called, then prints with its methods and changes its
// output and prefix as code that is not verified may, at random; New and
// the methods are called only when their requires holds of what the
// harness knows. The writer must run only while a method that prints is
// active, and only through Write; New must run nothing.
func checkLoggerEntries(t *testing.T, pv *pkgVerifier, pkg *types.Package, key string) {
	newFn := contractOfKey(t, pv, pkg, "log.New")
	// The header of a logger shows the name of this file with Llongfile,
	// since the calls are made here.
	_, file, _, _ := runtime.Caller(0)
	if key != "log.New" && loggerMethods[key] == nil {
		t.Fatalf("no harness calls %s; add one to loggerMethods", key)
	}
	rng := rand.New(rand.NewSource(1))
	checked := 0
	arrays := &ownerArrays{}
	var made []*log.Logger
	for range 300 {
		k := &keptLog{}
		var out io.Writer
		if rng.Intn(8) > 0 {
			out = randomKeptWriter(rng, k)
		}
		prefix := randomPrefix(rng)
		c := &sequenceCheck{t: t, pv: pv, fn: newFn,
			given: map[*types.Var]*logic.Term{newFn.params[0]: reference(out == nil), newFn.params[1]: logic.Bytes(prefix), newFn.params[2]: logic.IntLit(0)}}
		if !c.holds(newFn.requires) {
			continue
		}
		// New runs nothing it is given: no call of a method is active.
		l := log.New(out, prefix, rng.Intn(128))
		k.check()
		ghost := loggerGhost{output: out, prefix: prefix}
		fresh := true
		for _, earlier := range made {
			fresh = fresh && earlier != l
		}
		made = append(made, l)
		c.results = []*logic.Term{reference(l == nil)}
		c.fresh = map[*types.Var]bool{newFn.results[0]: fresh}
		c.after = map[*types.Var]map[string]bool{newFn.results[0]: {"ready": ghost.ready()}}
		c.ensure("New")
		if key == "log.New" {
			checked++
			continue
		}
		method := contractOfKey(t, pv, pkg, key)
		for range 1 + rng.Intn(6) {
			switch rng.Intn(6) {
			case 0:
				// Code that is not verified may set another output, or none.
				w := io.Writer(nil)
				if rng.Intn(3) > 0 {
					w = randomKeptWriter(rng, k)
				}
				l.SetOutput(w)
				ghost.output = w
				continue
			case 1:
				ghost.prefix = randomPrefix(rng)
				l.SetPrefix(ghost.prefix)
				continue
			case 2:
				// Kept code that runs later on its own would run now.
				time.Sleep(time.Millisecond)
				k.check()
				continue
			}
			state := map[*types.Var]map[string]bool{method.params[0]: {"ready": ghost.ready()}}
			m := &sequenceCheck{t: t, pv: pv, fn: method, before: state, after: state,
				given: map[*types.Var]*logic.Term{method.params[0]: reference(false)}}
			for _, param := range method.params[1:] {
				m.given[param] = logic.Const("unreadable", logic.IntSeq)
			}
			if !m.holds(method.requires) {
				continue
			}
			k.written = nil
			done := k.enter()
			var printed int
			arrays.checkGrowth(t, l, key, func() { printed = loggerMethods[key](l, rng) })
			done()
			k.check()
			m.ensure(key)
			// What the logger writes is what fmt prints, the header, and the
			// prefix: the bound at the call counts fmtSlack and loggerPrefix
			// beyond what fmt prints, and assumes the name of the file in the
			// header, which is this file for these calls.
			for _, n := range k.written {
				if limit := printed + int(slackOf(method.obj)) + len(file); n > limit {
					t.Fatalf("%s wrote %d bytes, more than the %d that fmt prints of the operands, the slack the bound counts, and the name of this file",
						key, n, printed)
				}
			}
			checked++
		}
	}
	if checked < 100 {
		t.Fatalf("only %d calls of %s were checked", checked, key)
	}
}

// randomKeptReader returns a reader that keptReader wraps around one of
// several: random lines, any reader the documentation allows, an endless
// reader of one byte with no newline, or a final line without a newline of
// exactly MaxScanTokenSize bytes or one more.
func randomKeptReader(rng *rand.Rand, k *keptLog) *keptReader {
	var inner io.Reader
	switch rng.Intn(5) {
	case 0:
		inner = anyReader{rng}
	case 1:
		inner = endless{}
	case 2:
		inner = strings.NewReader(strings.Repeat("x", bufio.MaxScanTokenSize+rng.Intn(2)))
	default:
		var lines strings.Builder
		for range rng.Intn(20) {
			lines.WriteString(strings.Repeat("ab", rng.Intn(40)))
			lines.WriteString([]string{"\n", "\r\n", ""}[rng.Intn(3)])
		}
		inner = strings.NewReader(lines.String())
	}
	return &keptReader{log: k, inner: inner}
}

// endless reads the byte x for ever.
type endless struct{}

func (endless) Read(p []byte) (int, error) {
	for i := range p {
		p[i] = 'x'
	}
	return len(p), nil
}

// within runs a call of a method of a wrapper as active on a goroutine of
// its own, so that kept code that runs on another goroutine is seen, and
// fails the test if it does not return within 5 s.
func within(t *testing.T, k *keptLog, what string, call func()) {
	t.Helper()
	done := make(chan struct{})
	go func() {
		defer close(done)
		leave := k.enter()
		defer leave()
		call()
	}()
	select {
	case <-done:
	case <-time.After(5 * time.Second):
		t.Fatalf("%s did not return within 5s", what)
	}
	if len(k.problems) > 0 {
		t.Fatalf("after %s: %s", what, strings.Join(k.problems, "; "))
	}
}

// standIn is the error that errorTerm grounds every error that is not nil
// to; the entries compare errors only with nil.
var standIn = &grounder{errs: []error{io.ErrShortWrite}}

// errorTerm grounds an error that no formula of these entries reads but
// to compare it with nil, as an error the evaluator knows.
func errorTerm(err error) *logic.Term {
	if err == nil {
		return logic.NilErr()
	}
	return logic.Const(errorName+"0", logic.Err)
}

// lengthTerm grounds a string or a slice by its length, which is all that
// the entries of these wrappers say of one.
func lengthTerm(n int) *logic.Term {
	return logic.Fill(logic.IntLit(int64(n)), logic.IntLit(0))
}

// checkMethod checks one call of a method of a wrapper whose receiver is
// its first parameter: the requires with the ghost before, the call, and
// the ensures with the ghost after, which the call itself does not change.
// It reports whether the requires held and the call was made. What the
// receiver owns must change only as ownerGrowth assumes (F32 of the review
// of step 3); arrays holds the arrays the harness has seen.
func checkMethod(t *testing.T, pv *pkgVerifier, fn *funcInfo, k *keptLog, ready bool, given []*logic.Term,
	owner any, arrays *ownerArrays, call func() []*logic.Term) bool {
	t.Helper()
	state := map[*types.Var]map[string]bool{fn.params[0]: {"ready": ready}}
	c := &sequenceCheck{t: t, pv: pv, fn: fn, before: state, after: state,
		given: map[*types.Var]*logic.Term{fn.params[0]: reference(false)}}
	for i, param := range fn.params[1:] {
		c.given[param] = given[i]
	}
	if !c.holds(fn.requires) {
		return false
	}
	within(t, k, fn.obj.FullName(), func() {
		arrays.checkGrowth(t, owner, fn.obj.FullName(), func() { c.results = call() })
	})
	c.ensure(fn.obj.FullName())
	return true
}

// checkScannerEntries runs the entries of bufio.NewScanner and the methods
// of a Scanner. Each round makes a Scanner over a reader that records how
// it is called, then calls Scan, Text, and Err at random, and Split or
// Buffer as code that is not verified may before the first Scan, after
// which ready is false. NewScanner must run nothing it is given, and
// make a new Scanner each time.
func checkScannerEntries(t *testing.T, pv *pkgVerifier, pkg *types.Package, key string) {
	newFn := contractOfKey(t, pv, pkg, "bufio.NewScanner")
	methods := map[string]*funcInfo{}
	for _, name := range []string{"Scan", "Text", "Err"} {
		methods[name] = contractOfKey(t, pv, pkg, "(*bufio.Scanner)."+name)
	}
	rng := rand.New(rand.NewSource(1))
	checked := 0
	arrays := &ownerArrays{}
	var made []*bufio.Scanner
	for range 300 {
		k := &keptLog{}
		var r io.Reader
		if rng.Intn(8) > 0 {
			r = randomKeptReader(rng, k)
		}
		c := &sequenceCheck{t: t, pv: pv, fn: newFn, given: map[*types.Var]*logic.Term{newFn.params[0]: reference(r == nil)}}
		if !c.holds(newFn.requires) {
			continue
		}
		s := bufio.NewScanner(r)
		k.check()
		fresh := !slices.Contains(made, s)
		made = append(made, s)
		ready := true
		c.results = []*logic.Term{reference(s == nil)}
		c.fresh = map[*types.Var]bool{newFn.results[0]: fresh}
		c.after = map[*types.Var]map[string]bool{newFn.results[0]: {"ready": ready}}
		c.ensure("NewScanner")
		if key == "bufio.NewScanner" {
			checked++
			continue
		}
		scanned := false
		for range 1 + rng.Intn(10) {
			name := []string{"Scan", "Scan", "Text", "Text", "Err", "Split", "Buffer", "sleep"}[rng.Intn(8)]
			switch name {
			case "Split", "Buffer":
				// Both panic once Scan has been called.
				if scanned {
					continue
				}
				if name == "Split" {
					s.Split(bufio.ScanWords)
				} else {
					given := make([]byte, 16)
					arrays.add(given)
					s.Buffer(given, 64)
				}
				ready = false
				continue
			case "sleep":
				time.Sleep(time.Millisecond)
				k.check()
				continue
			}
			fn := methods[name]
			made := checkMethod(t, pv, fn, k, ready, nil, s, arrays, func() []*logic.Term {
				switch name {
				case "Scan":
					return []*logic.Term{logic.BoolLit(s.Scan())}
				case "Text":
					return []*logic.Term{lengthTerm(len(s.Text()))}
				}
				return []*logic.Term{errorTerm(s.Err())}
			})
			scanned = scanned || (made && name == "Scan")
			if made && fn.obj.FullName() == key {
				checked++
			}
		}
	}
	if checked < 100 {
		t.Fatalf("only %d calls of %s were checked", checked, key)
	}
}

// checkReaderEntries runs the entries of bufio.NewReader and of ReadByte.
// The reader given to NewReader is sometimes a *bufio.Reader that is large
// enough, which NewReader returns as it is, so that a claim that the result
// is new fails. Code that is not verified may Reset the Reader at random.
func checkReaderEntries(t *testing.T, pv *pkgVerifier, pkg *types.Package, key string) {
	newFn := contractOfKey(t, pv, pkg, "bufio.NewReader")
	readByte := contractOfKey(t, pv, pkg, "(*bufio.Reader).ReadByte")
	rng := rand.New(rand.NewSource(1))
	checked := 0
	arrays := &ownerArrays{}
	var made []*bufio.Reader
	for range 200 {
		k := &keptLog{}
		var rd io.Reader
		switch rng.Intn(8) {
		case 0:
		case 1:
			own := bufio.NewReaderSize(randomKeptReader(rng, k), 8192)
			made = append(made, own)
			rd = own
		default:
			rd = randomKeptReader(rng, k)
		}
		c := &sequenceCheck{t: t, pv: pv, fn: newFn, given: map[*types.Var]*logic.Term{newFn.params[0]: reference(rd == nil)}}
		if !c.holds(newFn.requires) {
			continue
		}
		b := bufio.NewReader(rd)
		k.check()
		c.results = []*logic.Term{reference(b == nil)}
		c.fresh = map[*types.Var]bool{newFn.results[0]: !slices.Contains(made, b)}
		c.kept = map[*types.Var]bool{newFn.results[0]: io.Reader(b) == rd}
		made = append(made, b)
		ready := true
		c.after = map[*types.Var]map[string]bool{newFn.results[0]: {"ready": ready}}
		c.ensure("NewReader")
		if key == "bufio.NewReader" {
			checked++
			continue
		}
		for range 1 + rng.Intn(10) {
			switch rng.Intn(8) {
			case 0:
				b.Reset(nil)
				ready = false
				continue
			case 1:
				b.Reset(randomKeptReader(rng, k))
				ready = true
				continue
			case 2:
				// Reset to itself sets nothing.
				b.Reset(b)
				continue
			case 3:
				time.Sleep(time.Millisecond)
				k.check()
				continue
			}
			if checkMethod(t, pv, readByte, k, ready, nil, b, arrays, func() []*logic.Term {
				c, err := b.ReadByte()
				return []*logic.Term{logic.IntLit(int64(c)), errorTerm(err)}
			}) {
				checked++
			}
		}
	}
	if checked < 100 {
		t.Fatalf("only %d calls of %s were checked", checked, key)
	}
}

// writerMethods calls a method of a Writer by the key of its entry, with
// the slice Write is given, and returns its results.
var writerMethods = map[string]func(b *bufio.Writer, p []byte) []*logic.Term{
	"(*bufio.Writer).Write": func(b *bufio.Writer, p []byte) []*logic.Term {
		n, err := b.Write(p)
		return []*logic.Term{logic.IntLit(int64(n)), errorTerm(err)}
	},
	"(*bufio.Writer).WriteByte": func(b *bufio.Writer, p []byte) []*logic.Term {
		return []*logic.Term{errorTerm(b.WriteByte('w'))}
	},
	"(*bufio.Writer).Flush": func(b *bufio.Writer, p []byte) []*logic.Term {
		return []*logic.Term{errorTerm(b.Flush())}
	},
}

// checkWriterEntries runs the entries of bufio.NewWriter and the methods of
// a Writer, as checkReaderEntries does for a Reader. Every slice that Write
// was given must be as it was, after that call and after the later ones.
func checkWriterEntries(t *testing.T, pv *pkgVerifier, pkg *types.Package, key string) {
	newFn := contractOfKey(t, pv, pkg, "bufio.NewWriter")
	if key != "bufio.NewWriter" && writerMethods[key] == nil {
		t.Fatalf("no harness calls %s; add one to writerMethods", key)
	}
	contracts := map[string]*funcInfo{}
	for name := range writerMethods {
		contracts[name] = contractOfKey(t, pv, pkg, name)
	}
	rng := rand.New(rand.NewSource(1))
	checked := 0
	arrays := &ownerArrays{}
	var made []*bufio.Writer
	for range 200 {
		k := &keptLog{}
		var w io.Writer
		switch rng.Intn(8) {
		case 0:
		case 1:
			own := bufio.NewWriterSize(randomKeptWriter(rng, k), 8192)
			made = append(made, own)
			w = own
		default:
			w = randomKeptWriter(rng, k)
		}
		c := &sequenceCheck{t: t, pv: pv, fn: newFn, given: map[*types.Var]*logic.Term{newFn.params[0]: reference(w == nil)}}
		if !c.holds(newFn.requires) {
			continue
		}
		b := bufio.NewWriter(w)
		k.check()
		c.results = []*logic.Term{reference(b == nil)}
		c.fresh = map[*types.Var]bool{newFn.results[0]: !slices.Contains(made, b)}
		c.kept = map[*types.Var]bool{newFn.results[0]: io.Writer(b) == w}
		made = append(made, b)
		ready := true
		c.after = map[*types.Var]map[string]bool{newFn.results[0]: {"ready": ready}}
		c.ensure("NewWriter")
		if key == "bufio.NewWriter" {
			checked++
			continue
		}
		var given, copies [][]byte
		for range 1 + rng.Intn(10) {
			switch rng.Intn(9) {
			case 0:
				b.Reset(nil)
				ready = false
				continue
			case 1:
				b.Reset(randomKeptWriter(rng, k))
				ready = true
				continue
			case 2:
				b.Reset(b)
				continue
			case 3:
				time.Sleep(time.Millisecond)
				k.check()
				continue
			}
			name := []string{"(*bufio.Writer).Write", "(*bufio.Writer).WriteByte", "(*bufio.Writer).Flush"}[rng.Intn(3)]
			p := make([]byte, []int{0, 1, 100, 4096, 10000}[rng.Intn(5)])
			rng.Read(p)
			var args []*logic.Term
			switch name {
			case "(*bufio.Writer).Write":
				args = []*logic.Term{lengthTerm(len(p))}
				given, copies = append(given, p), append(copies, slices.Clone(p))
			case "(*bufio.Writer).WriteByte":
				args = []*logic.Term{logic.IntLit('w')}
			}
			arrays.add(p)
			if checkMethod(t, pv, contracts[name], k, ready, args, b, arrays, func() []*logic.Term {
				return writerMethods[name](b, p)
			}) && name == key {
				checked++
			}
			for i := range given {
				if !bytes.Equal(given[i], copies[i]) {
					t.Fatalf("a slice that Write was given changed after %s", name)
				}
			}
		}
	}
	if checked < 100 {
		t.Fatalf("only %d calls of %s were checked", checked, key)
	}
}

// ioConstructors makes a wrapper of package io from kept readers and
// writers, by the key of its entry. It returns the arguments, grounded, and
// a function that makes the call. A nil argument comes now and then, and so
// does an argument that is a wrapper made before, so that a claim that the
// result is new is tested against it. The variadic functions are passed a
// spread slice, into which the harness puts poisoned values after the call.
var ioConstructors = map[string]func(rng *rand.Rand, k *keptLog, earlier []any) (given []*logic.Term, args []any, call func() any, after func()){
	"io.NopCloser": func(rng *rand.Rand, k *keptLog, earlier []any) ([]*logic.Term, []any, func() any, func()) {
		r := randomIOReader(rng, k, earlier)
		return []*logic.Term{reference(r == nil)}, []any{r}, func() any { return io.NopCloser(r) }, nil
	},
	"io.LimitReader": func(rng *rand.Rand, k *keptLog, earlier []any) ([]*logic.Term, []any, func() any, func()) {
		r, n := randomIOReader(rng, k, earlier), int64(rng.Intn(100)-10)
		return []*logic.Term{reference(r == nil), logic.IntLit(n)}, []any{r}, func() any { return io.LimitReader(r, n) }, nil
	},
	"io.TeeReader": func(rng *rand.Rand, k *keptLog, earlier []any) ([]*logic.Term, []any, func() any, func()) {
		r := randomIOReader(rng, k, earlier)
		var w io.Writer
		if rng.Intn(8) > 0 {
			w = randomKeptWriter(rng, k)
		}
		return []*logic.Term{reference(r == nil), reference(w == nil)}, []any{r, w}, func() any { return io.TeeReader(r, w) }, nil
	},
	"io.MultiReader": func(rng *rand.Rand, k *keptLog, earlier []any) ([]*logic.Term, []any, func() any, func()) {
		readers := make([]io.Reader, rng.Intn(4))
		for i := range readers {
			readers[i] = randomIOReader(rng, k, earlier)
		}
		args := make([]any, len(readers))
		for i, r := range readers {
			args[i] = r
		}
		return []*logic.Term{refsTerm(len(readers), func(i int) bool { return readers[i] == nil })}, args,
			func() any { return io.MultiReader(readers...) },
			func() {
				for i := range readers {
					readers[i] = poisoned{k}
				}
			}
	},
	"io.MultiWriter": func(rng *rand.Rand, k *keptLog, earlier []any) ([]*logic.Term, []any, func() any, func()) {
		writers := make([]io.Writer, rng.Intn(4))
		for i := range writers {
			if rng.Intn(10) > 0 {
				writers[i] = randomKeptWriter(rng, k)
			}
		}
		args := make([]any, len(writers))
		for i, w := range writers {
			args[i] = w
		}
		return []*logic.Term{refsTerm(len(writers), func(i int) bool { return writers[i] == nil })}, args,
			func() any { return io.MultiWriter(writers...) },
			func() {
				for i := range writers {
					writers[i] = poisoned{k}
				}
			}
	},
}

// randomIOReader returns a kept reader, nil now and then, or a wrapper
// that the harness made before.
func randomIOReader(rng *rand.Rand, k *keptLog, earlier []any) io.Reader {
	switch n := rng.Intn(10); {
	case n == 0:
		return nil
	case n == 1 && len(earlier) > 0:
		if r, ok := earlier[rng.Intn(len(earlier))].(io.Reader); ok {
			return r
		}
	}
	return randomKeptReader(rng, k)
}

// refsTerm grounds a slice of interface values by which are nil.
func refsTerm(n int, isNil func(int) bool) *logic.Term {
	seq := logic.Fill(logic.IntLit(0), logic.RefLit(0))
	for i := range n {
		seq = logic.Push(seq, reference(isNil(i)))
	}
	return seq
}

// checkTypeCall checks one call through a value against the shipped entry
// of its method: the requires with the states before, the call, and the
// ensures with the states after. It reports whether the requires held and
// the call was made.
func checkTypeCall(t *testing.T, pv *pkgVerifier, fn *funcInfo, k *keptLog, before, after map[*types.Var]map[string]bool,
	given map[*types.Var]*logic.Term, call func() []*logic.Term) bool {
	t.Helper()
	c := &sequenceCheck{t: t, pv: pv, fn: fn, before: before, after: after, given: given}
	if !c.holds(fn.requires) {
		return false
	}
	within(t, k, fn.obj.FullName(), func() { c.results = call() })
	c.ensure(fn.obj.FullName())
	return true
}

// checkIOEntries runs the entries of the functions of io that keep the
// readers and writers they are given. Each round makes a wrapper, when the
// requires holds, with no call active, and checks the ensures: that it is
// not nil, and, where the entry says so, that it is new and not closed.
// Then the wrapper is read from, written to, or closed at random, each call
// checked against the shipped entry of its method, with the kept values
// run only while a call of the wrapper is active, only through Read and
// Write, and never closed.
func checkIOEntries(t *testing.T, pv *pkgVerifier, pkg *types.Package, key string) {
	fn := contractOfKey(t, pv, pkg, key)
	construct := ioConstructors[key]
	if construct == nil {
		t.Fatalf("no harness calls %s; add one to ioConstructors", key)
	}
	read := shippedTypeContract(pv, pkg, "(Reader).Read")
	write := shippedTypeContract(pv, pkg, "(Writer).Write")
	closer := shippedTypeContract(pv, pkg, "(Closer).Close")
	rng := rand.New(rand.NewSource(1))
	checked := 0
	var earlier []any
	// One log for the whole run: a wrapper made in an earlier round may be
	// given to a later one, and what it keeps records into the log it was
	// made with, which every call must find active.
	k := &keptLog{}
	for range 300 {
		given, args, call, after := construct(rng, k, earlier)
		c := &sequenceCheck{t: t, pv: pv, fn: fn, given: map[*types.Var]*logic.Term{}}
		for i, param := range fn.params {
			c.given[param] = given[i]
		}
		if !c.holds(fn.requires) {
			continue
		}
		made := call()
		k.check()
		if after != nil {
			after()
		}
		// A value whose dynamic type is not a pointer has no identity in Go:
		// two NopClosers of one reader are ==. It is new unless the call
		// returned one of the wrappers it was given; one that is a pointer
		// is new unless it is one made before.
		fresh := true
		for _, other := range earlier {
			if reflect.ValueOf(made).Kind() == reflect.Pointer {
				fresh = fresh && other != made
			}
		}
		for _, arg := range args {
			fresh = fresh && arg != made
		}
		earlier = append(earlier, made)
		closed := false
		c.results = []*logic.Term{reference(made == nil)}
		c.fresh = map[*types.Var]bool{fn.results[0]: fresh}
		c.after = map[*types.Var]map[string]bool{fn.results[0]: {"closed": closed}}
		c.ensure(key)
		checked++
		for range 1 + rng.Intn(8) {
			switch value := made.(type) {
			case io.Reader:
				if rc, ok := value.(io.ReadCloser); ok && rng.Intn(4) == 0 {
					state := func(closed bool) map[*types.Var]map[string]bool {
						return map[*types.Var]map[string]bool{closer.receiver: {"closed": closed}}
					}
					if checkTypeCall(t, pv, closer, k, state(closed), state(true), map[*types.Var]*logic.Term{closer.receiver: reference(false)},
						func() []*logic.Term { return []*logic.Term{errorTerm(rc.Close())} }) {
						closed = true
					}
					continue
				}
				p := make([]byte, rng.Intn(65))
				checkTypeCall(t, pv, read, k, nil, nil, map[*types.Var]*logic.Term{read.params[0]: lengthTerm(len(p))},
					func() []*logic.Term {
						n, err := value.Read(p)
						return []*logic.Term{logic.IntLit(int64(n)), errorTerm(err)}
					})
			case io.Writer:
				p := make([]byte, rng.Intn(65))
				rng.Read(p)
				before := slices.Clone(p)
				checkTypeCall(t, pv, write, k, nil, nil, map[*types.Var]*logic.Term{write.params[0]: lengthTerm(len(p))},
					func() []*logic.Term {
						n, err := value.Write(p)
						return []*logic.Term{logic.IntLit(int64(n)), errorTerm(err)}
					})
				if !bytes.Equal(p, before) {
					t.Fatalf("the Write of what %s returned changed what it was given", key)
				}
			}
			if rng.Intn(4) == 0 {
				time.Sleep(time.Millisecond)
				k.check()
			}
		}
	}
	if checked < 100 {
		t.Fatalf("only %d calls of %s were checked", checked, key)
	}
}
