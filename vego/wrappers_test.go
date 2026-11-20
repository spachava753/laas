package vego

import (
	"fmt"
	"go/types"
	"io"
	"log"
	"math/big"
	"math/rand"
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
	return w.inner.Write(p)
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
	return r.inner.Read(p)
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
	// fresh holds the results that the call made new.
	fresh map[*types.Var]bool
	bound int64
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
	env.givenRelation = func(name string, paths []logic.Path) (*logic.Term, error) {
		index, isResult := c.fn.resultNames[paths[0].Root]
		if name != "fresh" || len(paths[0].Steps) > 0 || !isResult {
			return nil, fmt.Errorf("the harness can tell only whether a result is fresh, not %s(%s)", name, paths[0].Root)
		}
		return logic.BoolLit(c.fresh[c.fn.results[index]]), nil
	}
	return env
}

// holds reports whether every clause holds.
func (c *sequenceCheck) holds(clauses []*clause) bool {
	env := c.env()
	eval := &evaluator{bound: c.bound, bindings: map[string]*big.Int{}}
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
	eval := &evaluator{bound: c.bound, bindings: map[string]*big.Int{}}
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

// loggerMethods prints with a method of a logger, by the key of its entry.
var loggerMethods = map[string]func(l *log.Logger, rng *rand.Rand){
	"(*log.Logger).Printf":  func(l *log.Logger, rng *rand.Rand) { l.Printf(randomFormat(rng), randomOperands(rng)...) },
	"(*log.Logger).Print":   func(l *log.Logger, rng *rand.Rand) { l.Print(randomOperands(rng)...) },
	"(*log.Logger).Println": func(l *log.Logger, rng *rand.Rand) { l.Println(randomOperands(rng)...) },
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
	if key != "log.New" && loggerMethods[key] == nil {
		t.Fatalf("no harness calls %s; add one to loggerMethods", key)
	}
	rng := rand.New(rand.NewSource(1))
	checked := 0
	var made []*log.Logger
	for range 300 {
		k := &keptLog{}
		var out io.Writer
		if rng.Intn(8) > 0 {
			out = randomKeptWriter(rng, k)
		}
		prefix := randomPrefix(rng)
		c := &sequenceCheck{t: t, pv: pv, fn: newFn, bound: int64(len(prefix)) + 2,
			given: map[*types.Var]*logic.Term{newFn.params[0]: reference(out == nil), newFn.params[1]: logic.Bytes(prefix), newFn.params[2]: logic.IntLit(0)}}
		if !c.holds(newFn.requires) {
			continue
		}
		// New runs nothing it is given: no call of a method is active.
		l := log.New(out, prefix, rng.Intn(64))
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
			done := k.enter()
			loggerMethods[key](l, rng)
			done()
			k.check()
			m.ensure(key)
			checked++
		}
	}
	if checked < 100 {
		t.Fatalf("only %d calls of %s were checked", checked, key)
	}
}
