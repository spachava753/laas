package vego

import (
	"errors"
	"fmt"
	"go/types"
	"reflect"
	"slices"
	"sync"
	"sync/atomic"
	"time"

	"golang.org/x/tools/go/analysis"

	"github.com/spachava753/laas/vego/internal/solver"
)

// The functions of a package are verified one after another, so a run of
// one package keeps one Z3 process busy at a time. Speculation uses the
// others. While the package is verified as always, up to maxSpeculative
// speculative verifiers in the whole process verify its functions from the
// end of the order that the verification has not reached. They only put
// answers into the solver's cache: what they find is thrown away, and they
// report nothing, export nothing, and count no costs. When the verification
// reaches such a function it asks the same questions, which the cache or a
// problem still being solved for a speculative verifier answers.
//
// So nothing but time depends on speculation. The verification asks the
// same questions in the same order with and without it, each answer is
// Z3's answer to the same text, which any process gives (see the premise of
// the cache in the solver), and a cached answer counts as Z3 counted it.
// That each answer the verification gets is Z3's rests on the invariant of
// the solver's pool of processes (see pool in the solver): a process ended
// to free its place for another asker is never handed to anyone again, and
// only a speculative asker can be told that its process was ended; a
// question of the verification told so, or a pool found inconsistent, is
// an internal error that fails the package, never an open answer.
// A speculative problem never delays another: it takes a process only
// while no other asker waits and at most all processes but one serve
// speculation, and another asker that finds every process busy ends one
// that serves speculation (solver.Options.Speculative). A speculative
// verifier that fails, panics, or reads facts otherwise than the
// verification does wastes only work, except for an error that says the
// answer cache or the solver cannot be trusted: it records that in the
// solver, and the verification of the package fails with it once its
// speculative verifiers have stopped (end).

// maxSpeculative bounds the speculative verifiers of the whole process.
const maxSpeculative = 3

// speculating holds a place for each speculative verifier at work.
var speculating = make(chan struct{}, maxSpeculative)

// speculativeRunning counts the speculative verifiers at work, which a
// test that changes a setting of the whole package waits for.
var speculativeRunning atomic.Int64

// stopped is panicked by a question of a speculative verifier whose
// package is verified, so that the verifier ends at once.
type stopped struct{}

// speculatedFunctions counts the functions that speculative verifiers
// verified, and speculationPanics the panics they dropped; the tests read
// them.
var speculatedFunctions, speculationPanics atomic.Int64

// verifying, when set, runs when the verification of a package begins
// its functions ("begin") and when it has verified them ("end"); the tests
// hold it there.
var verifying func(phase string)

// speculativeFault, when set, runs before a speculative verifier verifies a
// function; the tests make it panic.
var speculativeFault func(pv *pkgVerifier, fn *funcInfo)

// speculationBound bounds how long the verification of a package waits for
// its speculative verifiers to stop. They stop at once, so a wait that
// reaches it is a defect of vego, which fails the package.
var speculationBound = 10 * time.Minute

// speculation is what the verification of a package and its speculative
// verifiers share: the index of the function the verification is at, the
// next function from the end that a speculative verifier may take, and
// whether the verification has ended, which also closes stop. mu guards
// running, the speculative verifiers that have begun, which none does
// once done is set, and ended is signalled when the last one ends. z3 is
// the solver a speculative verifier used.
type speculation struct {
	at      atomic.Int64
	next    atomic.Int64
	once    sync.Once
	done    atomic.Bool
	stop    chan struct{}
	mu      sync.Mutex
	running int
	late    bool
	ended   *sync.Cond
	z3      atomic.Pointer[solver.Solver]
}

// begin registers a speculative verifier, unless the verification of the
// package has ended.
func (sp *speculation) begin() bool {
	sp.mu.Lock()
	defer sp.mu.Unlock()
	if sp.done.Load() {
		return false
	}
	sp.running++
	return true
}

// finish unregisters a speculative verifier.
func (sp *speculation) finish() {
	sp.mu.Lock()
	defer sp.mu.Unlock()
	sp.running--
	if sp.running == 0 {
		sp.ended.Broadcast()
	}
}

// end stops the speculative verifiers of the package and waits until
// those that began have ended. Each stops at once: a question of one ends
// with no answer, whether it waits for a process or for another asker's
// problem or is being solved, since stop is closed and every asker waiting
// for a process is woken (solver.Options.Stop); its next question panics
// with stopped. One that has not stopped within speculationBound is an
// internal error.
func (sp *speculation) end() error {
	sp.mu.Lock()
	sp.done.Store(true)
	close(sp.stop)
	sp.mu.Unlock()
	solver.WakeAll()
	timer := time.AfterFunc(speculationBound, func() {
		sp.mu.Lock()
		defer sp.mu.Unlock()
		sp.late = true
		sp.ended.Broadcast()
	})
	defer timer.Stop()
	sp.mu.Lock()
	defer sp.mu.Unlock()
	for sp.running > 0 && !sp.late {
		sp.ended.Wait()
	}
	if sp.running > 0 {
		return &solver.InternalError{Err: fmt.Errorf("%d speculative verifiers of the package did not stop within %v", sp.running, speculationBound)}
	}
	return nil
}

// untrusted returns what makes the solver of the package, the
// verification's or one a speculative verifier used, untrustworthy; see
// solver.Untrusted. sp may be nil.
func (sp *speculation) untrusted(s *solver.Solver) error {
	if s == nil && sp != nil {
		s = sp.z3.Load()
	}
	if s == nil {
		return nil
	}
	return s.Untrusted()
}

// take returns the index of the next function a speculative verifier may
// verify, or -1 when the verification has reached it or finished.
func (sp *speculation) take() int {
	i := sp.next.Add(-1)
	if sp.done.Load() || i <= sp.at.Load() {
		return -1
	}
	return int(i)
}

// speculate starts the speculative verifiers of a package, each made by
// verifier on a pass of its own, and returns what they share with the
// verification. It is called once the verification has collected the
// annotations, for a package with two functions to verify or more: a
// package with one has nothing to verify ahead, and most packages a run
// analyses, such as those of the standard library, have none.
//
// A speculative verifier must not touch what the verification writes
// while it runs. The facts of the package's dependencies are read here,
// leaving out those the verification exported of its own package while it
// collected, and a speculative verifier reads only those and the facts it
// exports itself; its reports and exports go nowhere else.
func speculate(pass *analysis.Pass, verifier func(*analysis.Pass) *pkgVerifier, trustPath string) *speculation {
	type objectKey struct {
		obj  types.Object
		kind reflect.Type
	}
	objects := map[objectKey]analysis.Fact{}
	var allObjects []analysis.ObjectFact
	for _, f := range pass.AllObjectFacts() {
		if f.Object.Pkg() != pass.Pkg {
			objects[objectKey{f.Object, reflect.TypeOf(f.Fact)}] = f.Fact
			allObjects = append(allObjects, f)
		}
	}
	type packageKey struct {
		pkg  *types.Package
		kind reflect.Type
	}
	packages := map[packageKey]analysis.Fact{}
	var all []analysis.PackageFact
	for _, f := range pass.AllPackageFacts() {
		if f.Package != pass.Pkg {
			packages[packageKey{f.Package, reflect.TypeOf(f.Fact)}] = f.Fact
			all = append(all, f)
		}
	}
	var mu sync.Mutex
	ownObjects := map[objectKey]analysis.Fact{}
	ownPackage := map[packageKey]analysis.Fact{}
	copyFact := func(found, into analysis.Fact) bool {
		reflect.ValueOf(into).Elem().Set(reflect.ValueOf(found).Elem())
		return true
	}
	own := *pass
	own.Report = func(analysis.Diagnostic) {}
	own.ExportObjectFact = func(obj types.Object, fact analysis.Fact) {
		mu.Lock()
		defer mu.Unlock()
		ownObjects[objectKey{obj, reflect.TypeOf(fact)}] = fact
	}
	own.ExportPackageFact = func(fact analysis.Fact) {
		mu.Lock()
		defer mu.Unlock()
		ownPackage[packageKey{pass.Pkg, reflect.TypeOf(fact)}] = fact
	}
	own.ImportObjectFact = func(obj types.Object, fact analysis.Fact) bool {
		key := objectKey{obj, reflect.TypeOf(fact)}
		if obj.Pkg() == pass.Pkg {
			mu.Lock()
			defer mu.Unlock()
			found, ok := ownObjects[key]
			return ok && copyFact(found, fact)
		}
		found, ok := objects[key]
		return ok && copyFact(found, fact)
	}
	own.ImportPackageFact = func(pkg *types.Package, fact analysis.Fact) bool {
		key := packageKey{pkg, reflect.TypeOf(fact)}
		if pkg == pass.Pkg {
			mu.Lock()
			defer mu.Unlock()
			found, ok := ownPackage[key]
			return ok && copyFact(found, fact)
		}
		found, ok := packages[key]
		return ok && copyFact(found, fact)
	}
	// What is listed is the dependencies' facts and the verifier's own.
	own.AllPackageFacts = func() []analysis.PackageFact {
		mu.Lock()
		defer mu.Unlock()
		listed := slices.Clone(all)
		for key, fact := range ownPackage {
			listed = append(listed, analysis.PackageFact{Package: key.pkg, Fact: fact})
		}
		return listed
	}
	own.AllObjectFacts = func() []analysis.ObjectFact {
		mu.Lock()
		defer mu.Unlock()
		listed := slices.Clone(allObjects)
		for key, fact := range ownObjects {
			listed = append(listed, analysis.ObjectFact{Object: key.obj, Fact: fact})
		}
		return listed
	}

	sp := &speculation{stop: make(chan struct{})}
	sp.ended = sync.NewCond(&sp.mu)
	sp.at.Store(-1)
	for range maxSpeculative {
		go func() {
			speculating <- struct{}{}
			speculativeRunning.Add(1)
			defer func() {
				speculativeRunning.Add(-1)
				<-speculating
			}()
			if !sp.begin() {
				return
			}
			defer sp.finish()
			var pv *pkgVerifier
			defer func() {
				if pv != nil && pv.z3 != nil {
					sp.z3.CompareAndSwap(nil, pv.z3)
				}
				if r := recover(); r != nil && r != (stopped{}) {
					speculationPanics.Add(1)
					sp.distrust(pv, r)
				}
			}()
			pv = verifier(&own)
			pv.speculative = true
			pv.stopSpeculation = sp.done.Load
			pv.speculationStop = sp.stop
			pv.loadTrust(trustPath)
			pv.collect()
			// Every speculative verifier of the package collects the same
			// order as the verification; the first one says where taking
			// starts.
			sp.once.Do(func() { sp.next.Store(int64(len(pv.order))) })
			pv.checkInvariantsDeclared()
			pv.exportInvariants()
			pv.checkTypeContracts()
			pv.exportTypeContracts()
			pv.exportStates()
			for i := sp.take(); i >= 0; i = sp.take() {
				fn := pv.order[i]
				if !fn.annotated() || fn.broken {
					continue
				}
				func() {
					defer func() {
						if r := recover(); r != nil {
							if r == (stopped{}) {
								panic(r)
							}
							speculationPanics.Add(1)
							sp.distrust(pv, r)
						}
					}()
					if speculativeFault != nil {
						speculativeFault(pv, fn)
					}
					pv.verified(fn)
					speculatedFunctions.Add(1)
				}()
			}
		}()
	}
	return sp
}

// distrust records in the solver an error that a speculative verifier
// panicked with and that says the answer cache or the solver cannot be
// trusted, which nobody else would read; see solver.Distrust. The solver is
// the one the package's verifiers share, which a verifier that has asked
// nothing yet has not opened.
func (sp *speculation) distrust(pv *pkgVerifier, r any) {
	err, ok := r.(error)
	if !ok || pv == nil || !(errors.As(err, new(*solver.CacheError)) || errors.As(err, new(*solver.InternalError))) {
		return
	}
	s := pv.z3
	if s == nil {
		var openErr error
		if s, openErr = solver.Open(pv.z3Path, pv.cacheDir); openErr != nil {
			return
		}
	}
	sp.z3.CompareAndSwap(nil, s)
	s.Distrust(err)
}

// countFuncs counts the functions that keep says to.
func countFuncs(fns []*funcInfo, keep func(*funcInfo) bool) int {
	n := 0
	for _, fn := range fns {
		if keep(fn) {
			n++
		}
	}
	return n
}
