package vego

import (
	"go/types"
	"reflect"
	"slices"
	"sync"
	"sync/atomic"

	"golang.org/x/tools/go/analysis"
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
// A speculative problem never delays another: it takes a process only
// while no other asker waits and at most all processes but one serve
// speculation, and another asker that finds every process busy ends one
// that serves speculation (solver.Options.Speculative). A speculative
// verifier that fails, panics, or reads facts otherwise than the
// verification does wastes only work.

// maxSpeculative bounds the speculative verifiers of the whole process.
const maxSpeculative = 3

// speculating holds a place for each speculative verifier at work.
var speculating = make(chan struct{}, maxSpeculative)

// speculatedFunctions counts the functions that speculative verifiers
// verified, and speculationPanics the panics they dropped; the tests read
// them.
var speculatedFunctions, speculationPanics atomic.Int64

// speculativeFault, when set, runs before a speculative verifier verifies a
// function; the tests make it panic.
var speculativeFault func(fn *funcInfo)

// speculation is what the verification of a package and its speculative
// verifiers share: the index of the function the verification is at, and
// the next function from the end that a speculative verifier may take.
type speculation struct {
	at   atomic.Int64
	next atomic.Int64
	once sync.Once
	done atomic.Bool
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

	sp := &speculation{}
	sp.at.Store(-1)
	for range maxSpeculative {
		go func() {
			speculating <- struct{}{}
			if sp.done.Load() {
				<-speculating
				return
			}
			defer func() { <-speculating }()
			defer func() {
				if recover() != nil {
					speculationPanics.Add(1)
				}
			}()
			pv := verifier(&own)
			pv.speculative = true
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
						if recover() != nil {
							speculationPanics.Add(1)
						}
					}()
					if speculativeFault != nil {
						speculativeFault(fn)
					}
					pv.verified(fn)
					speculatedFunctions.Add(1)
				}()
			}
		}()
	}
	return sp
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
