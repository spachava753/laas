package vego

import (
	"math/big"
	"math/rand"
	"strings"
	"sync"
	"testing"
	"time"

	"go/types"

	"github.com/spachava753/laas/vego/internal/logic"
)

// lockMethods calls the methods of sync.Mutex and sync.RWMutex that have
// shipped entries, by the name in the key, and reports what TryLock and
// TryRLock returned.
var lockMethods = map[string]func(m *sync.Mutex, rw *sync.RWMutex) bool{
	"(*sync.Mutex).Lock":      func(m *sync.Mutex, _ *sync.RWMutex) bool { m.Lock(); return false },
	"(*sync.Mutex).TryLock":   func(m *sync.Mutex, _ *sync.RWMutex) bool { return m.TryLock() },
	"(*sync.Mutex).Unlock":    func(m *sync.Mutex, _ *sync.RWMutex) bool { m.Unlock(); return false },
	"(*sync.RWMutex).Lock":    func(_ *sync.Mutex, rw *sync.RWMutex) bool { rw.Lock(); return false },
	"(*sync.RWMutex).TryLock": func(_ *sync.Mutex, rw *sync.RWMutex) bool { return rw.TryLock() },
	"(*sync.RWMutex).Unlock":  func(_ *sync.Mutex, rw *sync.RWMutex) bool { rw.Unlock(); return false },
	"(*sync.RWMutex).RLock":   func(_ *sync.Mutex, rw *sync.RWMutex) bool { rw.RLock(); return false },
	"(*sync.RWMutex).TryRLock": func(_ *sync.Mutex, rw *sync.RWMutex) bool {
		return rw.TryRLock()
	},
	"(*sync.RWMutex).RUnlock": func(_ *sync.Mutex, rw *sync.RWMutex) bool { rw.RUnlock(); return false },
}

// lockGhost is what the harness knows of the goroutine that calls: whether
// it holds the mutex, and for an RWMutex whether it holds a read lock.
type lockGhost struct{ held, rheld bool }

// after returns what the calling goroutine holds once a method returned,
// from what the method did, not from its entry.
func (g lockGhost) after(method string, ok bool) lockGhost {
	switch method {
	case "Lock":
		g.held = true
	case "Unlock":
		g.held = false
	case "TryLock":
		g.held = g.held || ok
	case "RLock":
		g.rheld = true
	case "RUnlock":
		g.rheld = false
	case "TryRLock":
		g.rheld = g.rheld || ok
	}
	return g
}

// checkLockEntry runs the entry of one method of a mutex against sync. A
// random sequence of the methods of the type is called on one mutex, each
// only when its entry's requires holds of what the harness knows, while
// another goroutine locks and unlocks the same mutex whenever it can. Every
// call must return within a bound, and the entry's ensures must hold of
// what the harness knows before and after it and of what it returned.
func checkLockEntry(t *testing.T, pv *pkgVerifier, pkg *types.Package, key string) {
	receiver, method, _ := strings.Cut(strings.TrimPrefix(key, "(*sync."), ").")
	typeName := pkg.Scope().Lookup(receiver).(*types.TypeName)
	found, _, _ := types.LookupFieldOrMethod(types.NewPointer(typeName.Type()), true, pkg, method)
	callee, ok := found.(*types.Func)
	if !ok {
		t.Fatalf("%s has no method %s", receiver, method)
	}
	fn := pv.trustedContract(callee)
	for _, defect := range fn.defects {
		t.Errorf("contract cannot be used: %s", defect)
	}
	if lockMethods[key] == nil {
		t.Fatalf("no harness calls %s; add one to lockMethods", key)
	}
	var others []string
	for other := range lockMethods {
		if strings.HasPrefix(other, "(*sync."+receiver+").") {
			others = append(others, other)
		}
	}
	contracts := map[string]*funcInfo{}
	for _, other := range others {
		_, name, _ := strings.Cut(other, ").")
		found, _, _ := types.LookupFieldOrMethod(types.NewPointer(typeName.Type()), true, pkg, name)
		contracts[other] = pv.trustedContract(found.(*types.Func))
	}
	var m sync.Mutex
	var rw sync.RWMutex
	stop := make(chan struct{})
	contending := make(chan struct{})
	go func() {
		defer close(contending)
		for i := 0; ; i++ {
			select {
			case <-stop:
				return
			default:
			}
			switch {
			case receiver == "Mutex":
				m.Lock()
				time.Sleep(time.Microsecond)
				m.Unlock()
			case i%2 == 0:
				rw.Lock()
				time.Sleep(time.Microsecond)
				rw.Unlock()
			default:
				rw.RLock()
				time.Sleep(time.Microsecond)
				rw.RUnlock()
			}
		}
	}()
	var ghost lockGhost
	// The other goroutine may be waiting for a lock the harness holds, so
	// the harness lets go of it before it waits for the other goroutine.
	defer func() {
		close(stop)
		switch {
		case receiver == "Mutex" && ghost.held:
			m.Unlock()
		case ghost.held:
			rw.Unlock()
		case ghost.rheld:
			rw.RUnlock()
		}
		// After a call that did not return, the other goroutine may wait
		// for ever; the test has failed then, and the goroutine is left.
		select {
		case <-contending:
		case <-time.After(5 * time.Second):
		}
	}()
	rng := rand.New(rand.NewSource(1))
	checked := 0
	for range 1500 {
		other := others[rng.Intn(len(others))]
		contract := contracts[other]
		param := contract.params[0]
		state := func(g lockGhost) func(*types.Var, string, logic.When) *logic.Term {
			return func(_ *types.Var, name string, _ logic.When) *logic.Term {
				return map[bool]*logic.Term{true: logic.True(), false: logic.False()}[map[string]bool{"held": g.held, "rheld": g.rheld}[name]]
			}
		}
		before := ghost
		env := &specEnv{
			v: &fnVerifier{pkgVerifier: pv, fn: contract}, fn: contract,
			given:      map[*types.Var]*logic.Term{param: logic.Pair(logic.RefLit(1), logic.IntLit(0))},
			givenPost:  map[*types.Var]*logic.Term{param: logic.Pair(logic.RefLit(1), logic.IntLit(0))},
			givenState: state(before),
		}
		eval := &evaluator{bindings: map[string]*big.Int{}}
		satisfied := true
		for _, c := range contract.requires {
			formula, err := pv.res.Formula(c.node, env)
			if err != nil {
				t.Fatalf("%s: requires %q: %v", other, c.text, err)
			}
			satisfied = satisfied && eval.holds(formula)
		}
		if !satisfied {
			continue
		}
		done := make(chan bool)
		go func() { done <- lockMethods[other](&m, &rw) }()
		var ok bool
		select {
		case ok = <-done:
		case <-time.After(5 * time.Second):
			t.Fatalf("%s did not return within 5s, with the calling goroutine holding %+v", other, before)
		}
		_, name, _ := strings.Cut(other, ").")
		ghost = before.after(name, ok)
		if other != key {
			continue
		}
		checked++
		// The ensures speaks of the state before, plainly, and after,
		// primed.
		env.givenState = func(p *types.Var, s string, when logic.When) *logic.Term {
			if when == logic.Primed {
				return state(ghost)(p, s, when)
			}
			return state(before)(p, s, when)
		}
		env.givenResults = []*logic.Term{map[bool]*logic.Term{true: logic.True(), false: logic.False()}[ok]}
		for _, c := range contract.ensures {
			formula, err := pv.res.Formula(c.node, env)
			if err != nil {
				t.Fatalf("ensures %q: %v", c.text, err)
			}
			if !eval.holds(formula) {
				t.Fatalf("ensures %q is false after %s returned %v, with the calling goroutine holding %+v before and %+v after",
					c.text, other, ok, before, ghost)
			}
		}
	}
	if checked < 30 {
		t.Fatalf("only %d calls of %s satisfied its requires; the harness does not exercise the contract", checked, key)
	}
}
