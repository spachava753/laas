package solver

import (
	"errors"
	"fmt"
	"math/rand/v2"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"github.com/spachava753/laas/vego/internal/logic"
)

// The tests of the pool force the order of events with paused, at the
// points where the pool drops a lock or is about to take one, and use a Z3
// that answers at once: a delay of its own would let every preemption land
// while Z3 is solving, which is how the tests of the pool once missed a
// process ended after it had answered. A problem is slow only where a test
// needs one that is still being solved, and then it waits until the test
// lets it go or its process is killed.

// instant returns a Z3 of the pinned version that answers at once, unsat
// for a problem that asserts a negation, as Prove does, and sat otherwise,
// except that a problem whose text holds "999)" waits until the file it
// also returns exists.
func instant(t *testing.T) (path, release string) {
	t.Helper()
	dir := t.TempDir()
	path, release = filepath.Join(dir, "z3"), filepath.Join(dir, "go")
	script := `#!/bin/sh
if [ "$1" = "-version" ]; then
	echo "` + pinned + `"
	exit 0
fi
ans=sat
slow=
while IFS= read -r line; do
	case "$line" in
	*'(assert (not'*) ans=unsat ;;
	esac
	case "$line" in
	*'999)'*) slow=1 ;;
	esac
	case "$line" in
	*'(echo "'*)
		end=${line#*\(echo \"}
		end=${end%%\"*}
		if [ -n "$slow" ]; then
			while [ ! -e '` + release + `' ]; do sleep 0.01; done
		fi
		echo $ans; echo '(:reason-unknown "")'; echo '(:rlimit 7)'
		echo "$end"
		ans=sat
		slow=
		;;
	esac
done
`
	if err := os.WriteFile(path, []byte(script), 0o755); err != nil {
		t.Fatal(err)
	}
	return path, release
}

// pooled starts a solver of its own on instant with at most limit
// processes, and no quiet window unless a test sets one.
func pooled(t *testing.T, limit int) (s *Solver, release func()) {
	t.Helper()
	savedProcesses, savedQuiet := maxProcesses, quiet
	maxProcesses, quiet = limit, 0
	t.Cleanup(func() { maxProcesses, quiet = savedProcesses, savedQuiet })
	path, flag := instant(t)
	s, err := start(path)
	if err != nil {
		t.Fatal(err)
	}
	// It is among the solvers of the program, which WakeAll wakes.
	solversMu.Lock()
	solvers[path+"\x00"] = &solverOrError{s: s}
	solversMu.Unlock()
	t.Cleanup(func() {
		solversMu.Lock()
		delete(solvers, path+"\x00")
		solversMu.Unlock()
	})
	var once sync.Once
	release = func() {
		once.Do(func() {
			if err := os.WriteFile(flag, nil, 0o644); err != nil {
				t.Error(err)
			}
		})
	}
	t.Cleanup(func() {
		release()
		endIdle(s)
	})
	return s, release
}

// at sets paused for the test.
func at(t *testing.T, f func(point string, p *process)) {
	t.Helper()
	paused = f
	t.Cleanup(func() { paused = nil })
}

// proof is a goal with n in it, which instant proves; slow for an n
// that ends in 999.
func proof(n int64) *logic.Term {
	x := logic.Const("x", logic.Int)
	return logic.Le(x, logic.Add(x, logic.IntLit(n)))
}

// outcome is what a question got, and what it panicked with.
type outcome struct {
	result Result
	panic  any
	done   chan struct{}
}

// ask asks for a proof of proof(n) in a goroutine of its own.
func ask(s *Solver, n int64, opts Options) *outcome {
	o := &outcome{done: make(chan struct{})}
	go func() {
		defer close(o.done)
		defer func() { o.panic = recover() }()
		o.result = s.Prove(nil, proof(n), opts)
	}()
	return o
}

// within waits for a question for at most d, and reports whether it ended.
func (o *outcome) within(d time.Duration) bool {
	select {
	case <-o.done:
		return true
	case <-time.After(d):
		return false
	}
}

// internal reports whether a question panicked with an InternalError.
func (o *outcome) internal() bool {
	e, ok := o.panic.(error)
	return ok && errors.As(e, new(*InternalError))
}

// until waits for a condition for at most ten seconds.
func until(t *testing.T, what string, cond func() bool) {
	t.Helper()
	for deadline := time.Now().Add(10 * time.Second); !cond(); time.Sleep(time.Millisecond) {
		if time.Now().After(deadline) {
			t.Fatalf("waited ten seconds for %s", what)
		}
	}
}

// signal is a channel that is closed once.
type signal struct {
	once sync.Once
	ch   chan struct{}
}

func newSignal() *signal { return &signal{ch: make(chan struct{})} }
func (s *signal) fire()  { s.once.Do(func() { close(s.ch) }) }

// mainWaiting returns how many askers that are not speculative wait in
// acquire.
func (s *Solver) waiting() int {
	s.pool.mu.Lock()
	defer s.pool.mu.Unlock()
	return s.pool.mainWaiting
}

// TestPreemption checks how the pool ends a process that serves
// speculation to free its place for another asker, at each moment a
// preemption can come, and that only a speculative asker is ever told so.
func TestPreemption(t *testing.T) {
	// The return of a held process to the idle ones (release): a process
	// ended to free its place after it answered a speculative problem, and
	// before it was returned, serves no other asker. The verification's
	// first problem holds one process once answered, a speculative problem
	// holds the other once answered, and a second question of the
	// verification finds every process busy and ends the speculative one; it
	// must get Z3's answer from another process. At bb4e7be, which read
	// whether the process was ended before taking the lock, the second
	// question got unknown.
	t.Run("after an answer", func(t *testing.T) {
		s, _ := pooled(t, 2)
		held, entered := newSignal(), make(chan *process, 2)
		var releases atomic.Int64
		at(t, func(point string, p *process) {
			if point != "release" {
				return
			}
			switch releases.Add(1) {
			case 1:
				entered <- p
				<-held.ch
			case 2:
				entered <- p
				for deadline := time.Now().Add(10 * time.Second); !p.preempted.Load(); time.Sleep(time.Millisecond) {
					if time.Now().After(deadline) {
						t.Error("the speculative process was never ended for the verification's question")
						return
					}
				}
			}
		})
		defer held.fire()
		first := ask(s, 1, Options{})
		<-entered
		speculative := ask(s, 2, Options{Speculative: true})
		<-entered
		second := ask(s, 3, Options{})
		if !second.within(10 * time.Second) {
			t.Fatal("the question that ended the speculative process got no answer in ten seconds")
		}
		held.fire()
		<-first.done
		<-speculative.done
		if second.panic != nil || second.result != Proved {
			t.Errorf("the question that ended the speculative process got %v (panic %v), want Z3's answer, proved", second.result, second.panic)
		}
		if first.result != Proved || speculative.result != Proved || first.panic != nil || speculative.panic != nil {
			t.Errorf("the other questions got %v and %v (panics %v, %v), want proved", first.result, speculative.result, first.panic, speculative.panic)
		}
	})
	// The same return by its other caller: a speculative asker that takes a
	// process, finds its problem being solved for another asker, and returns
	// the process, while a question of the verification ends that process
	// to free its place. The process must be ended, not returned to the idle
	// ones.
	t.Run("before solving", func(t *testing.T) {
		s, _ := pooled(t, 2)
		held, entered := newSignal(), make(chan *process, 2)
		var releases atomic.Int64
		at(t, func(point string, p *process) {
			if point != "release" {
				return
			}
			switch releases.Add(1) {
			case 1:
				// The first problem stays in flight while its asker is held.
				entered <- p
				<-held.ch
			case 2:
				entered <- p
				for deadline := time.Now().Add(10 * time.Second); !p.preempted.Load(); time.Sleep(time.Millisecond) {
					if time.Now().After(deadline) {
						t.Error("the speculative process was never ended for the verification's question")
						return
					}
				}
			}
		})
		defer held.fire()
		first := ask(s, 1, Options{})
		<-entered
		// The same problem: the speculative asker takes a process, finds the
		// flight, and returns the process.
		speculative := ask(s, 1, Options{Speculative: true})
		<-entered
		second := ask(s, 3, Options{})
		if !second.within(10 * time.Second) {
			t.Fatal("the question that ended the speculative process got no answer in ten seconds")
		}
		held.fire()
		<-first.done
		<-speculative.done
		if second.panic != nil || second.result != Proved {
			t.Errorf("the question that ended the speculative process got %v (panic %v), want proved", second.result, second.panic)
		}
		if first.result != Proved || speculative.result != Proved {
			t.Errorf("the other questions got %v and %v (panics %v, %v), want proved", first.result, speculative.result, first.panic, speculative.panic)
		}
	})
	// Preemption (acquire): a question of the verification that finds every
	// process busy ends one that is solving a speculative problem, whose
	// asker gets no answer and no fault, and gets its own answer without
	// waiting for that problem.
	t.Run("while solving", func(t *testing.T) {
		s, release := pooled(t, 2)
		running := make(chan *process, 4)
		at(t, func(point string, p *process) {
			if point == "run" {
				running <- p
			}
		})
		speculative := ask(s, 999, Options{Speculative: true})
		<-running
		busy := ask(s, 1999, Options{})
		<-running
		urgent := ask(s, 3, Options{})
		if !urgent.within(10 * time.Second) {
			t.Fatal("the question that found every process busy got no answer in ten seconds")
		}
		if !speculative.within(10 * time.Second) {
			t.Fatal("the speculative problem was not ended")
		}
		release()
		<-busy.done
		if urgent.result != Proved || urgent.panic != nil {
			t.Errorf("the question that found every process busy got %v (panic %v), want proved", urgent.result, urgent.panic)
		}
		if speculative.result != Unknown || speculative.panic != nil {
			t.Errorf("the speculative problem, whose process was ended, got %v (panic %v), want unknown", speculative.result, speculative.panic)
		}
		if busy.result != Proved {
			t.Errorf("the slow question got %v (panic %v), want proved", busy.result, busy.panic)
		}
	})
	// The start of a process for a speculative problem (acquire): it cannot
	// be ended until it can answer, and an asker that found every process
	// busy while it was being started ends it as soon as it can, instead of
	// waiting for some later change of the pool.
	t.Run("once registered", func(t *testing.T) {
		s, release := pooled(t, 2)
		held, entered := newSignal(), make(chan struct{}, 1)
		starting := newSignal()
		var releases, spawns atomic.Int64
		at(t, func(point string, p *process) {
			switch {
			case point == "release" && releases.Add(1) == 1:
				entered <- struct{}{}
				<-held.ch
			case point == "spawn" && spawns.Add(1) == 2:
				// Hold the speculative asker's start until the question of
				// the verification waits.
				starting.fire()
				until(t, "the question of the verification to wait", func() bool { return s.waiting() == 1 })
			}
		})
		defer held.fire()
		first := ask(s, 1, Options{})
		<-entered
		speculative := ask(s, 999, Options{Speculative: true})
		<-starting.ch
		urgent := ask(s, 3, Options{})
		if !urgent.within(5 * time.Second) {
			t.Error("the question that found every process busy waited for more than five seconds while a speculative problem held a process")
		}
		held.fire()
		release()
		<-first.done
		<-urgent.done
		<-speculative.done
		if urgent.result != Proved || urgent.panic != nil {
			t.Errorf("the question that found every process busy got %v (panic %v), want proved", urgent.result, urgent.panic)
		}
		if speculative.result != Unknown || speculative.panic != nil {
			t.Errorf("the speculative problem got %v (panic %v), want unknown, its process ended", speculative.result, speculative.panic)
		}
	})
	// A question of the verification never reads a process ended for
	// another asker as an open answer: whatever ended it, the asker, a
	// waiter on its problem, and every later question fail with an internal
	// error. The process is ended here by hand, which
	// stands for any defect that would.
	t.Run("of the verification", func(t *testing.T) {
		s, _ := pooled(t, 2)
		running := make(chan *process, 4)
		var misses atomic.Int64
		at(t, func(point string, p *process) {
			switch point {
			case "run":
				running <- p
			case "missed":
				misses.Add(1)
			}
		})
		first := ask(s, 999, Options{})
		p := <-running
		waiter := ask(s, 999, Options{})
		// The waiter has found no answer kept; it then finds the flight.
		until(t, "the second asker to look for the first one's problem", func() bool { return misses.Load() == 2 })
		time.Sleep(50 * time.Millisecond)
		s.pool.mu.Lock()
		p.preempted.Store(true)
		_ = p.cmd.Process.Kill()
		s.pool.mu.Unlock()
		for _, o := range []*outcome{first, waiter} {
			if !o.within(10 * time.Second) {
				t.Fatal("a question whose process was ended got nothing in ten seconds")
			}
			if !o.internal() {
				t.Errorf("a question whose process was ended for another asker got %v (panic %v), want an internal error", o.result, o.panic)
			}
		}
		if later := ask(s, 5, Options{}); !later.within(10*time.Second) || !later.internal() {
			t.Errorf("a later question got %v (panic %v), want the internal error", later.result, later.panic)
		}
	})
	// The same for the solving again of an answer read from disk (watch):
	// it fails with an internal error, where it once returned without a
	// word.
	t.Run("of a watched answer", func(t *testing.T) {
		z3 := z3Binary(t)
		dir := cacheDir(t)
		cached(t, z3, dir).Prove(nil, proof(1), Options{})
		saved := watchRate
		watchRate = 1
		defer func() { watchRate = saved }()
		s := cached(t, z3, dir)
		at(t, func(point string, p *process) {
			if point == "run" {
				s.pool.mu.Lock()
				p.preempted.Store(true)
				_ = p.cmd.Process.Kill()
				s.pool.mu.Unlock()
			}
		})
		o := ask(s, 1, Options{})
		if !o.within(10*time.Second) || !o.internal() {
			t.Errorf("a watched answer whose process was ended got %v (panic %v), want an internal error", o.result, o.panic)
		}
	})
}

// TestInconsistentPool checks that a pool found inconsistent fails every
// question, of a speculative asker that found it and of an asker that was
// waiting for a process, within a bound, instead of serving the process or
// leaving the asker waiting. An ended process is put among the idle ones
// by hand, which stands for any defect that would.
func TestInconsistentPool(t *testing.T) {
	s, _ := pooled(t, 2)
	held, entered := newSignal(), make(chan struct{}, 2)
	var releases atomic.Int64
	at(t, func(point string, p *process) {
		if point == "release" && releases.Add(1) <= 2 {
			entered <- struct{}{}
			<-held.ch
		}
	})
	defer held.fire()
	first, second := ask(s, 1, Options{}), ask(s, 2, Options{})
	<-entered
	<-entered
	waiter := ask(s, 3, Options{})
	until(t, "the third question to wait", func() bool { return s.waiting() == 1 })
	dead, err := s.spawn()
	if err != nil {
		t.Fatal(err)
	}
	_ = dead.cmd.Process.Kill()
	dead.preempted.Store(true)
	s.pool.mu.Lock()
	s.pool.idle = append(s.pool.idle, dead)
	s.pool.mu.Unlock()
	speculative := ask(s, 4, Options{Speculative: true})
	for _, o := range []*outcome{speculative, waiter} {
		if !o.within(5 * time.Second) {
			t.Fatal("a question waited for more than five seconds on an inconsistent pool")
		}
		if !o.internal() {
			t.Errorf("a question on an inconsistent pool got %v (panic %v), want an internal error", o.result, o.panic)
		}
	}
	if later := ask(s, 5, Options{}); !later.within(5*time.Second) || !later.internal() {
		t.Errorf("a later question got %v (panic %v), want the internal error", later.result, later.panic)
	}
	// An asker that leaves acquire with the error no longer counts as
	// waiting, or speculative askers would wait for ever.
	if n := s.waiting(); n != 0 {
		t.Errorf("%d askers count as waiting after the error", n)
	}
	held.fire()
	<-first.done
	<-second.done
	s.pool.mu.Lock()
	s.pool.idle = slices.DeleteFunc(s.pool.idle, func(p *process) bool { return p == dead })
	s.pool.mu.Unlock()
}

// TestStoppedSpeculation checks that a speculative question whose answer is
// no longer wanted ends at once wherever it is: waiting for a process
// behind questions that hold every one, sleeping out the quiet window,
// waiting for another asker's problem, or being solved, whose process is
// then ended.
func TestStoppedSpeculation(t *testing.T) {
	stopped := func(t *testing.T, s *Solver, n int64, ready func()) {
		t.Helper()
		stop := make(chan struct{})
		o := ask(s, n, Options{Speculative: true, Stop: stop})
		ready()
		close(stop)
		WakeAll()
		if !o.within(5 * time.Second) {
			t.Fatal("a stopped speculative question did not end within five seconds")
		}
		if o.result != Unknown || o.panic != nil {
			t.Errorf("a stopped speculative question got %v (panic %v), want unknown", o.result, o.panic)
		}
	}
	t.Run("waiting for a process", func(t *testing.T) {
		s, release := pooled(t, 2)
		running := make(chan *process, 4)
		at(t, func(point string, p *process) {
			if point == "run" {
				running <- p
			}
		})
		a, b := ask(s, 999, Options{}), ask(s, 1999, Options{})
		<-running
		<-running
		stopped(t, s, 3, func() { time.Sleep(100 * time.Millisecond) })
		release()
		<-a.done
		<-b.done
	})
	t.Run("in the quiet window", func(t *testing.T) {
		s, _ := pooled(t, 2)
		quiet = time.Hour
		s.pool.mu.Lock()
		s.pool.busy = time.Now()
		s.pool.mu.Unlock()
		stopped(t, s, 3, func() { time.Sleep(100 * time.Millisecond) })
	})
	t.Run("waiting for another asker's problem", func(t *testing.T) {
		s, release := pooled(t, 3)
		running := make(chan *process, 4)
		at(t, func(point string, p *process) {
			if point == "run" {
				running <- p
			}
		})
		a := ask(s, 999, Options{})
		<-running
		stopped(t, s, 999, func() {
			until(t, "the speculative question to wait", func() bool {
				s.pool.mu.Lock()
				defer s.pool.mu.Unlock()
				return len(s.pool.idle) == 1
			})
		})
		release()
		<-a.done
	})
	t.Run("being solved", func(t *testing.T) {
		s, _ := pooled(t, 2)
		running := make(chan *process, 4)
		at(t, func(point string, p *process) {
			if point == "run" {
				running <- p
			}
		})
		var p *process
		stopped(t, s, 999, func() { p = <-running; time.Sleep(50 * time.Millisecond) })
		until(t, "the stopped process to end", func() bool {
			s.pool.mu.Lock()
			defer s.pool.mu.Unlock()
			return p.ended && s.pool.live == 0
		})
	})
}

// TestConcurrentQuestions asks a few thousand questions with known answers, of
// askers of both kinds at once, some of them the same text, of a Z3 that
// answers at once, while the pool sleeps at random wherever it has dropped
// a lock or is about to take one. Every question of the verification must
// get its known answer, and nothing may fault. On bb4e7be with only
// questions of the verification that get errPreempted made a fault, it
// faulted on every run tried (see the ROADMAP).
func TestConcurrentQuestions(t *testing.T) {
	s, release := pooled(t, 3)
	// No problem waits.
	release()
	at(t, func(string, *process) {
		if rand.IntN(4) == 0 {
			time.Sleep(time.Duration(rand.IntN(200)) * time.Microsecond)
		}
	})
	x := logic.Const("x", logic.Int)
	known := func(n int, speculative bool) (got, want Result) {
		opts := Options{Speculative: speculative}
		if n%2 == 0 {
			return s.Prove(nil, logic.Le(x, logic.Add(x, logic.IntLit(int64(n)))), opts), Proved
		}
		return s.Check([]*logic.Term{logic.Lt(x, logic.Add(x, logic.IntLit(int64(n))))}, opts), Refuted
	}
	const askers, each = 3, 400
	var wrong, faults atomic.Int64
	var first atomic.Value
	deadline := time.Now().Add(time.Minute)
	var wg sync.WaitGroup
	for m := range askers {
		wg.Go(func() {
			for i := range each {
				if time.Now().After(deadline) {
					return
				}
				func() {
					defer func() {
						if r := recover(); r != nil {
							faults.Add(1)
							first.CompareAndSwap(nil, fmt.Sprint(r))
						}
					}()
					// A third of the texts are shared with other askers.
					n := 2 + m*each + i
					if i%3 == 0 {
						n = 2 + i
					}
					if got, want := known(n, false); got != want {
						wrong.Add(1)
						first.CompareAndSwap(nil, fmt.Sprintf("question %d got %v, want %v", n, got, want))
					}
				}()
			}
		})
	}
	for k := range askers {
		wg.Go(func() {
			for i := range each {
				if time.Now().After(deadline) {
					return
				}
				func() {
					defer func() {
						if r := recover(); r != nil {
							faults.Add(1)
							first.CompareAndSwap(nil, fmt.Sprint(r))
						}
					}()
					n := 2 + (askers+k)*each + i
					if i%2 == 0 {
						n = 2 + i
					}
					if got, want := known(n, true); got != want && got != Unknown {
						wrong.Add(1)
						first.CompareAndSwap(nil, fmt.Sprintf("speculative question %d got %v, want %v or unknown", n, got, want))
					}
				}()
			}
		})
	}
	wg.Wait()
	if time.Now().After(deadline) {
		t.Error("the questions took more than a minute")
	}
	if wrong.Load() > 0 || faults.Load() > 0 {
		t.Errorf("%d questions got a wrong answer and %d faulted; the first: %v", wrong.Load(), faults.Load(), first.Load())
	}
}

// TestSpeculativeDrift checks that an answer on disk that Z3 contradicts,
// found only by a speculative asker's solving it again, is not dropped with
// the asker: Untrusted returns it, which the verification of the package
// reads once its speculative verifiers have stopped, and every later
// question of another asker fails with it.
func TestSpeculativeDrift(t *testing.T) {
	z3 := z3Binary(t)
	dir := cacheDir(t)
	key := Script([]*logic.Term{logic.Not(proof(1))}, Options{}) + "\x00"
	cached(t, z3, dir).disk.write(key, reply{check: []string{"sat", `(:reason-unknown "")`, "(:rlimit 7)"}})
	saved := watchRate
	watchRate = 1
	defer func() { watchRate = saved }()
	s := cached(t, z3, dir)
	if o := ask(s, 1, Options{Speculative: true}); !o.within(10 * time.Second) {
		t.Fatal("the speculative question did not end")
	}
	var cache *CacheError
	if err := s.Untrusted(); !errors.As(err, &cache) || !strings.Contains(err.Error(), "otherwise") {
		t.Fatalf("Untrusted returned %v, want the drift the speculative asker found", err)
	}
	if message := cacheFailure(func() { s.Prove(nil, proof(2), Options{}) }); !strings.Contains(message, "otherwise") {
		t.Errorf("a later question got %q, want the drift", message)
	}
}
