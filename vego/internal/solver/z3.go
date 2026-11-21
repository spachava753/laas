package solver

import (
	"bufio"
	"errors"
	"fmt"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"runtime"
	"slices"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"
)

// Version is the version of Z3 that vego is built for. Another version may
// prove different obligations, or the same ones with different effort, so
// it is refused.
const Version = "5.4.1"

// installHint says how to get the pinned version.
const installHint = "install Z3 " + Version + " from https://github.com/Z3Prover/z3/releases/tag/z3-" + Version +
	" and put its bin/z3 on PATH, or name it with -vego.z3"

// Processes returns how many Z3 processes a solver keeps at most.
func Processes() int { return maxProcesses }

// maxProcesses bounds the Z3 processes one run of vego keeps. It is memory,
// not processors, that runs out first when several large problems are
// solved at once.
var maxProcesses = min(runtime.GOMAXPROCS(0), 4)

// memoryLimit is the memory, in megabytes, that one Z3 process may use. A
// problem that needs more is not proved.
const memoryLimit = 1024

// wallLimit is how long one problem may take before the process is killed
// and the problem counts as not proved. The resource limit of every
// problem normally stops Z3 long before.
var wallLimit = 5 * time.Minute

// settings are the options every Z3 process runs with. They are fixed on
// the command line for the life of the process: an option a problem set
// would survive the reset before the next problem. Every problem sets its
// own resource limit.
var settings = []string{
	"-in", "-smt2", "-memory:" + strconv.Itoa(memoryLimit),
	"smt.random_seed=0",
	"sat.random_seed=0",
}

// A Solver hands problems to a pool of Z3 processes of the pinned version.
// It is safe for concurrent use.
type Solver struct {
	path string
	// pool holds the processes; see acquire.
	pool pool
	// flights holds the problems being solved, by key, so that a problem
	// asked while it is solved is not solved twice; see answer.
	flightsMu sync.Mutex
	flights   map[string]*flight
	// untrusted holds the first CacheError raised for a speculative asker,
	// and broken the first InternalError raised for any asker; see answer
	// and Untrusted.
	untrusted atomic.Pointer[CacheError]
	broken    atomic.Pointer[InternalError]
	// disk keeps answers between runs when a cache directory is given;
	// see disk.go.
	disk *disk
	// answers holds what Z3 answered to each problem whose answer does
	// not depend on the machine, by the text of the problem and the names
	// whose values were asked; see answer. queue holds the keys in the
	// order they were added, and held the bytes of the keys kept.
	mu      sync.Mutex
	answers map[string]answer
	queue   []string
	held    int
}

// cacheBytes bounds the text of the problems whose answers a solver keeps.
// The oldest are forgotten first.
var cacheBytes = 256 << 20

var (
	solversMu sync.Mutex
	solvers   = map[string]*solverOrError{}
)

type solverOrError struct {
	s     *Solver
	err   error
	cache bool
}

// New returns the solver that runs the Z3 binary at path, or the one named
// z3 on PATH if path is empty, and keeps answers only in the process; see
// Open.
func New(path string) (*Solver, error) { return Open(path, "") }

// Open returns the solver that runs the Z3 binary at path, or the one named
// z3 on PATH if path is empty, and keeps answers between runs in the cache
// directory when one is given. It fails unless the binary is Z3 of exactly
// the pinned version, and, with a cache, unless the directory may hold one
// and the binary is the Z3 that answers. Solvers are shared: one binary and
// one cache have one pool of processes in a program. The error says why and
// how to install Z3 the first time; later calls for the same binary get a
// short error that refers to it, so that a run over many packages says it
// once.
func Open(path, cache string) (*Solver, error) {
	solversMu.Lock()
	defer solversMu.Unlock()
	if found, ok := solvers[path+"\x00"+cache]; ok {
		if found.err != nil {
			name := "the z3 on PATH"
			if path != "" {
				name = path
			}
			if found.cache {
				return nil, fmt.Errorf("the answer cache %s cannot be used, as said for another package", cache)
			}
			return nil, fmt.Errorf("proving obligations needs Z3 %s, and %s cannot be used, as said for another package; %s", Version, name, installHint)
		}
		return found.s, nil
	}
	s, err := start(path)
	cacheFailed := false
	if err == nil && cache != "" {
		err = s.openCache(cache)
		cacheFailed = err != nil
	}
	if err != nil {
		s = nil
	}
	solvers[path+"\x00"+cache] = &solverOrError{s, err, cacheFailed}
	return s, err
}

// CacheDir returns the directory of the answer cache, or "" for none.
func (s *Solver) CacheDir() string {
	if s.disk == nil {
		return ""
	}
	return s.disk.root
}

// openCache opens the cache directory and identifies the first process,
// which names the directory its answers are kept in.
func (s *Solver) openCache(cache string) error {
	d, err := openDisk(cache)
	if err != nil {
		return err
	}
	s.disk = d
	p, err := s.acquire(asker{})
	if err != nil {
		return err
	}
	s.release(p)
	return nil
}

// start finds the binary and checks its version.
func start(path string) (*Solver, error) {
	resolved := path
	if path == "" {
		found, err := exec.LookPath("z3")
		if err != nil {
			return nil, fmt.Errorf("proving obligations needs Z3 %s, and no z3 was found on PATH; %s", Version, installHint)
		}
		resolved = found
	}
	if abs, err := filepath.Abs(resolved); err == nil {
		resolved = abs
	}
	out, err := exec.Command(resolved, "-version").Output()
	if err != nil {
		return nil, fmt.Errorf("proving obligations needs Z3 %s, and %s could not be run: %v; %s", Version, resolved, err, installHint)
	}
	version := regexp.MustCompile(`^Z3 version (\S+)`).FindStringSubmatch(string(out))
	switch {
	case version == nil:
		return nil, fmt.Errorf("proving obligations needs Z3 %s, and %s does not say which version of Z3 it is (it printed %q); %s",
			Version, resolved, strings.TrimSpace(string(out)), installHint)
	case version[1] != Version:
		return nil, fmt.Errorf("proving obligations needs Z3 %s, and %s is Z3 %s; %s", Version, resolved, version[1], installHint)
	}
	return &Solver{
		path:    resolved,
		pool:    pool{limit: maxProcesses},
		flights: map[string]*flight{},
		answers: map[string]answer{},
	}, nil
}

// process is one running Z3 that reads commands from its standard input.
type process struct {
	cmd    *exec.Cmd
	in     io.WriteCloser
	out    *bufio.Reader
	stderr *strings.Builder
	done   chan struct{}
	served int
	// speculative is set while the process solves a speculative problem,
	// and preempted once it has been ended to free it for another; see
	// acquire.
	speculative bool
	preempted   atomic.Bool
	ended       bool
}

func (s *Solver) spawn() (*process, error) {
	cmd := exec.Command(s.path, settings...)
	in, err := cmd.StdinPipe()
	if err != nil {
		return nil, err
	}
	out, err := cmd.StdoutPipe()
	if err != nil {
		return nil, err
	}
	stderr := &strings.Builder{}
	cmd.Stderr = &lockedWriter{w: stderr}
	if err := cmd.Start(); err != nil {
		return nil, err
	}
	p := &process{cmd: cmd, in: in, out: bufio.NewReaderSize(out, 1<<16), stderr: stderr, done: make(chan struct{})}
	go func() {
		_ = cmd.Wait()
		close(p.done)
	}()
	return p, nil
}

// identified checks a new process against the identity of the cache
// directory. What the process runs is read once it has answered, so that a
// program that starts another with exec has done so. On any failure the
// process is discarded, which frees its slot.
func (s *Solver) identified(p *process) error {
	if _, err := s.exchange(p, "", time.Now().Add(wallLimit), nil); err != nil {
		// exchange has discarded the process.
		return err
	}
	if err := s.disk.identify(p.cmd.Process.Pid, s.path); err != nil {
		s.discard(p)
		return &CacheError{err}
	}
	return nil
}

type lockedWriter struct {
	mu sync.Mutex
	w  io.Writer
}

func (l *lockedWriter) Write(b []byte) (int, error) {
	l.mu.Lock()
	defer l.mu.Unlock()
	return l.w.Write(b)
}

// pool is the processes of a solver: those idle, how many run, which
// serve speculative problems, and how many main askers wait for one.
//
// Every process is in one of these states, and only a holder of mu moves it
// from one to another:
//
//   - idle: in idle, and neither speculative, preempted, nor ended;
//   - held: taken from idle, or started, by one asker, which alone uses it
//     until it returns it (release) or ends it (discard);
//   - held for speculation: held by a speculative asker, with speculative
//     set; it is in speculating once it can answer, and only then can it be
//     preempted;
//   - preempted: taken out of speculating, with preempted set and the
//     process killed, in one critical section of acquire. Its holder may
//     still be reading an answer it gave before, which stands, but the
//     process is never idle again and never serves another asker: release
//     ends it;
//   - ended: discard has counted it out of live; it is in no list.
//
// So a question gets its answer from a process that only it was using, and
// only a speculative asker can be told that its process was ended for
// another (errPreempted). check verifies what can be seen of this after
// every transition.
type pool struct {
	mu          sync.Mutex
	cond        *sync.Cond
	limit       int
	idle        []*process
	live        int
	speculating []*process
	specHeld    int
	mainWaiting int
	// busy is when an asker that is not speculative last found every
	// process busy.
	busy time.Time
}

// check verifies the states of the pool, with its lock held: no idle
// process is speculative, preempted, or ended; every process in
// speculating is speculative and neither preempted nor ended; no process is
// in both lists; and the counts agree with the lists. A violation is an
// internal error, which check records and never panics with, since its
// caller holds the lock: every later question fails with it (see broken),
// and every waiter wakes to find it.
func (s *Solver) check() {
	pl := &s.pool
	fail := func(format string, args ...any) {
		s.broken.CompareAndSwap(nil, &InternalError{fmt.Errorf("the pool of Z3 processes is inconsistent: "+format, args...)})
		if pl.cond != nil {
			pl.cond.Broadcast()
		}
	}
	for _, p := range pl.idle {
		switch {
		case p.speculative || p.preempted.Load() || p.ended:
			fail("an idle process is speculative (%v), preempted (%v), or ended (%v)", p.speculative, p.preempted.Load(), p.ended)
			return
		case slices.Contains(pl.speculating, p):
			fail("an idle process serves speculation")
			return
		}
	}
	for _, p := range pl.speculating {
		if !p.speculative || p.preempted.Load() || p.ended {
			fail("a process that serves speculation is not speculative (%v), or is preempted (%v) or ended (%v)", !p.speculative, p.preempted.Load(), p.ended)
			return
		}
	}
	switch {
	case len(pl.speculating) > pl.specHeld || pl.specHeld < 0 || pl.specHeld > max(pl.limit-1, 0):
		fail("%d processes serve speculation in %d places, of at most %d", len(pl.speculating), pl.specHeld, max(pl.limit-1, 0))
	case len(pl.idle)+len(pl.speculating) > pl.live || pl.live > pl.limit:
		fail("%d idle and %d speculating processes, of %d running and at most %d", len(pl.idle), len(pl.speculating), pl.live, pl.limit)
	case pl.mainWaiting < 0:
		fail("%d askers wait", pl.mainWaiting)
	}
}

// paused, when set, is called with the name of the point and the process
// at hand, if any, wherever the pool or the flights have dropped a lock, or
// are about to take one, and then act on what was read before, and where an
// asker begins to wait: "sleeps" for the quiet window, "waits" for a
// process, with the pool's lock held, and "follows" for another asker's
// problem. Only the tests set it: to hold an asker at a point until another has done
// something, which forces an order of events, and to sleep at random
// (jitter), which brings about orders that are otherwise rare. A new such
// place gets a call.
var paused func(point string, p *process)

func pause(point string, p *process) {
	if paused != nil {
		paused(point, p)
	}
}

// quiet is how long after an asker found every process busy no
// speculative problem starts: while other askers keep every process busy, a
// speculative problem would mostly be ended for one of theirs, which wastes
// its work and the start of a process.
var quiet = 100 * time.Millisecond

// acquire returns an idle process, or starts one if fewer than the limit
// run, or waits for one. Speculative problems, which only fill the cache
// for a verification that will ask them later, never delay another: a
// speculative asker takes a process only while no other asker waits and at
// most limit-1 processes serve speculation, and an asker that is not
// speculative and finds every process busy ends one that serves
// speculation, whose asker then gets no answer (errPreempted). Once the
// pool is found inconsistent, it returns that error to every asker.
func (s *Solver) acquire(who asker) (*process, error) {
	speculative := who.speculative
	pl := &s.pool
	pl.mu.Lock()
	if pl.cond == nil {
		pl.cond = sync.NewCond(&pl.mu)
	}
	if !speculative {
		pl.mainWaiting++
	}
	// pending is the process this asker ended to free a place, until its
	// place is free.
	var pending *process
	for {
		// The state found is checked before it is acted on, and again
		// after each change.
		s.check()
		if e := s.broken.Load(); e != nil {
			if !speculative {
				pl.mainWaiting--
			}
			pl.mu.Unlock()
			return nil, e
		}
		if who.stopped() {
			pl.mu.Unlock()
			return nil, errPreempted
		}
		allowed := !speculative || (pl.mainWaiting == 0 && pl.specHeld < pl.limit-1)
		if pending != nil && pending.ended {
			pending = nil
		}
		if !speculative && len(pl.idle) == 0 && pl.live == pl.limit {
			pl.busy = time.Now()
		}
		if wait := quiet - time.Since(pl.busy); allowed && speculative && wait > 0 {
			pl.mu.Unlock()
			pause("sleeps", nil)
			select {
			case <-time.After(wait):
			case <-who.stop:
			}
			pause("quiet", nil)
			pl.mu.Lock()
			continue
		}
		switch {
		case allowed && len(pl.idle) > 0:
			p := pl.idle[len(pl.idle)-1]
			pl.idle = pl.idle[:len(pl.idle)-1]
			s.taken(p, speculative)
			s.check()
			pl.mu.Unlock()
			return p, nil
		case allowed && pl.live < pl.limit:
			pl.live++
			if speculative {
				pl.specHeld++
			} else {
				pl.mainWaiting--
			}
			s.check()
			pl.mu.Unlock()
			pause("spawn", nil)
			p, err := s.spawn()
			if err == nil && s.disk != nil {
				// identified discards the process on any failure, which
				// frees its place.
				err = s.identified(p)
			} else if err != nil {
				// A process that never started frees its place here.
				pause("unstarted", nil)
				pl.mu.Lock()
				pl.live--
				if speculative {
					pl.specHeld--
				}
				s.check()
				pl.cond.Broadcast()
				pl.mu.Unlock()
				return nil, err
			}
			pause("spawned", p)
			pl.mu.Lock()
			if err != nil {
				if speculative {
					pl.specHeld--
				}
				s.check()
				pl.cond.Broadcast()
				pl.mu.Unlock()
				return nil, err
			}
			if speculative {
				// It can be preempted from now on, which an asker that
				// found every process busy may be waiting to do.
				p.speculative = true
				pl.speculating = append(pl.speculating, p)
				pl.cond.Broadcast()
			}
			s.check()
			pl.mu.Unlock()
			return p, nil
		case !speculative && pending == nil && len(pl.speculating) > 0:
			// The youngest speculative problem has done the least work.
			pending = pl.speculating[len(pl.speculating)-1]
			pl.speculating = pl.speculating[:len(pl.speculating)-1]
			pending.preempted.Store(true)
			_ = pending.cmd.Process.Kill()
			s.check()
		}
		// Called with the lock held, which anything that wakes the asker
		// takes, so the asker waits before it can be woken.
		pause("waits", nil)
		pl.cond.Wait()
	}
}

// taken records that p, taken from the idle processes with the pool's lock
// held, now serves an asker.
func (s *Solver) taken(p *process, speculative bool) {
	pl := &s.pool
	if speculative {
		p.speculative = true
		pl.speculating = append(pl.speculating, p)
		pl.specHeld++
	} else {
		pl.mainWaiting--
	}
}

// release returns a process that answered to the idle ones. A process
// that was ended to free its place, even after it had answered, is
// discarded instead: whether it was is read under the lock that acquire
// ends it under, so the process is either among the idle ones before any
// asker can end it, or ended before it would be.
func (s *Solver) release(p *process) {
	pause("release", p)
	pl := &s.pool
	pl.mu.Lock()
	if p.preempted.Load() {
		pl.mu.Unlock()
		s.discard(p)
		return
	}
	defer pl.mu.Unlock()
	s.unspeculate(p)
	pl.idle = append(pl.idle, p)
	s.check()
	if pl.cond != nil {
		pl.cond.Broadcast()
	}
}

// preempt ends a process that serves speculation, as acquire does to free
// its place: one that is no longer in speculating has been preempted
// already, or is no longer held for speculation, and is left alone.
func (s *Solver) preempt(p *process) {
	pl := &s.pool
	pl.mu.Lock()
	defer pl.mu.Unlock()
	if i := slices.Index(pl.speculating, p); i >= 0 {
		pl.speculating = slices.Delete(pl.speculating, i, i+1)
		p.preempted.Store(true)
		_ = p.cmd.Process.Kill()
		s.check()
	}
}

// Wake wakes every asker waiting for a process, so that a speculative one
// whose answer is no longer wanted sees so; see Options.Stop.
func (s *Solver) Wake() {
	pl := &s.pool
	pl.mu.Lock()
	defer pl.mu.Unlock()
	if pl.cond != nil {
		pl.cond.Broadcast()
	}
}

// WakeAll wakes every asker waiting for a process of any solver of the
// program; see Wake.
func WakeAll() {
	solversMu.Lock()
	var all []*Solver
	for _, found := range solvers {
		if found.s != nil {
			all = append(all, found.s)
		}
	}
	solversMu.Unlock()
	for _, s := range all {
		s.Wake()
	}
}

// unspeculate removes p from the processes that serve speculation, with
// the pool's lock held.
func (s *Solver) unspeculate(p *process) {
	pl := &s.pool
	if p.speculative {
		p.speculative = false
		pl.specHeld--
		if i := slices.Index(pl.speculating, p); i >= 0 {
			pl.speculating = slices.Delete(pl.speculating, i, i+1)
		}
	}
}

// discard ends a process that can no longer be trusted to answer the next
// problem, freeing its place.
func (s *Solver) discard(p *process) {
	_ = p.cmd.Process.Kill()
	<-p.done
	_ = p.in.Close()
	pause("discard", p)
	pl := &s.pool
	pl.mu.Lock()
	defer pl.mu.Unlock()
	s.unspeculate(p)
	p.ended = true
	pl.live--
	s.check()
	if pl.cond != nil {
		pl.cond.Broadcast()
	}
}

// answer is what Z3 said about one problem.
type answer struct {
	status string // sat, unsat, or unknown
	reason string // for unknown, why
	// values holds the values Z3 gave the constants asked for, when it
	// found a model; see parseValues.
	values map[string]string
	// effort is the resources Z3 counted for the problem, and took the
	// time it took once a process was free.
	effort int64
	took   time.Duration
	// stored is set for an answer read from the cache on disk, and for
	// one the process kept after reading it there.
	stored bool
}

// answer returns Z3's answer to a problem, from the cache when the same
// text with the same names asked was answered before, and reports which.
//
// After (reset), with the options fixed on the command line and the
// resource limit in the text, Z3 of one binary gives a problem the same
// answer, values, and resource count every time; the answer depends on the
// text alone. That is what makes a proof deterministic in the first place,
// since any process of the pool may serve any problem. So an answer
// read from the cache is the one Z3 would give again. What depends on the
// machine is never kept: a problem that ran past the wall limit, one that
// ran out of memory, and one whose process died or replied with anything
// else, which are errors here; and an unknown for want of memory. An
// unknown because Z3 was canceled is kept: Z3 is given no time limit of its
// own, so it cancels a problem only at the resource limit, which exhausted
// takes it for, with the same count on every run.
//
// With a cache directory, an answer not kept in the process is looked for
// there before Z3 is asked, and every answer kept in the process is also
// kept there; see disk.go. An answer read from there is marked stored, and
// so is the same answer when the process gives it again.
func (s *Solver) answer(script string, values []string, who asker) (answer, bool, error) {
	speculative := who.speculative
	key := script + "\x00" + strings.Join(values, " ")
	// A cache that a speculative asker found cannot be trusted cannot be
	// trusted by anyone: its error, which nobody reads where it was
	// raised, fails every later question of another asker. A defect of
	// the solver itself fails every later question of every asker.
	if e := s.broken.Load(); e != nil {
		panic(e)
	}
	if speculative {
		defer func() {
			if r := recover(); r != nil {
				if e, ok := r.(error); ok {
					s.Distrust(e)
				}
				panic(r)
			}
		}()
	} else if e := s.untrusted.Load(); e != nil {
		panic(e)
	}
	for {
		s.mu.Lock()
		a, ok := s.answers[key]
		s.mu.Unlock()
		if ok {
			a.took = 0
			return a, true, nil
		}
		if s.disk != nil {
			if r, ok := s.disk.read(key); ok {
				a, err := interpret(r)
				if err == nil && (len(values) > 0 && a.status != "unsat") != r.asked {
					err = errors.New("its values do not go with its answer")
				}
				if err != nil {
					cacheFault("the answer cache entry %s is damaged: %v; to empty the cache, remove %s", s.disk.entryPath(key), err, s.disk.root)
				}
				// A sample of the answers read, drawn anew for each run, is
				// solved again to watch the premise.
				s.disk.mu.Lock()
				watched := s.disk.rng.IntN(watchRate) == 0
				s.disk.mu.Unlock()
				if watched {
					s.watch(key, script, values, r, who)
				}
				a.stored = true
				s.remember(key, a)
				return a, true, nil
			}
		}
		// A problem being solved is not solved again: the asker waits for
		// its answer. A speculative asker takes a process before it
		// says it solves the problem, so that no other asker waits while
		// it waits for one; see acquire.
		pause("missed", nil)
		var p *process
		if speculative {
			var err error
			if p, err = s.acquire(who); err != nil {
				return answer{}, false, s.startError(err)
			}
		}
		s.flightsMu.Lock()
		if f := s.flights[key]; f != nil {
			s.flightsMu.Unlock()
			if p != nil {
				s.release(p)
			}
			pause("follows", nil)
			select {
			case <-f.done:
			case <-who.stop:
				// A speculative asker whose answer is no longer wanted does
				// not wait for another's.
				return answer{}, false, errPreempted
			}
			pause("waited", nil)
			switch {
			case f.kept:
				a := f.a
				a.took = 0
				return a, true, nil
			case f.speculative, f.abandoned:
				// A speculative asker that got no answer to keep, as when
				// its process was ended for another asker, answers for
				// nobody else, and neither does an asker that panicked.
				continue
			}
			return f.a, false, f.err
		}
		s.mu.Lock()
		_, known := s.answers[key]
		s.mu.Unlock()
		if known {
			s.flightsMu.Unlock()
			if p != nil {
				s.release(p)
			}
			continue
		}
		f := &flight{done: make(chan struct{}), speculative: speculative}
		s.flights[key] = f
		s.flightsMu.Unlock()
		a, err := s.fly(f, key, p, script, values, who)
		return a, false, err
	}
}

// fly solves the problem of a flight, keeps its answer, and ends the
// flight on every path, a panic included: an asker that panicked, as on a
// cache that cannot be written, has no answer for its waiters, who then ask
// again.
func (s *Solver) fly(f *flight, key string, p *process, script string, values []string, who asker) (a answer, err error) {
	f.abandoned = true
	defer func() {
		s.flightsMu.Lock()
		delete(s.flights, key)
		s.flightsMu.Unlock()
		close(f.done)
	}()
	var r reply
	if p == nil {
		a, r, err = s.solve(script, values, who)
	} else {
		a, r, err = s.run(p, script, values, who)
	}
	pause("flown", p)
	if err == nil && !(a.status == "unknown" && machineBound(a.reason)) {
		if s.disk != nil {
			s.disk.write(key, r)
		}
		s.remember(key, a)
		f.kept = true
	}
	f.a, f.err, f.abandoned = a, err, false
	return a, err
}

// flight is a problem being solved, which other askers of it wait for.
// kept is set when its answer is kept; speculative when its asker is; and
// abandoned when its asker panicked.
type flight struct {
	done        chan struct{}
	a           answer
	err         error
	kept        bool
	speculative bool
	abandoned   bool
}

// solve takes a process and solves a problem with it.
func (s *Solver) solve(script string, values []string, who asker) (answer, reply, error) {
	p, err := s.acquire(who)
	if err != nil {
		return answer{}, reply{}, s.startError(err)
	}
	return s.run(p, script, values, who)
}

// asker is who asks a question: whether it is speculative, and, for a
// speculative one, a channel closed once its answer is no longer wanted;
// see Options.Stop.
type asker struct {
	speculative bool
	stop        <-chan struct{}
}

// stopped reports whether the asker's answer is no longer wanted.
func (who asker) stopped() bool {
	select {
	case <-who.stop:
		return true
	default:
		return false
	}
}

// startError says that a process could not be started; a CacheError, an
// InternalError, and errPreempted say themselves why.
func (s *Solver) startError(err error) error {
	if errors.As(err, new(*CacheError)) || errors.As(err, new(*InternalError)) || err == errPreempted {
		return err
	}
	return fmt.Errorf("starting %s: %v", s.path, err)
}

// watch solves again a problem whose answer was read from disk and stops
// the run if Z3 now answers otherwise. An answer that depends on the
// machine, past the wall limit or for want of memory, says nothing about
// the premise, and leaves the answer read from disk to be used. So does a
// speculative asker's process ended for another asker, the one asker that
// can be told so. Any other failure leaves the entry unconfirmed, as when
// Z3 crashes on a text it once answered, and is a CacheError, which a
// speculative asker records too (see answer): whether the verification or
// a speculative asker reads an entry first is a matter of timing, so the
// outcome must not depend on which.
func (s *Solver) watch(key, script string, values []string, stored reply, who asker) {
	live, r, err := s.solve(script, values, who)
	switch {
	case errors.As(err, new(*CacheError)), errors.As(err, new(*InternalError)):
		panic(err)
	case err == errTimeout, err == errMemory, err == errPreempted && who.speculative:
		return
	case err != nil:
		cacheFault("solving again the problem of the answer cache entry %s failed, so the entry cannot be confirmed: %v (the problem is saved in %s); to empty the cache, remove %s", s.disk.entryPath(key), err, dump(script), s.disk.root)
	case live.status == "unknown" && machineBound(live.reason):
		return
	}
	if !r.equal(stored) {
		cacheFault("Z3 answers a problem otherwise than the answer cache entry %s says, %q against %q, so the answers kept there cannot be trusted; to empty the cache, remove %s", s.disk.entryPath(key), r.check, stored.check, s.disk.root)
	}
}

// remember keeps an answer in the process, forgetting the oldest beyond
// cacheBytes.
func (s *Solver) remember(key string, a answer) {
	s.mu.Lock()
	defer s.mu.Unlock()
	if _, ok := s.answers[key]; !ok && len(key) <= cacheBytes {
		s.answers[key] = a
		s.queue = append(s.queue, key)
		s.held += len(key)
		for s.held > cacheBytes {
			s.held -= len(s.queue[0])
			delete(s.answers, s.queue[0])
			s.queue = s.queue[1:]
		}
	}
}

// preemptedOr returns, for a process that was ended to free its place for
// another asker, errPreempted to a speculative asker, and an internal error
// to any other, which no process of the pool can serve that way; it
// returns err otherwise. A process is preempted before it is killed, so a
// failure that the kill caused always reads as preempted; a speculative
// process that failed on its own as it was preempted reads so too, which
// loses nothing, since its answer serves only the cache.
func (s *Solver) preemptedOr(p *process, err error, who asker) error {
	switch {
	case !p.preempted.Load():
		return err
	case who.speculative:
		return errPreempted
	}
	e := &InternalError{errors.New("a question that is not speculative was served by a Z3 process ended for another asker")}
	s.Distrust(e)
	return e
}

// Distrust records an error that a speculative asker met and nobody reads
// where it was raised: a CacheError then fails every later question of an
// asker that is not speculative, and an InternalError every later
// question, and both are returned by Untrusted. Other errors are left
// alone.
func (s *Solver) Distrust(err error) {
	var cache *CacheError
	var internal *InternalError
	switch {
	case errors.As(err, &internal):
		s.broken.CompareAndSwap(nil, internal)
		s.pool.mu.Lock()
		if s.pool.cond != nil {
			s.pool.cond.Broadcast()
		}
		s.pool.mu.Unlock()
	case errors.As(err, &cache):
		s.untrusted.CompareAndSwap(nil, cache)
	}
}

// Untrusted returns the first InternalError met by any asker, or else the
// first CacheError met by a speculative asker, or nil. The verification of
// a package calls it once the package's speculative verifiers have
// stopped, so that what they found fails that package.
func (s *Solver) Untrusted() error {
	if e := s.broken.Load(); e != nil {
		return e
	}
	if e := s.untrusted.Load(); e != nil {
		return e
	}
	return nil
}

// errPreempted is returned to a speculative asker whose process was ended
// to free its place for another asker; see acquire. It is no answer, and
// only a speculative asker, whose answers serve nobody but the cache, can
// get it.
var errPreempted = errors.New("preempted")

// errTimeout is returned when a problem runs past the wall limit, and
// errMemory when Z3 stopped because it reached its memory limit, which it
// does by printing an error and exiting.
var (
	errTimeout = errors.New("timed out")
	errMemory  = errors.New("out of memory")
)

// What a process is sent around a problem: before it, after it, and, to
// ask for values, with the names in place of the verb. They are part of the
// identity of a cache directory, since a reply depends on them.
const (
	resetCommand  = "(reset)\n"
	infoCommands  = "(get-info :reason-unknown)\n(get-info :rlimit)\n"
	valuesCommand = "(get-value (%s))\n"
)

// run sends one problem, which must end in a check-sat-using, and reads the
// answer. When the answer is not unsat and values names constants, it then
// asks for their values in the model. Every reply other than the expected
// ones is an error: a problem that Z3 could not read was not proved,
// whatever else it printed.
func (s *Solver) run(p *process, script string, values []string, who asker) (answer, reply, error) {
	pause("run", p)
	began := time.Now()
	deadline := began.Add(wallLimit)
	lines, err := s.exchange(p, resetCommand+script+infoCommands, deadline, who.stop)
	pause("exchanged", p)
	if err != nil {
		return answer{}, reply{}, s.preemptedOr(p, err, who)
	}
	r := reply{check: lines}
	a, err := parseAnswer(lines)
	if err == nil && len(values) > 0 && a.status != "unsat" {
		lines, err := s.exchange(p, fmt.Sprintf(valuesCommand, strings.Join(values, " ")), deadline, who.stop)
		if err != nil {
			return answer{}, reply{}, s.preemptedOr(p, err, who)
		}
		r.values, r.asked = lines, true
		if noModel(lines) {
			// The error names the line it is on, which counts what the
			// process read before; kept on disk, the reply would depend on
			// which process gave it.
			r.values = []string{noModelReply}
		}
		a, err = interpret(r)
	}
	if err != nil {
		s.discard(p)
		return answer{}, reply{}, fmt.Errorf("%s: %v", s.path, err)
	}
	// A process that ran out of resources may hold on to memory; a fresh
	// one serves the next problem.
	a.took = time.Since(began)
	if a.status == "unknown" && (exhausted(a.reason) || machineBound(a.reason)) {
		s.discard(p)
	} else {
		s.release(p)
	}
	return a, r, nil
}

// noModelReply is how a reply to a get-value that Z3 had no model for is
// kept.
const noModelReply = `(error "model is not available")`

// noModel reports whether the lines are Z3's error for a get-value without
// a model.
func noModel(lines []string) bool {
	return len(lines) == 1 && strings.HasPrefix(lines[0], "(error") && strings.Contains(lines[0], "model is not available")
}

// interpret reads a reply, live or kept on disk: the answer, and the values
// when they were asked. Z3 may have no model to give after unknown, which
// it says with an error; that only means there are no values. Any other
// reply that is not an answer is an error.
func interpret(r reply) (answer, error) {
	a, err := parseAnswer(r.check)
	if err != nil || !r.asked {
		return a, err
	}
	if a.status == "unsat" {
		return answer{}, errors.New("values were asked after unsat")
	}
	if noModel(r.values) {
		return a, nil
	}
	a.values, err = parseValues(strings.Join(r.values, "\n"))
	return a, err
}

// exchange sends commands to a process and reads what it prints up to a
// marker that follows them. The reply is read while the commands are
// written, since Z3 answers each command as it reads it and would stop
// reading once its output is not taken. On any failure the process is
// discarded. When stop is closed first, the process, which serves a
// speculative asker, is preempted, so that the asker gets no answer.
func (s *Solver) exchange(p *process, commands string, deadline time.Time, stop <-chan struct{}) ([]string, error) {
	p.served++
	end := "vego-end-" + strconv.Itoa(p.served)
	type reply struct {
		lines []string
		err   error
	}
	replies := make(chan reply, 1)
	go func() {
		var lines []string
		for {
			line, err := p.out.ReadString('\n')
			if err != nil {
				replies <- reply{lines, err}
				return
			}
			line = strings.TrimRight(line, "\r\n")
			if line == end {
				replies <- reply{lines, nil}
				return
			}
			lines = append(lines, line)
		}
	}()
	written := make(chan error, 1)
	go func() {
		_, err := io.WriteString(p.in, commands+"(echo \""+end+"\")\n")
		written <- err
	}()
	timer := time.NewTimer(time.Until(deadline))
	defer timer.Stop()
	var r reply
	select {
	case r = <-replies:
	case <-stop:
		s.preempt(p)
		r = <-replies
	case <-timer.C:
		s.discard(p)
		<-replies
		<-written
		return nil, errTimeout
	}
	if err := <-written; err != nil && r.err == nil {
		r.err = err
	}
	if r.err != nil {
		// The process has ended, so what it wrote can be read safely.
		s.discard(p)
		if strings.Contains(strings.Join(r.lines, "\n")+p.stderr.String(), `(error "out of memory")`) {
			return nil, errMemory
		}
		return nil, fmt.Errorf("%s stopped: %v; it printed %q and on standard error %q", s.path, r.err, strings.Join(r.lines, "\n"), p.stderr.String())
	}
	return r.lines, nil
}

var reasonPattern = regexp.MustCompile(`^\(:reason-unknown "(.*)"\)$`)

// parseAnswer reads the reply to a problem: the result of the check-sat,
// the reason for an unknown result, and the resources Z3 counted, and
// nothing else.
func parseAnswer(lines []string) (answer, error) {
	if len(lines) == 0 {
		return answer{}, fmt.Errorf("no reply")
	}
	count := rlimitPattern.FindStringSubmatch(lines[len(lines)-1])
	if count == nil {
		return answer{}, fmt.Errorf("unexpected reply %q, which does not end in the resources counted", strings.Join(lines, "\n"))
	}
	effort, err := strconv.ParseInt(count[1], 10, 64)
	if err != nil {
		return answer{}, fmt.Errorf("unexpected count of resources %q", count[1])
	}
	a, err := parseStatus(lines[:len(lines)-1])
	a.effort = effort
	return a, err
}

var rlimitPattern = regexp.MustCompile(`^\(:rlimit (\d+)\)$`)

// parseStatus reads the result of the check-sat and the reason for an
// unknown result.
func parseStatus(lines []string) (answer, error) {
	// A tactic of the chain that runs out of the resource limit stops the
	// check-sat with an error in place of its answer. That is the limit,
	// which leaves the problem open, as an unknown for it does.
	if len(lines) == 2 && lines[0] == `(error "tactic failed: max. resource limit exceeded")` &&
		lines[1] == `(:reason-unknown "max. resource limit exceeded")` {
		return answer{status: "unknown", reason: "max. resource limit exceeded"}, nil
	}
	if len(lines) != 2 {
		return answer{}, fmt.Errorf("unexpected reply %q", strings.Join(lines, "\n"))
	}
	status := lines[0]
	if status != "sat" && status != "unsat" && status != "unknown" {
		return answer{}, fmt.Errorf("unexpected reply %q", strings.Join(lines, "\n"))
	}
	reason := reasonPattern.FindStringSubmatch(lines[1])
	if reason == nil {
		return answer{}, fmt.Errorf("unexpected reply %q", strings.Join(lines, "\n"))
	}
	return answer{status: status, reason: reason[1]}, nil
}

// dump writes a problem to a temporary file for a report of a fault, and
// returns its name.
func dump(script string) string {
	f, err := os.CreateTemp("", "vego-problem-*.smt2")
	if err != nil {
		return "(the problem could not be saved: " + err.Error() + ")"
	}
	defer f.Close()
	_, _ = f.WriteString(script)
	return f.Name()
}

// parseValues reads the reply to a get-value: a list of pairs of a constant
// and its value, as text. Only integers and booleans are kept; another
// value, such as an element of an uninterpreted sort, is left out.
func parseValues(text string) (map[string]string, error) {
	list, rest, err := readExpr(text)
	if err != nil || strings.TrimSpace(rest) != "" {
		return nil, fmt.Errorf("unexpected values %q", text)
	}
	pairs, ok := list.([]any)
	if !ok {
		return nil, fmt.Errorf("unexpected values %q", text)
	}
	values := map[string]string{}
	for _, pair := range pairs {
		kv, ok := pair.([]any)
		if !ok || len(kv) != 2 {
			return nil, fmt.Errorf("unexpected values %q", text)
		}
		name, ok := kv[0].(string)
		if !ok {
			return nil, fmt.Errorf("unexpected values %q", text)
		}
		if value, ok := plainValue(kv[1]); ok {
			values[name] = value
		}
	}
	return values, nil
}

// plainValue returns an integer, written as a decimal with an optional sign,
// or a boolean.
func plainValue(v any) (string, bool) {
	switch v := v.(type) {
	case string:
		if v == "true" || v == "false" {
			return v, true
		}
		if isDigits(v) {
			return v, true
		}
	case []any:
		if len(v) == 2 && v[0] == "-" {
			if digits, ok := v[1].(string); ok && isDigits(digits) {
				return "-" + digits, true
			}
		}
	}
	return "", false
}

func isDigits(s string) bool {
	return s != "" && strings.Trim(s, "0123456789") == ""
}

// readExpr reads one s-expression: an atom as a string, or a list as a
// slice. Quoted strings and symbols are not expected in values and are
// rejected.
func readExpr(text string) (any, string, error) {
	text = strings.TrimLeft(text, " \t\r\n")
	if text == "" {
		return nil, "", errors.New("end of input")
	}
	switch text[0] {
	case '(':
		var list []any
		rest := text[1:]
		for {
			rest = strings.TrimLeft(rest, " \t\r\n")
			if rest == "" {
				return nil, "", errors.New("unclosed list")
			}
			if rest[0] == ')' {
				return list, rest[1:], nil
			}
			item, after, err := readExpr(rest)
			if err != nil {
				return nil, "", err
			}
			list = append(list, item)
			rest = after
		}
	case ')', '"', '|':
		return nil, "", fmt.Errorf("unexpected %q", text[0])
	}
	end := strings.IndexAny(text, " \t\r\n()")
	if end < 0 {
		end = len(text)
	}
	return text[:end], text[end:], nil
}
