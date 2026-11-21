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
	"strconv"
	"strings"
	"sync"
	"time"
)

// Version is the version of Z3 that vego is built for. Another version may
// prove different obligations, or the same ones with different effort, so
// it is refused.
const Version = "5.4.1"

// installHint says how to get the pinned version.
const installHint = "install Z3 " + Version + " from https://github.com/Z3Prover/z3/releases/tag/z3-" + Version +
	" and put its bin/z3 on PATH, or name it with -vego.z3"

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
	path  string
	idle  chan *process
	slots chan struct{}
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
	p, err := s.acquire()
	if err != nil {
		return err
	}
	s.idle <- p
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
		idle:    make(chan *process, maxProcesses),
		slots:   make(chan struct{}, maxProcesses),
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
	if _, err := s.exchange(p, "", time.Now().Add(wallLimit)); err != nil {
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

// acquire returns an idle process, or starts one if fewer than the limit
// are running, or waits for one.
func (s *Solver) acquire() (*process, error) {
	select {
	case p := <-s.idle:
		return p, nil
	default:
	}
	select {
	case p := <-s.idle:
		return p, nil
	case s.slots <- struct{}{}:
		p, err := s.spawn()
		if err != nil {
			<-s.slots
			return nil, err
		}
		if s.disk != nil {
			if err := s.identified(p); err != nil {
				return nil, err
			}
		}
		return p, nil
	}
}

// discard ends a process that can no longer be trusted to answer the next
// problem, freeing its slot.
func (s *Solver) discard(p *process) {
	_ = p.cmd.Process.Kill()
	<-p.done
	_ = p.in.Close()
	<-s.slots
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
func (s *Solver) answer(script string, values []string) (answer, bool, error) {
	key := script + "\x00" + strings.Join(values, " ")
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
				cacheFault(s.disk.root, "the answer cache entry %s is damaged: %v", s.disk.entryPath(key), err)
			}
			// A sample of the answers read, drawn anew for each run, is
			// solved again to watch the premise.
			s.disk.mu.Lock()
			watched := s.disk.rng.IntN(watchRate) == 0
			s.disk.mu.Unlock()
			if watched {
				s.watch(key, script, values, r)
			}
			a.stored = true
			s.remember(key, a)
			return a, true, nil
		}
	}
	a, r, err := s.run(script, values)
	if err != nil || (a.status == "unknown" && machineBound(a.reason)) {
		return a, false, err
	}
	if s.disk != nil {
		s.disk.write(key, r)
	}
	s.remember(key, a)
	return a, false, nil
}

// watch solves again a problem whose answer was read from disk and stops
// the run if Z3 now answers otherwise. An answer that depends on the
// machine says nothing about the premise.
func (s *Solver) watch(key, script string, values []string, stored reply) {
	live, r, err := s.run(script, values)
	if errors.As(err, new(*CacheError)) {
		panic(err)
	}
	if err != nil || (live.status == "unknown" && machineBound(live.reason)) {
		return
	}
	if !r.equal(stored) {
		cacheFault(s.disk.root, "Z3 answers a problem otherwise than the answer cache entry %s says, %q against %q, so the answers kept there cannot be trusted", s.disk.entryPath(key), r.check, stored.check)
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
func (s *Solver) run(script string, values []string) (answer, reply, error) {
	p, err := s.acquire()
	if err != nil {
		var cacheErr *CacheError
		if errors.As(err, &cacheErr) {
			return answer{}, reply{}, err
		}
		return answer{}, reply{}, fmt.Errorf("starting %s: %v", s.path, err)
	}
	began := time.Now()
	deadline := began.Add(wallLimit)
	lines, err := s.exchange(p, resetCommand+script+infoCommands, deadline)
	if err != nil {
		return answer{}, reply{}, err
	}
	r := reply{check: lines}
	a, err := parseAnswer(lines)
	if err == nil && len(values) > 0 && a.status != "unsat" {
		lines, err := s.exchange(p, fmt.Sprintf(valuesCommand, strings.Join(values, " ")), deadline)
		if err != nil {
			return answer{}, reply{}, err
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
		s.idle <- p
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
// discarded.
func (s *Solver) exchange(p *process, commands string, deadline time.Time) ([]string, error) {
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
