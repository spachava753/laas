package solver

import (
	"bytes"
	"errors"
	"io/fs"
	"math/rand/v2"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/spachava753/laas/vego/internal/logic"
)

// cacheDir returns a new directory for an answer cache. The temporary
// directory may be inside a repository, which a cache is refused in, so
// the search for one stops at the test's own directory.
func cacheDir(t *testing.T) string {
	t.Helper()
	root := t.TempDir()
	// Every temporary directory of a test is in one directory of its own.
	saved := searchedUpTo
	searchedUpTo = filepath.Dir(root)
	t.Cleanup(func() { searchedUpTo = saved })
	return filepath.Join(root, "cache")
}

// z3Binary returns the absolute path of the z3 on PATH, with links
// resolved.
func z3Binary(t *testing.T) string {
	t.Helper()
	path, err := exec.LookPath("z3")
	if err != nil {
		t.Fatal("no z3 on PATH")
	}
	resolved, err := filepath.EvalSymlinks(path)
	if err != nil {
		t.Fatal(err)
	}
	return resolved
}

// cached returns a solver of its own, not shared with the rest of the
// test binary, that keeps answers in dir; its processes end with the test.
func cached(t *testing.T, path, dir string) *Solver {
	t.Helper()
	s, err := opened(t, path, dir)
	if err != nil {
		t.Fatal(err)
	}
	return s
}

func opened(t *testing.T, path, dir string) (*Solver, error) {
	t.Helper()
	s, err := start(path)
	if err != nil {
		return nil, err
	}
	t.Cleanup(func() { endIdle(s) })
	return s, s.openCache(dir)
}

// endIdle ends the idle processes of a solver, so that the next problem
// starts a new one.
func endIdle(s *Solver) {
	for {
		s.pool.mu.Lock()
		if len(s.pool.idle) == 0 {
			s.pool.mu.Unlock()
			return
		}
		p := s.pool.idle[len(s.pool.idle)-1]
		s.pool.idle = s.pool.idle[:len(s.pool.idle)-1]
		s.pool.mu.Unlock()
		s.discard(p)
	}
}

// cacheFailure runs f and returns the message of the CacheError it
// panicked with, or "" if it did not.
func cacheFailure(f func()) (message string) {
	defer func() {
		if r := recover(); r != nil {
			e, ok := r.(*CacheError)
			if !ok {
				panic(r)
			}
			message = e.Error()
		}
	}()
	f()
	return ""
}

// entries returns the entries kept under dir.
func entries(t *testing.T, dir string) []string {
	t.Helper()
	var found []string
	err := filepath.WalkDir(dir, func(path string, entry fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if !entry.IsDir() && entryName.MatchString(entry.Name()) {
			found = append(found, path)
		}
		return nil
	})
	if err != nil {
		t.Fatal(err)
	}
	return found
}

// TestDiskCache checks the answers kept between runs: a second solver on
// the same directory answers from it with what Z3 counted, and every way an
// entry, a process, or the directory can be wrong fails the package.
func TestDiskCache(t *testing.T) {
	z3 := z3Binary(t)
	x, y := logic.Const("x", logic.Int), logic.Const("y", logic.Int)
	goal := logic.Le(x, logic.Add(x, logic.IntLit(1)))
	var costs []Cost
	observed := Options{Observe: func(c Cost) { costs = append(costs, c) }}

	t.Run("a second run answers from the directory", func(t *testing.T) {
		dir := cacheDir(t)
		costs = nil
		if got := cached(t, z3, dir).Prove(nil, goal, observed); got != Proved {
			t.Fatalf("got %v", got)
		}
		if got := cached(t, z3, dir).Prove(nil, goal, observed); got != Proved {
			t.Fatalf("from the directory, got %v", got)
		}
		if len(costs) != 2 || costs[0].Stored || costs[0].Cached || !costs[1].Stored || !costs[1].Cached || costs[1].Effort != costs[0].Effort || costs[1].Time != 0 {
			t.Fatalf("costs %+v, want the second answer from the directory with the count of the first", costs)
		}
		if n := len(entries(t, dir)); n != 1 {
			t.Fatalf("%d entries, want 1", n)
		}
	})

	// The names whose values are asked are part of what a problem is: the
	// same text asked with and without them is two entries, and the values
	// come back from the directory.
	t.Run("values asked", func(t *testing.T) {
		dir := cacheDir(t)
		facts := []*logic.Term{logic.Lt(x, y), logic.Lt(logic.IntLit(5), x)}
		first := cached(t, z3, dir)
		first.Check(facts, Options{})
		result, values := first.Model(facts, Options{}, []*logic.Term{x})
		if result != Refuted || values["x"] == nil {
			t.Fatalf("got %v with %v", result, values)
		}
		if n := len(entries(t, dir)); n != 2 {
			t.Fatalf("%d entries, want 2: one without values and one with", n)
		}
		again, stored := cached(t, z3, dir).Model(facts, Options{}, []*logic.Term{x})
		if again != Refuted || stored["x"] == nil || stored["x"].String() != values["x"].String() {
			t.Fatalf("from the directory, got %v with %v, want %v with %v", again, stored, result, values)
		}
	})

	// Two processes that served different numbers of problems before, and
	// so end their replies with different markers, write the same entry.
	t.Run("the same entry from any process", func(t *testing.T) {
		one, other := cacheDir(t), cacheDir(t)
		busy := cached(t, z3, one)
		for i := range 3 {
			busy.Prove(nil, logic.Le(x, logic.Add(x, logic.IntLit(int64(10+i)))), Options{})
		}
		busy.Prove(nil, goal, Options{})
		cached(t, z3, other).Prove(nil, goal, Options{})
		path := cached(t, z3, other).disk.entryPath(Script([]*logic.Term{logic.Not(goal)}, Options{}) + "\x00")
		written, err := os.ReadFile(path)
		if err != nil {
			t.Fatal(err)
		}
		rel, _ := filepath.Rel(other, path)
		first, err := os.ReadFile(filepath.Join(one, rel))
		if err != nil || !bytes.Equal(first, written) {
			t.Fatalf("the entries differ: %q against %q (%v)", first, written, err)
		}
	})

	// Every kind of damage fails the package, and says how to empty the cache.
	damage := []struct {
		name  string
		edit  func(content []byte) []byte
		wants string
	}{
		{"a byte changed", func(c []byte) []byte { c[len(c)/2] ^= 1; return c }, "damaged"},
		{"cut short", func(c []byte) []byte { return c[:len(c)-10] }, "damaged"},
		{"empty", func(c []byte) []byte { return nil }, "damaged"},
		{"another format", func(c []byte) []byte {
			key, r, _ := decodeEntry(c)
			return bytes.Replace(encodeEntry(key, r), []byte(cacheFormat), []byte("vego z3 answers 0"), 1)
		}, "damaged"},
		// A whole entry with its hash right, for another problem: what a
		// collision of the names, or a writer that took the wrong text,
		// would leave.
		{"the answer to another problem", func(c []byte) []byte {
			_, r, _ := decodeEntry(c)
			return encodeEntry(Script([]*logic.Term{logic.Not(logic.Lt(y, y))}, Options{})+"\x00", r)
		}, "another problem"},
		// The same with a problem that this one is a prefix of, and one
		// that is a prefix of this one.
		{"the answer to a longer problem", func(c []byte) []byte {
			key, r, _ := decodeEntry(c)
			return encodeEntry(key+" ", r)
		}, "another problem"},
		{"the answer to a shorter problem", func(c []byte) []byte {
			key, r, _ := decodeEntry(c)
			return encodeEntry(key[:len(key)-1], r)
		}, "another problem"},
		{"values with an unsat", func(c []byte) []byte {
			key, r, _ := decodeEntry(c)
			r.asked, r.values = true, []string{"((c1 0))"}
			return encodeEntry(key, r)
		}, "damaged"},
		{"a reply that is no answer", func(c []byte) []byte {
			key, r, _ := decodeEntry(c)
			r.check[0] = "valid"
			return encodeEntry(key, r)
		}, "damaged"},
	}
	for _, test := range damage {
		t.Run("an entry "+test.name, func(t *testing.T) {
			dir := cacheDir(t)
			cached(t, z3, dir).Prove(nil, goal, Options{})
			found := entries(t, dir)
			content, err := os.ReadFile(found[0])
			if err != nil {
				t.Fatal(err)
			}
			if err := os.WriteFile(found[0], test.edit(content), 0o644); err != nil {
				t.Fatal(err)
			}
			message := cacheFailure(func() { cached(t, z3, dir).Prove(nil, goal, Options{}) })
			if !strings.Contains(message, test.wants) || !strings.Contains(message, "to empty the cache, remove "+filepath.Dir(filepath.Dir(filepath.Dir(found[0])))) {
				t.Fatalf("got %q, want a failure that says %q and how to empty the cache", message, test.wants)
			}
		})
	}

	// A missing entry is a miss, as when another run trimmed it between
	// the lookup and the read.
	t.Run("an entry removed", func(t *testing.T) {
		dir := cacheDir(t)
		cached(t, z3, dir).Prove(nil, goal, Options{})
		for _, path := range entries(t, dir) {
			os.Remove(path)
		}
		costs = nil
		if got := cached(t, z3, dir).Prove(nil, goal, observed); got != Proved || costs[0].Stored {
			t.Fatalf("got %v with %+v, want a proof from Z3", got, costs)
		}
	})

	// A reply that another run kept first must be the reply this run got.
	t.Run("two writers that disagree", func(t *testing.T) {
		dir := cacheDir(t)
		s := cached(t, z3, dir)
		key := Script([]*logic.Term{logic.Not(goal)}, Options{}) + "\x00"
		s.disk.write(key, reply{check: []string{"sat", `(:reason-unknown "")`, "(:rlimit 7)"}})
		if message := cacheFailure(func() { s.disk.write(key, reply{check: []string{"unsat", `(:reason-unknown "")`, "(:rlimit 7)"}}) }); !strings.Contains(message, "two ways") {
			t.Fatalf("got %q, want a failure that says Z3 answered in two ways", message)
		}
		if message := cacheFailure(func() { s.disk.write(key, reply{check: []string{"sat", `(:reason-unknown "")`, "(:rlimit 7)"}}) }); message != "" {
			t.Fatalf("the same reply written twice failed: %s", message)
		}
	})

	// A kept answer that Z3 no longer gives is caught when the sample of
	// the run solves it again.
	t.Run("a watched answer that Z3 does not give", func(t *testing.T) {
		dir := cacheDir(t)
		s := cached(t, z3, dir)
		key := Script([]*logic.Term{logic.Not(goal)}, Options{}) + "\x00"
		s.disk.write(key, reply{check: []string{"sat", `(:reason-unknown "")`, "(:rlimit 7)"}})
		saved := watchRate
		watchRate = 1
		defer func() { watchRate = saved }()
		if message := cacheFailure(func() { cached(t, z3, dir).Prove(nil, goal, Options{}) }); !strings.Contains(message, "otherwise") {
			t.Fatalf("got %q, want a failure that says Z3 answers otherwise", message)
		}
	})

	// The directory is named by what the processes run: another binary is
	// another directory, a script that runs Z3 is refused, and so is a
	// binary replaced while the solver runs.
	t.Run("the identity of the processes", func(t *testing.T) {
		dir := cacheDir(t)
		copied := filepath.Join(t.TempDir(), "z3")
		content, err := os.ReadFile(z3)
		if err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(copied, content, 0o755); err != nil {
			t.Fatal(err)
		}
		cached(t, z3, dir).Prove(nil, goal, Options{})
		s := cached(t, copied, dir)
		s.Prove(nil, goal, Options{})
		if s.disk.dir == "" || len(entries(t, dir)) != 1 {
			t.Fatalf("a copy of the same binary does not share the directory: %d entries", len(entries(t, dir)))
		}
		other := filepath.Join(t.TempDir(), "z3")
		if err := os.WriteFile(other, append(content, 0), 0o755); err != nil {
			t.Fatal(err)
		}
		changed := cached(t, other, dir)
		changed.Prove(nil, goal, Options{})
		if changed.disk.dir == s.disk.dir || len(entries(t, dir)) != 2 {
			t.Fatalf("a binary with other contents shares the directory %s", changed.disk.dir)
		}

		script := filepath.Join(t.TempDir(), "z3")
		if err := os.WriteFile(script, []byte("#!/bin/sh\nexec "+z3+" \"$@\"\n"), 0o755); err != nil {
			t.Fatal(err)
		}
		if _, err := opened(t, script, dir); err == nil || !strings.Contains(err.Error(), "needs the Z3 binary itself") {
			t.Fatalf("a script that runs Z3 was accepted: %v", err)
		}

		// The file at the path is replaced between two processes.
		replaced := cached(t, copied, dir)
		replaced.Prove(nil, goal, Options{})
		next := copied + ".new"
		if err := os.WriteFile(next, append(content, 1), 0o755); err != nil {
			t.Fatal(err)
		}
		if err := os.Rename(next, copied); err != nil {
			t.Fatal(err)
		}
		endIdle(replaced)
		if message := cacheFailure(func() { replaced.Prove(nil, logic.Lt(x, logic.Add(x, logic.IntLit(2))), Options{}) }); !strings.Contains(message, "other files") {
			t.Fatalf("got %q, want a failure that says a process runs other files", message)
		}
		// Every later question fails with it, one whose answer is kept in
		// the process too.
		if message := cacheFailure(func() { replaced.Prove(nil, goal, Options{}) }); !strings.Contains(message, "other files") {
			t.Fatalf("a later question whose answer is kept got %q, want the failure that says a process runs other files", message)
		}
	})

	// What depends on the machine, and a reply that is no answer, are not
	// kept; the reply to a get-value without a model is kept in one form,
	// whatever line Z3 says it is on.
	t.Run("an answer for want of memory", func(t *testing.T) {
		dir := cacheDir(t)
		s, err := fakeSolver(t, dir, "unknown\n(:reason-unknown \"memout\")\n(:rlimit 7)", "")
		if err != nil {
			t.Fatal(err)
		}
		if got := s.Prove(nil, goal, Options{}); got != OutOfMemory {
			t.Fatalf("got %v", got)
		}
		if n := len(entries(t, dir)); n != 0 {
			t.Fatalf("%d entries were written for an answer that depends on the machine", n)
		}
	})
	t.Run("a reply that is no answer", func(t *testing.T) {
		dir := cacheDir(t)
		s, err := fakeSolver(t, dir, "valid\n(:reason-unknown \"\")\n(:rlimit 7)", "")
		if err != nil {
			t.Fatal(err)
		}
		func() {
			defer func() {
				if _, ok := recover().(*Fault); !ok {
					t.Fatal("a reply that is no answer is not a fault")
				}
			}()
			s.Prove(nil, goal, Options{})
		}()
		if n := len(entries(t, dir)); n != 0 {
			t.Fatalf("%d entries were written for a fault", n)
		}
	})
	t.Run("a get-value without a model", func(t *testing.T) {
		var written [2][]byte
		facts := []*logic.Term{logic.Lt(x, y)}
		for i := range 2 {
			dir := cacheDir(t)
			s, err := fakeSolver(t, dir, "unknown\n(:reason-unknown \"canceled\")\n(:rlimit 7)", `(error "line {line} column 21: model is not available")`)
			if err != nil {
				t.Fatal(err)
			}
			// The second process has read other lines before.
			if i == 1 {
				s.Prove(nil, goal, Options{})
			}
			if result, values := s.Model(facts, Options{}, []*logic.Term{x}); result != Exhausted || values != nil {
				t.Fatalf("got %v with %v", result, values)
			}
			path := s.disk.entryPath(Script(facts, Options{}) + "\x00c1")
			content, err := os.ReadFile(path)
			if err != nil {
				t.Fatal(err)
			}
			written[i] = content
		}
		if !bytes.Equal(written[0], written[1]) || !bytes.Contains(written[0], []byte(noModelReply+"\n")) {
			t.Fatalf("the entries differ, or do not hold the fixed form:\n%s\n%s", written[0], written[1])
		}
	})
	// A Z3 that ends at once fails the package, and frees the slot of its
	// process once, so that the run neither hangs nor starts a fifth.
	t.Run("a Z3 that ends at start", func(t *testing.T) {
		dir := cacheDir(t)
		done := make(chan error, 1)
		go func() {
			_, err := fakeSolver(t, dir, "exit", "")
			done <- err
		}()
		select {
		case err := <-done:
			if err == nil {
				t.Fatal("a Z3 that ends at start was accepted")
			}
		case <-time.After(20 * time.Second):
			t.Fatal("a Z3 that ends at start hangs the run")
		}
	})

	// The trim removes files, so a directory that holds anything and is
	// not an answer cache is refused, and the trim of a cache removes
	// nothing but the cache's own files.
	t.Run("a directory that is not a cache", func(t *testing.T) {
		for name, content := range map[string]string{"notes.txt": "mine", tagName: "Signature: 8a477f597d28d172789f06886806bc55\n"} {
			dir := cacheDir(t)
			if err := os.MkdirAll(dir, 0o755); err != nil {
				t.Fatal(err)
			}
			if err := os.WriteFile(filepath.Join(dir, name), []byte(content), 0o644); err != nil {
				t.Fatal(err)
			}
			if _, err := opened(t, z3, dir); err == nil || !strings.Contains(err.Error(), "not an answer cache") {
				t.Fatalf("a directory holding %s was accepted: %v", name, err)
			}
			if got, _ := os.ReadFile(filepath.Join(dir, name)); string(got) != content {
				t.Fatalf("%s was changed", name)
			}
		}
	})
	// Another run makes the cache between the first look for the mark and
	// the listing of the directory: the directory is a cache.
	t.Run("a cache made by another run meanwhile", func(t *testing.T) {
		dir := cacheDir(t)
		if err := os.MkdirAll(dir, 0o755); err != nil {
			t.Fatal(err)
		}
		afterTagRead = func() {
			afterTagRead = nil
			if err := claim(dir); err != nil {
				t.Fatal(err)
			}
			if err := os.WriteFile(filepath.Join(dir, "trimmed"), nil, 0o644); err != nil {
				t.Fatal(err)
			}
		}
		defer func() { afterTagRead = nil }()
		if err := claim(dir); err != nil {
			t.Fatalf("a cache made meanwhile is refused: %v", err)
		}
	})
	t.Run("two runs making one cache at once", func(t *testing.T) {
		for range 50 {
			dir := cacheDir(t)
			var wg sync.WaitGroup
			errs := make([]error, 2)
			for i := range 2 {
				wg.Go(func() {
					errs[i] = claim(dir)
					if errs[i] == nil {
						errs[i] = os.MkdirAll(filepath.Join(dir, "z3-"+strings.Repeat("0", 32)), 0o755)
					}
				})
			}
			wg.Wait()
			for _, err := range errs {
				if err != nil {
					t.Fatalf("one of two runs making a cache at once failed: %v", err)
				}
			}
		}
	})
	t.Run("files of others in a cache", func(t *testing.T) {
		dir := cacheDir(t)
		s := cached(t, z3, dir)
		s.Prove(nil, goal, Options{})
		entry := entries(t, dir)[0]
		shard := filepath.Dir(entry)
		foreign := []string{
			filepath.Join(dir, "notes.txt"),
			filepath.Join(dir, "sub", "old.txt"),
			filepath.Join(filepath.Dir(shard), "foreign.txt"),
			filepath.Join(shard, "foreign"),
			filepath.Join(shard, strings.Repeat("a", 61)),
		}
		old := time.Now().Add(-10 * 24 * time.Hour)
		for _, path := range append(foreign, entry) {
			if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
				t.Fatal(err)
			}
			if path != entry {
				if err := os.WriteFile(path, []byte("mine"), 0o644); err != nil {
					t.Fatal(err)
				}
			}
			if err := os.Chtimes(path, old, old); err != nil {
				t.Fatal(err)
			}
		}
		savedLimit := cacheLimit
		cacheLimit = 0
		defer func() { cacheLimit = savedLimit }()
		if err := s.disk.trim(time.Now().Add(2 * trimEvery)); err != nil {
			t.Fatal(err)
		}
		if _, err := os.Stat(entry); !errors.Is(err, fs.ErrNotExist) {
			t.Fatal("an entry unused for ten days was kept")
		}
		for _, path := range foreign {
			if got, err := os.ReadFile(path); err != nil || string(got) != "mine" {
				t.Fatalf("the trim removed or changed %s, which is not the cache's", path)
			}
		}
		// A cache made before is one, whatever else it holds now.
		if _, err := opened(t, z3, dir); err != nil {
			t.Fatalf("the cache is refused: %v", err)
		}
	})

	// An asker that panics, here because the cache cannot be written,
	// ends its problem's flight, and an asker waiting for its answer asks
	// again instead of waiting for ever.
	t.Run("an asker that panics while another waits", func(t *testing.T) {
		dir := cacheDir(t)
		t.Setenv("VEGO_FAKE_Z3_DELAY", "1000")
		s, err := fakeSolver(t, dir, "unsat\n(:reason-unknown \"\")\n(:rlimit 7)", "")
		if err != nil {
			t.Fatal(err)
		}
		if err := os.Chmod(s.disk.dir, 0o555); err != nil {
			t.Fatal(err)
		}
		defer os.Chmod(s.disk.dir, 0o755)
		var wg sync.WaitGroup
		var messages [2]string
		for i := range 2 {
			wg.Go(func() {
				time.Sleep(time.Duration(i) * 300 * time.Millisecond)
				messages[i] = cacheFailure(func() { s.Prove(nil, goal, Options{}) })
			})
		}
		returned := make(chan struct{})
		go func() { wg.Wait(); close(returned) }()
		select {
		case <-returned:
		case <-time.After(10 * time.Second):
			t.Fatal("the second asker of the same problem has not returned 10 s after the first one panicked")
		}
		for i, message := range messages {
			if !strings.Contains(message, "cannot be written") {
				t.Errorf("asker %d got %q, want the failure to write the cache", i, message)
			}
		}
	})
	// A speculative asker that finds the cache untrustworthy, here by the
	// watch, makes every later question of another asker fail, so that no
	// verification uses the entry that was found wrong.
	t.Run("a wrong entry that a speculative asker found", func(t *testing.T) {
		dir := cacheDir(t)
		s := cached(t, z3, dir)
		key := Script([]*logic.Term{logic.Not(goal)}, Options{}) + "\x00"
		s.disk.write(key, reply{check: []string{"sat", `(:reason-unknown "")`, "(:rlimit 7)"}})
		saved := watchRate
		defer func() { watchRate = saved }()
		watchRate = 1
		if message := cacheFailure(func() { s.Prove(nil, goal, Options{Speculative: true}) }); !strings.Contains(message, "otherwise") {
			t.Fatalf("the speculative asker got %q, want the watch's failure", message)
		}
		watchRate = 1 << 30
		if message := cacheFailure(func() { s.Prove(nil, goal, Options{}) }); !strings.Contains(message, "otherwise") {
			t.Fatalf("the asker after it got %q, want the watch's failure", message)
		}
	})
	t.Run("a directory inside a module", func(t *testing.T) {
		root := t.TempDir()
		saved := searchedUpTo
		searchedUpTo = root
		defer func() { searchedUpTo = saved }()
		module := filepath.Join(root, "m")
		if err := os.MkdirAll(module, 0o755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(filepath.Join(module, "go.mod"), []byte("module m\n"), 0o644); err != nil {
			t.Fatal(err)
		}
		if _, err := opened(t, z3, filepath.Join(module, "a", "cache")); err == nil || !strings.Contains(err.Error(), "outside any") {
			t.Fatalf("a cache inside a module was accepted: %v", err)
		}
	})

	t.Run("a directory that cannot be written", func(t *testing.T) {
		dir := cacheDir(t)
		s := cached(t, z3, dir)
		if err := os.Chmod(s.disk.dir, 0o555); err != nil {
			t.Fatal(err)
		}
		defer os.Chmod(s.disk.dir, 0o755)
		if message := cacheFailure(func() { s.Prove(nil, goal, Options{}) }); !strings.Contains(message, "cannot be written") {
			t.Fatalf("got %q, want a failure that says the cache cannot be written", message)
		}
	})

	// Trimming removes what was not used for long, temporary files that a
	// run left, and then the oldest until the cache fits its bound.
	t.Run("trimming", func(t *testing.T) {
		dir := cacheDir(t)
		s := cached(t, z3, dir)
		for i := range 4 {
			s.Prove(nil, logic.Le(x, logic.Add(x, logic.IntLit(int64(20+i)))), Options{})
		}
		found := entries(t, dir)
		old := time.Now().Add(-6 * 24 * time.Hour)
		if err := os.Chtimes(found[0], old, old); err != nil {
			t.Fatal(err)
		}
		left := filepath.Join(filepath.Dir(found[1]), tempPrefix+"left")
		if err := os.WriteFile(left, []byte("x"), 0o644); err != nil {
			t.Fatal(err)
		}
		recent := filepath.Join(filepath.Dir(found[1]), tempPrefix+"recent")
		if err := os.WriteFile(recent, []byte("x"), 0o644); err != nil {
			t.Fatal(err)
		}
		// The trim below is two days ahead, at which this file is an hour
		// old.
		late := time.Now().Add(2*trimEvery - time.Hour)
		if err := os.Chtimes(recent, late, late); err != nil {
			t.Fatal(err)
		}
		if err := os.Chtimes(left, old, old); err != nil {
			t.Fatal(err)
		}
		infos := map[string]int64{}
		for _, path := range found[1:] {
			info, _ := os.Stat(path)
			infos[path] = info.Size()
		}
		// The newest entry alone fits.
		newest := found[1]
		for i, path := range found[1:] {
			when := time.Now().Add(-time.Duration(len(found)-i) * time.Hour)
			os.Chtimes(path, when, when)
			newest = path
		}
		savedLimit := cacheLimit
		cacheLimit = infos[newest]
		defer func() { cacheLimit = savedLimit }()
		if err := s.disk.trim(time.Now().Add(time.Hour)); err != nil {
			t.Fatal(err)
		}
		if got := entries(t, dir); len(got) != 4 {
			t.Fatalf("trimmed within a day of the last trim: %d entries", len(got))
		}
		if err := s.disk.trim(time.Now().Add(2 * trimEvery)); err != nil {
			t.Fatal(err)
		}
		got := entries(t, dir)
		if len(got) != 1 || got[0] != newest {
			t.Fatalf("after trimming, %v remain; want only %s", got, newest)
		}
		if _, err := os.Stat(left); !errors.Is(err, fs.ErrNotExist) {
			t.Fatalf("a temporary file left for a day was kept")
		}
		if _, err := os.Stat(recent); err != nil {
			t.Fatalf("a recent temporary file was removed")
		}
	})
}

// TestStoredAnswersAreZ3s solves random problems, values asked for some,
// on four workers that keep their answers on disk, and then solves every
// entry written again with Z3: each kept reply must be the reply Z3 gives
// to the problem the entry holds, which a writer that paired a reply with
// another problem in flight would break.
func TestStoredAnswersAreZ3s(t *testing.T) {
	z3 := z3Binary(t)
	dir := cacheDir(t)
	s := cached(t, z3, dir)
	rng := rand.New(rand.NewPCG(7, 8))
	type problem struct {
		hyps   []*logic.Term
		goal   *logic.Term
		values bool
	}
	vars := []*logic.Term{logic.Const("x", logic.Int), logic.Const("y", logic.Int), logic.Const("z", logic.Int)}
	problems := make([]problem, 400)
	for i := range problems {
		g := &generator{rng: rng, wide: true, vars: vars}
		var hyps []*logic.Term
		for range rng.IntN(4) {
			hyps = append(hyps, g.formula(2))
		}
		problems[i] = problem{hyps, g.formula(2), rng.IntN(3) == 0}
	}
	var wg sync.WaitGroup
	next := make(chan int)
	for range maxProcesses {
		wg.Go(func() {
			for i := range next {
				p := problems[i]
				opts := Options{Preds: definitions(), Effort: 200_000}
				if p.values {
					s.Model(append(p.hyps[:len(p.hyps):len(p.hyps)], logic.Not(p.goal)), opts, vars)
				} else {
					s.Prove(p.hyps, p.goal, opts)
				}
			}
		})
	}
	for i := range problems {
		next <- i
	}
	close(next)
	wg.Wait()
	live, err := start(z3)
	if err != nil {
		t.Fatal(err)
	}
	defer endIdle(live)
	found := entries(t, dir)
	if len(found) < 300 {
		t.Fatalf("only %d entries were written", len(found))
	}
	for _, path := range found {
		content, err := os.ReadFile(path)
		if err != nil {
			t.Fatal(err)
		}
		key, stored, problem := decodeEntry(content)
		if problem != "" {
			t.Fatalf("%s: %s", path, problem)
		}
		cut := strings.LastIndexByte(key, 0)
		script, names := key[:cut], strings.Fields(key[cut+1:])
		_, r, err := live.solve(script, names, asker{})
		if err != nil {
			t.Fatal(err)
		}
		if !r.equal(stored) {
			t.Fatalf("%s keeps %+v for a problem that Z3 answers with %+v", path, stored, r)
		}
	}
	t.Logf("%d entries checked against Z3", len(found))
}

// TestOwnEntriesAreNotStored checks that an answer this process solved and
// wrote is never counted as one kept by another run when an asker reads it
// back from the directory: one asker misses it in memory while another is
// between writing the entry and keeping the answer, and an answer too long
// to be kept in memory is read back. A run that starts with an empty
// directory counts no stored answers, whatever the timing.
func TestOwnEntriesAreNotStored(t *testing.T) {
	z3 := z3Binary(t)
	x := logic.Const("x", logic.Int)
	goal := logic.Le(x, logic.Add(x, logic.IntLit(3)))

	t.Run("read while another asker keeps it", func(t *testing.T) {
		s := cached(t, z3, cacheDir(t))
		flown, letFly := make(chan struct{}), make(chan struct{})
		missed, letRead := make(chan struct{}), make(chan struct{})
		var mu sync.Mutex
		unremembered, flights := 0, 0
		at(t, func(point string, _ *process) {
			mu.Lock()
			switch point {
			case "unremembered":
				unremembered++
				if unremembered == 2 {
					mu.Unlock()
					close(missed)
					<-letRead
					return
				}
			case "flown":
				flights++
				if flights == 1 {
					mu.Unlock()
					close(flown)
					<-letFly
					return
				}
			}
			mu.Unlock()
		})
		var costs [2]Cost
		first := make(chan struct{})
		go func() {
			defer close(first)
			s.Prove(nil, goal, Options{Observe: func(c Cost) { costs[0] = c }})
		}()
		<-flown
		second := make(chan struct{})
		go func() {
			defer close(second)
			s.Prove(nil, goal, Options{Observe: func(c Cost) { costs[1] = c }})
		}()
		<-missed
		close(letFly)
		<-first
		close(letRead)
		<-second
		if costs[0].Stored || !costs[1].Cached || costs[1].Stored {
			t.Fatalf("costs %+v, want the second answer read back and not counted as stored", costs)
		}
	})

	t.Run("read back when not kept in memory", func(t *testing.T) {
		saved := cacheBytes
		cacheBytes = 0
		t.Cleanup(func() { cacheBytes = saved })
		s := cached(t, z3, cacheDir(t))
		var costs []Cost
		observed := Options{Observe: func(c Cost) { costs = append(costs, c) }}
		s.Prove(nil, goal, observed)
		s.Prove(nil, goal, observed)
		if len(costs) != 2 || costs[0].Stored || !costs[1].Cached || costs[1].Stored {
			t.Fatalf("costs %+v, want the second answer read back and not counted as stored", costs)
		}
	})
}
