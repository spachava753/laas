package solver

import (
	"bufio"
	"bytes"
	"compress/gzip"
	"crypto/rand"
	"crypto/sha256"
	"encoding/hex"
	"errors"
	"fmt"
	"io"
	"io/fs"
	mrand "math/rand/v2"
	"os"
	"path/filepath"
	"runtime"
	"slices"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"
)

// Answers kept on disk, when a cache directory is given, are a memo of Z3
// as a function: the exact text a process reads for one problem, mapped to
// the exact lines it printed back. Nothing parsed is kept, so the reader
// decides what a reply means with its own code, as for a live reply.
//
// What makes a stored answer the answer Z3 would give again is the premise
// of the cache in the process (see answer): Z3 of one binary, with the
// options fixed on its command line and the limit in the text, answers a
// text the same way every time. On disk that premise could fail in ways a
// process cannot, and each is excluded or fails the run:
//
//   - Another Z3, a rebuilt one, other libraries, other options, another
//     system or processor. The entries live in a directory named by a hash
//     of everything a process runs: the binary and every file it maps with
//     code, read from /proc for every process started, the command line,
//     the system, and the processor's model and flags. A process whose files
//     differ from the directory's, or whose binary is not the file the path
//     names (a script that runs Z3), stops the run.
//   - An entry damaged, cut short, or for another text. Each entry ends in a
//     hash of what precedes it and holds the text it answers, which must be
//     the text being asked, byte for byte. Any doubt stops the run; nothing
//     is skipped or rewritten silently. A file that is missing is a miss.
//   - Two runs that write the same entry. An entry is published with
//     link(2), which fails when the name exists; the loser compares its
//     reply with the winner's, and a difference stops the run, since Z3
//     would then have answered one text in two ways.
//   - A drift the identity does not cover. Each run solves again, live, a
//     sample of the answers it reads, drawn at random for the run, and a
//     difference stops the run.
//
// An edit that keeps an entry well formed cannot be told from an answer,
// as an edited Z3 binary cannot; the cache directory is trusted as the
// binary is, which the guide states, and a run that read an answer from it
// says so.

// cacheFormat names the format of an entry and of the identity. A change to
// either, or to what a process is sent around a problem, changes it.
const cacheFormat = "vego z3 answers 1"

// Bounds of the cache: an entry not used for entryAge is removed, and then
// the oldest until the directory holds at most cacheLimit bytes; a
// temporary file older than tempAge was left by a run that ended between
// writing and publishing it. The directory is trimmed at most once in
// trimEvery, when a solver starts.
var (
	entryAge   = 5 * 24 * time.Hour
	tempAge    = 24 * time.Hour
	trimEvery  = 24 * time.Hour
	cacheLimit = int64(1 << 30)
	touchAfter = time.Hour
)

// watchRate is the share of answers read from disk that are solved again,
// live, to watch the premise: one in watchRate.
var watchRate = 256

// CacheError is panicked when the cache directory cannot be trusted or
// used: an entry is damaged, a process is not the Z3 the directory is for,
// Z3 answered one text in two ways, or the directory cannot be written.
type CacheError struct{ Err error }

func (e *CacheError) Error() string { return e.Err.Error() }

func cacheFault(dir, format string, args ...any) {
	panic(&CacheError{fmt.Errorf(format+"; to empty the cache, remove %s", append(args, dir)...)})
}

// disk is the cache of one solver in a directory.
type disk struct {
	root string
	// dir is the directory of the identity of the processes, which every
	// process started must have; see identify.
	mu       sync.Mutex
	dir      string
	identity string
	hashes   map[fileKey]string
	rng      *mrand.Rand
}

// fileKey tells a file and its state apart, so that each is hashed once.
type fileKey struct {
	dev, ino uint64
	size     int64
	mtime    int64
}

// openDisk checks the directory and trims it when it is due.
func openDisk(root string) (*disk, error) {
	if runtime.GOOS != "linux" {
		return nil, fmt.Errorf("-vego.cache needs /proc to identify the files Z3 runs, which %s does not have", runtime.GOOS)
	}
	abs, err := filepath.Abs(root)
	if err != nil {
		return nil, err
	}
	if inside := repository(abs); inside != "" {
		return nil, fmt.Errorf("the answer cache %s is inside %s, which holds %s; a cache in a module or a repository could carry its answers into the runs of others, so it must be outside any",
			abs, filepath.Dir(inside), filepath.Base(inside))
	}
	if err := os.MkdirAll(abs, 0o755); err != nil {
		return nil, fmt.Errorf("the answer cache %s cannot be made: %v", abs, err)
	}
	var seed [16]byte
	if _, err := rand.Read(seed[:]); err != nil {
		return nil, err
	}
	d := &disk{
		root:   abs,
		hashes: map[fileKey]string{},
		rng:    mrand.New(mrand.NewPCG(binaryUint(seed[:8]), binaryUint(seed[8:]))),
	}
	if err := d.trim(time.Now()); err != nil {
		return nil, err
	}
	return d, nil
}

func binaryUint(b []byte) uint64 {
	var n uint64
	for _, c := range b {
		n = n<<8 | uint64(c)
	}
	return n
}

// searchedUpTo, when set, is a directory whose ancestors repository does
// not search, so that the tests can make caches under a temporary directory
// that may itself be inside a repository.
var searchedUpTo string

// SearchRepositoriesBelow makes the search for a module or a repository
// around a cache directory stop at dir, until the returned function is
// called. It is for tests, whose temporary directories may be inside a
// repository.
func SearchRepositoriesBelow(dir string) func() {
	saved := searchedUpTo
	searchedUpTo = dir
	return func() { searchedUpTo = saved }
}

// repository returns the mark of the directory at or above dir that is a
// module or the root of a repository, or "".
func repository(dir string) string {
	for dir != searchedUpTo {
		for _, mark := range []string{"go.mod", ".git", ".hg", ".svn", ".bzr", ".jj"} {
			if _, err := os.Lstat(filepath.Join(dir, mark)); err == nil {
				return filepath.Join(dir, mark)
			}
		}
		parent := filepath.Dir(dir)
		if parent == dir {
			return ""
		}
		dir = parent
	}
	return ""
}

// identify checks the process against the identity of the directory, or
// sets it for the first process. It reads what the process runs from /proc
// after the process has answered, so that a program that starts another
// with exec has done so.
func (d *disk) identify(pid int, path string) error {
	proc := "/proc/" + strconv.Itoa(pid)
	exe, err := os.Stat(proc + "/exe")
	if err != nil {
		return fmt.Errorf("the binary of Z3 process %d cannot be read from /proc: %v", pid, err)
	}
	named, err := os.Stat(path)
	if err != nil {
		return fmt.Errorf("%s cannot be read: %v", path, err)
	}
	if !os.SameFile(exe, named) {
		target, _ := os.Readlink(proc + "/exe")
		return fmt.Errorf("the answer cache needs the Z3 binary itself, and %s runs %s; name the binary with -vego.z3, or run without -vego.cache", path, target)
	}
	maps, err := os.ReadFile(proc + "/maps")
	if err != nil {
		return fmt.Errorf("the files of Z3 process %d cannot be read from /proc: %v", pid, err)
	}
	files := []string{}
	for line := range strings.Lines(string(maps)) {
		// address perms offset dev inode path, where the path may hold
		// spaces; only files mapped with code identify what runs.
		fields := strings.Fields(line)
		if len(fields) < 6 || !strings.Contains(fields[1], "x") {
			continue
		}
		file := strings.TrimSpace(strings.Join(strings.Fields(line)[5:], " "))
		if !strings.HasPrefix(file, "/") {
			continue
		}
		if strings.HasSuffix(file, " (deleted)") {
			return fmt.Errorf("Z3 process %d runs %s, which was replaced while it ran", pid, file)
		}
		files = append(files, file)
	}
	slices.Sort(files)
	files = slices.Compact(files)
	d.mu.Lock()
	defer d.mu.Unlock()
	var id strings.Builder
	fmt.Fprintf(&id, "%s\nsettings %s\nsystem %s/%s\n", cacheFormat, strings.Join(settings, " "), runtime.GOOS, runtime.GOARCH)
	cpu, err := processor()
	if err != nil {
		return err
	}
	id.WriteString(cpu)
	exeHash, err := d.hash(proc + "/exe")
	if err != nil {
		return err
	}
	fmt.Fprintf(&id, "binary %s\n", exeHash)
	// The files are identified by their contents alone: a copy of the
	// same binary elsewhere answers as it does.
	var mapped []string
	for _, file := range files {
		h, err := d.hash(file)
		if err != nil {
			return err
		}
		mapped = append(mapped, h)
	}
	slices.Sort(mapped)
	for _, h := range slices.Compact(mapped) {
		fmt.Fprintf(&id, "file %s\n", h)
	}
	identity := id.String()
	if d.identity == "" {
		sum := sha256.Sum256([]byte(identity))
		dir := filepath.Join(d.root, "z3-"+hex.EncodeToString(sum[:16]))
		if err := os.MkdirAll(dir, 0o755); err != nil {
			return fmt.Errorf("the answer cache %s cannot be made: %v", dir, err)
		}
		// The identity is written for a person to read; nothing reads it.
		description := filepath.Join(dir, "identity")
		if _, err := os.Stat(description); errors.Is(err, fs.ErrNotExist) {
			if err := publish(dir, description, []byte(identity)); err != nil && !errors.Is(err, fs.ErrExist) {
				return fmt.Errorf("the answer cache %s cannot be written: %v", dir, err)
			}
		}
		d.identity, d.dir = identity, dir
		return nil
	}
	if identity != d.identity {
		return fmt.Errorf("a Z3 process of this run runs other files than the first one did, so its answers cannot be kept with theirs:\n%s\nagainst\n%s", identity, d.identity)
	}
	return nil
}

// processor returns the model and the flags of the processor, which are
// what may change how Z3 computes; its speed and microcode are left out.
func processor() (string, error) {
	f, err := os.Open("/proc/cpuinfo")
	if err != nil {
		return "", fmt.Errorf("the processor cannot be read from /proc/cpuinfo: %v", err)
	}
	defer f.Close()
	var model, flags string
	lines := bufio.NewScanner(f)
	lines.Buffer(nil, 1<<20)
	for lines.Scan() && (model == "" || flags == "") {
		name, value, ok := strings.Cut(lines.Text(), ":")
		switch name = strings.TrimSpace(name); {
		case !ok:
		case name == "model name" && model == "":
			model = strings.TrimSpace(value)
		case name == "flags" && flags == "":
			flags = strings.TrimSpace(value)
		}
	}
	return "processor " + model + "\nflags " + flags + "\n", lines.Err()
}

// hash returns the SHA-256 of a file's contents, computed once for each
// state of the file.
func (d *disk) hash(path string) (string, error) {
	info, err := os.Stat(path)
	if err != nil {
		return "", fmt.Errorf("%s, which Z3 runs, cannot be read: %v", path, err)
	}
	stat, ok := info.Sys().(*syscall.Stat_t)
	if !ok {
		return "", fmt.Errorf("%s, which Z3 runs, cannot be told apart from another file", path)
	}
	key := fileKey{uint64(stat.Dev), stat.Ino, info.Size(), info.ModTime().UnixNano()}
	if h, ok := d.hashes[key]; ok {
		return h, nil
	}
	f, err := os.Open(path)
	if err != nil {
		return "", fmt.Errorf("%s, which Z3 runs, cannot be read: %v", path, err)
	}
	defer f.Close()
	sum := sha256.New()
	if _, err := io.Copy(sum, f); err != nil {
		return "", fmt.Errorf("%s, which Z3 runs, cannot be read: %v", path, err)
	}
	h := hex.EncodeToString(sum.Sum(nil))
	d.hashes[key] = h
	return h, nil
}

// reply is what a process printed for one problem: the lines up to the
// marker after the check-sat and the two get-info commands, and, when
// values were asked and the answer is not unsat, the lines of the
// get-value.
type reply struct {
	check  []string
	values []string
	asked  bool
}

func (r reply) equal(other reply) bool {
	return slices.Equal(r.check, other.check) && r.asked == other.asked && slices.Equal(r.values, other.values)
}

// entryPath returns where the entry for a problem key is kept.
func (d *disk) entryPath(key string) string {
	sum := sha256.Sum256([]byte(key))
	name := hex.EncodeToString(sum[:])
	return filepath.Join(d.dir, name[:2], name[2:])
}

// read returns the reply stored for the key, and whether there is one. A
// file that does not exist is a miss; one that exists and is not a whole
// entry for exactly this key stops the run.
func (d *disk) read(key string) (reply, bool) {
	path := d.entryPath(key)
	content, err := os.ReadFile(path)
	switch {
	case errors.Is(err, fs.ErrNotExist):
		return reply{}, false
	case err != nil:
		cacheFault(d.root, "the answer cache entry %s cannot be read: %v", path, err)
	}
	stored, r, problem := decodeEntry(content)
	if problem == "" && stored != key {
		problem = "it holds the answer to another problem"
	}
	if problem != "" {
		cacheFault(d.root, "the answer cache entry %s is damaged: %s", path, problem)
	}
	if info, err := os.Stat(path); err == nil && time.Since(info.ModTime()) > touchAfter {
		now := time.Now()
		if err := os.Chtimes(path, now, now); err != nil && !errors.Is(err, fs.ErrNotExist) {
			cacheFault(d.root, "the answer cache entry %s cannot be marked as used: %v", path, err)
		}
	}
	return r, true
}

// write keeps the reply for the key. When another run kept one first, the
// two must be the same.
func (d *disk) write(key string, r reply) {
	path := d.entryPath(key)
	content := encodeEntry(key, r)
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		cacheFault(d.root, "the answer cache %s cannot be written: %v; run without -vego.cache or with another directory", d.root, err)
	}
	err := publish(filepath.Dir(path), path, content)
	switch {
	case err == nil:
		return
	case !errors.Is(err, fs.ErrExist):
		cacheFault(d.root, "the answer cache %s cannot be written: %v; run without -vego.cache or with another directory", d.root, err)
	}
	other, ok := d.read(key)
	if ok && !other.equal(r) {
		cacheFault(d.root, "Z3 answered one problem in two ways, %q against %q as kept in %s, so its answers cannot be kept", r.check, other.check, path)
	}
}

// tempPrefix starts the name of every file that is not yet published.
const tempPrefix = ".tmp-"

// publish writes content to a temporary file in dir and links it to path,
// so that a reader sees either no file or the whole of it. It fails with
// fs.ErrExist when path exists.
func publish(dir, path string, content []byte) error {
	f, err := os.CreateTemp(dir, tempPrefix+"*")
	if err != nil {
		return err
	}
	temp := f.Name()
	defer os.Remove(temp)
	if _, err := f.Write(content); err != nil {
		f.Close()
		return err
	}
	if err := f.Close(); err != nil {
		return err
	}
	return os.Link(temp, path)
}

// encodeEntry writes an entry: the format line, the key compressed, the
// reply, and the SHA-256 of all that.
func encodeEntry(key string, r reply) []byte {
	var compressed bytes.Buffer
	z := gzip.NewWriter(&compressed)
	_, _ = z.Write([]byte(key))
	_ = z.Close()
	var b bytes.Buffer
	fmt.Fprintf(&b, "%s\nproblem %d\n", cacheFormat, compressed.Len())
	b.Write(compressed.Bytes())
	fmt.Fprintf(&b, "\ncheck %d\n", len(r.check))
	for _, line := range r.check {
		b.WriteString(line + "\n")
	}
	if r.asked {
		fmt.Fprintf(&b, "values %d\n", len(r.values))
		for _, line := range r.values {
			b.WriteString(line + "\n")
		}
	} else {
		b.WriteString("no values\n")
	}
	sum := sha256.Sum256(b.Bytes())
	fmt.Fprintf(&b, "sum %s\n", hex.EncodeToString(sum[:]))
	return b.Bytes()
}

// decodeEntry reads an entry, or says what is wrong with it.
func decodeEntry(content []byte) (key string, r reply, problem string) {
	if len(content) == 0 || content[len(content)-1] != '\n' {
		return "", reply{}, "it does not end in its hash"
	}
	cut := bytes.LastIndexByte(content[:len(content)-1], '\n') + 1
	body, sumLine := content[:cut], string(content[cut:len(content)-1])
	if !strings.HasPrefix(sumLine, "sum ") {
		return "", reply{}, "it does not end in its hash"
	}
	sum := sha256.Sum256(body)
	if sumLine != "sum "+hex.EncodeToString(sum[:]) {
		return "", reply{}, "its hash does not match its contents"
	}
	rest := body
	line := func() (string, bool) {
		i := bytes.IndexByte(rest, '\n')
		if i < 0 {
			return "", false
		}
		l := string(rest[:i])
		rest = rest[i+1:]
		return l, true
	}
	count := func(prefix string) (int, bool) {
		l, ok := line()
		if !ok || !strings.HasPrefix(l, prefix+" ") {
			return 0, false
		}
		n, err := strconv.Atoi(strings.TrimPrefix(l, prefix+" "))
		return n, err == nil && n >= 0
	}
	if l, ok := line(); !ok || l != cacheFormat {
		return "", reply{}, "it is not in the format " + cacheFormat
	}
	n, ok := count("problem")
	if !ok || n > len(rest) {
		return "", reply{}, "its problem is cut short"
	}
	z, err := gzip.NewReader(bytes.NewReader(rest[:n]))
	if err != nil {
		return "", reply{}, "its problem cannot be read: " + err.Error()
	}
	text, err := io.ReadAll(z)
	if err != nil {
		return "", reply{}, "its problem cannot be read: " + err.Error()
	}
	rest = rest[n:]
	if l, ok := line(); !ok || l != "" {
		return "", reply{}, "its problem is not followed by its reply"
	}
	lines := func(n int) ([]string, bool) {
		out := []string{}
		for range n {
			l, ok := line()
			if !ok {
				return nil, false
			}
			out = append(out, l)
		}
		return out, true
	}
	k, ok := count("check")
	if !ok {
		return "", reply{}, "its reply is not in the format"
	}
	if r.check, ok = lines(k); !ok {
		return "", reply{}, "its reply is cut short"
	}
	if l := string(rest); strings.HasPrefix(l, "no values\n") {
		rest = rest[len("no values\n"):]
	} else {
		m, ok := count("values")
		if !ok {
			return "", reply{}, "its values are not in the format"
		}
		r.asked = true
		if r.values, ok = lines(m); !ok {
			return "", reply{}, "its values are cut short"
		}
	}
	if len(rest) != 0 {
		return "", reply{}, "it has more after its reply"
	}
	return string(text), r, ""
}

// trim removes the entries not used for entryAge, the temporary files left
// for tempAge, and then the oldest entries until the cache holds at most
// cacheLimit bytes, when it was last trimmed trimEvery ago or never. A file
// that another run removed meanwhile is no error.
func (d *disk) trim(now time.Time) error {
	marker := filepath.Join(d.root, "trimmed")
	if info, err := os.Stat(marker); err == nil && now.Sub(info.ModTime()) < trimEvery && info.ModTime().Before(now.Add(time.Minute)) {
		return nil
	}
	type kept struct {
		path  string
		size  int64
		mtime time.Time
	}
	var entries []kept
	var total int64
	err := filepath.WalkDir(d.root, func(path string, entry fs.DirEntry, err error) error {
		if errors.Is(err, fs.ErrNotExist) {
			return nil
		}
		if err != nil {
			return err
		}
		if entry.IsDir() || path == marker || entry.Name() == "identity" {
			return nil
		}
		info, err := entry.Info()
		if errors.Is(err, fs.ErrNotExist) {
			return nil
		}
		if err != nil {
			return err
		}
		age := now.Sub(info.ModTime())
		switch {
		case strings.HasPrefix(entry.Name(), tempPrefix) && age > tempAge, !strings.HasPrefix(entry.Name(), tempPrefix) && age > entryAge:
			if err := os.Remove(path); err != nil && !errors.Is(err, fs.ErrNotExist) {
				return err
			}
		case !strings.HasPrefix(entry.Name(), tempPrefix):
			entries = append(entries, kept{path, info.Size(), info.ModTime()})
			total += info.Size()
		}
		return nil
	})
	if err != nil {
		return fmt.Errorf("the answer cache %s cannot be trimmed: %v", d.root, err)
	}
	slices.SortFunc(entries, func(a, b kept) int { return a.mtime.Compare(b.mtime) })
	for _, e := range entries {
		if total <= cacheLimit {
			break
		}
		if err := os.Remove(e.path); err != nil && !errors.Is(err, fs.ErrNotExist) {
			return fmt.Errorf("the answer cache %s cannot be trimmed: %v", d.root, err)
		}
		total -= e.size
	}
	if err := os.WriteFile(marker, nil, 0o644); err != nil {
		return fmt.Errorf("the answer cache %s cannot be written: %v", d.root, err)
	}
	now = time.Now()
	return os.Chtimes(marker, now, now)
}
