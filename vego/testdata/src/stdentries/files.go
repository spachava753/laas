package stdentries

import (
	"fmt"
	"io"
	"os"
)

// ReadConfig reads at most 4096 bytes of a file, the way a verified
// function reads a file: Open, a bounded loop of Read, and Close.
//
// @Requires |name| <= 4096
// @Ensures err = nil -> |data| <= 4096
func ReadConfig(name string) (data []byte, err error) {
	f, err := os.Open(name)
	if err != nil {
		return nil, fmt.Errorf("open %s: %w", name, err)
	}
	buf := make([]byte, 4096)
	n := 0
	// @Invariant 0 <= n And n <= 4096 And |buf| = 4096 And fresh(buf)
	// @Variant 4096 - n
	for n < len(buf) {
		m, rerr := f.Read(buf[n:])
		n += m
		if rerr == io.EOF || m == 0 {
			break
		}
		if rerr != nil {
			f.Close()
			return nil, fmt.Errorf("read %s: %w", name, rerr)
		}
	}
	if cerr := f.Close(); cerr != nil {
		return nil, fmt.Errorf("close %s: %w", name, cerr)
	}
	return buf[:n], nil
}

// ReadForever does not stop when a read returns nothing.
//
// @Requires |name| <= 4096
// @Ensures True
func ReadForever(name string) (n int, err error) {
	f, err := os.Open(name)
	if err != nil {
		return 0, err
	}
	buf := make([]byte, 64)
	// @Invariant 0 <= n
	// @Variant MaxInt - n
	for { // want `loop variant may not decrease: MaxInt - n`
		m, rerr := f.Read(buf)
		if rerr != nil {
			break
		}
		n += m // want `addition may overflow int`
	}
	f.Close()
	return n, nil
}

// Report writes a report to a new file through fmt, which takes the file
// as an io.Writer. Create's error has a variable of its own, since err,
// the result, is also given what Fprintf returns.
//
// @Requires |name| <= 4096 And |title| <= 1000
// @Ensures True
func Report(name, title string, count int) (err error) {
	f, cerr := os.Create(name)
	if cerr != nil {
		return fmt.Errorf("create %s: %w", name, cerr)
	}
	if _, werr := fmt.Fprintf(f, "%s: %d\n", title, count); werr != nil {
		f.Close()
		return werr
	}
	return f.Close()
}

// ReportReused reuses err for a call whose errors nothing vouches for,
// after it wraps the error of os.Create; only os.Create reaches the %w.
//
// @Requires |name| <= 4096 And |title| <= 1000 And w != nil
// @Ensures True
func ReportReused(name, title string, w io.Writer) (err error) {
	f, err := os.Create(name)
	if err != nil {
		return fmt.Errorf("create %s: %w", name, err)
	}
	_, err = w.Write([]byte(title))
	f.Close()
	return err
}

// Save writes a file in a directory it makes.
//
// @Requires |dir| <= 1024 And |name| <= 4096 And |data| <= 1000000
// @Ensures True
func Save(dir, name string, data []byte) (err error) {
	if err := os.MkdirAll(dir, 0o755); err != nil {
		return fmt.Errorf("make %s: %w", dir, err)
	}
	if err := os.WriteFile(name, data, 0o644); err != nil {
		return fmt.Errorf("write %s: %w", name, err)
	}
	return nil
}

// SaveAnywhere does not bound the name.
//
// @Ensures True
func SaveAnywhere(name string) (err error) {
	return os.WriteFile(name, nil, 0o644) // want `precondition of WriteFile may not hold: 4 \* \|name\| \+ 65536 <= MaxAlloc`
}

// Home returns $HOME, or a default.
//
// @Ensures |dir| > 0
func Home() (dir string) {
	if home, ok := os.LookupEnv("HOME"); ok && home != "" {
		return home
	}
	return "/"
}

// Level reads a setting of the environment.
//
// @Ensures True
func Level() (level string) {
	return os.Getenv("LEVEL")
}

// Here wraps the error of Getwd.
//
// @Ensures True
func Here() (dir string, err error) {
	dir, err = os.Getwd()
	if err != nil {
		return "", fmt.Errorf("getwd: %w", err)
	}
	return dir, nil
}

// Warn writes a warning to standard error.
//
// @Requires |msg| <= 1000
// @Ensures True
func Warn(msg string) {
	fmt.Fprintln(os.Stderr, "warning:", msg)
}

// Shut closes a file it is handed without saying that it writes it.
//
// @Ensures True
func Shut(f *os.File) (err error) {
	return f.Close() // want `Close may modify f, which Shut may not modify; list it in a // @Modifies clause, as f$`
}

// ShutListed says so.
//
// @Modifies f
// @Ensures True
func ShutListed(f *os.File) (err error) {
	return f.Close()
}
