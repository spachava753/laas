package guide

import (
	"fmt"
	"io"
	"log"
	"os"
)

// ReadConfig reads at most 4096 bytes of a file.
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

// LoadSettings reads a file of this program's own with os.ReadFile, under
// the entry of the trust file.
//
// @Requires |name| <= 4096
// @Ensures True
func LoadSettings(name string) (data []byte, err error) {
	data, err = os.ReadFile(name)
	if err != nil {
		return nil, fmt.Errorf("load %s: %w", name, err)
	}
	return data, nil
}

// WriteReport writes a line to a new file. Only os.Create reaches the %w.
//
// @Requires |name| <= 4096 And |title| <= 1000
// @Ensures True
func WriteReport(name, title string) (err error) {
	f, err := os.Create(name)
	if err != nil {
		return fmt.Errorf("create %s: %w", name, err)
	}
	_, err = fmt.Fprintln(f, title)
	f.Close()
	return err
}

// ReportOnce wraps the error of either call in one place, so the error of
// fmt.Fprintln reaches the %w.
//
// @Requires |name| <= 4096 And |title| <= 1000
// @Ensures True
func ReportOnce(name, title string) (err error) {
	f, err := os.Create(name)
	if err == nil {
		_, err = fmt.Fprintln(f, title)
		f.Close()
	}
	if err != nil {
		return fmt.Errorf("report %s: %w", name, err) // want `cannot verify ReportOnce: formatting err would run the methods of an error whose origin is not known; only an error made by errors.New or fmt.Errorf, here or in a verified function, or one that a contract vouches for, can be formatted; err may hold here the error assigned fmt.Fprintln\(f, title\) at files.go:75:12, a call whose errors nothing vouches for, on a path that reaches this use; give that error a variable of its own`
	}
	return nil
}

// LogToFile logs a line to a new file through a logger that writes to it.
//
// @Requires |name| <= 4096 And |line| <= 1000
// @Ensures True
func LogToFile(name, line string) (err error) {
	f, cerr := os.Create(name)
	if cerr != nil {
		return fmt.Errorf("create %s: %w", name, cerr)
	}
	l := log.New(f, "app: ", 0)
	l.Println(line)
	return f.Close()
}
