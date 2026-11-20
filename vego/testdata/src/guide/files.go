package guide

import (
	"fmt"
	"io"
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

// WriteReport writes a line to a new file.
//
// @Requires |name| <= 4096 And |title| <= 1000
// @Ensures True
func WriteReport(name, title string) (err error) {
	f, err := os.Create(name)
	if err != nil {
		return fmt.Errorf("create %s: %w", name, err) // want `cannot verify WriteReport: formatting err would run the methods of an error whose origin is not known; only an error made by errors.New or fmt.Errorf, here or in a verified function, or one that a contract vouches for, can be formatted; err is also assigned fmt.Fprintln\(f, title\) at files.go:61:11, later, a call whose errors nothing vouches for, and an error variable has a known origin only when every assignment to it gives it one; give that a variable of its own`
	}
	_, err = fmt.Fprintln(f, title)
	f.Close()
	return err
}

// WriteReportApart gives the error of Create a variable of its own.
//
// @Requires |name| <= 4096 And |title| <= 1000
// @Ensures True
func WriteReportApart(name, title string) (err error) {
	f, cerr := os.Create(name)
	if cerr != nil {
		return fmt.Errorf("create %s: %w", name, cerr)
	}
	_, err = fmt.Fprintln(f, title)
	f.Close()
	return err
}
