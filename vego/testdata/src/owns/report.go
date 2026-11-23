package owns

import (
	"fmt"
	"io"
	"os"
)

// Report owns the writer it writes to, so a write through it keeps the
// count beside it and what the other parameters reach (F27, step 3b).
//
// @Owns out
type Report struct {
	out   io.Writer
	lines int
}

// NewReport makes a report over standard output.
//
// @Ensures r != nil And r.lines = 0
func NewReport() (r *Report) {
	return &Report{out: os.Stdout}
}

// Line writes p and counts it.
//
// @Requires r != nil And r.out != nil And r.lines < 1000000
// @Modifies r
// @Ensures err = nil -> r.lines' = r.lines + 1
func (r *Report) Line(p []byte) (err error) {
	_, err = r.out.Write(p)
	if err == nil {
		r.lines++
	}
	return err
}

// KeepsBeside writes through the report and keeps what data holds.
//
// @Requires r != nil And r.out != nil And r.lines < 1000000 And |data| > 0
// @Modifies r
// @Ensures data'[0] = data[0]
func KeepsBeside(r *Report, data []byte) {
	r.Line(data)
}

// Adopt makes a report own a writer it is handed, which it did not own
// (F9 (d) of the design review, not built).
//
// @Requires r != nil
// @Modifies r
// @Ensures True
func Adopt(r *Report, w io.Writer) {
	r.out = w // want `vego: r.out may come to refer to memory that existed when Adopt was called and that it did not own`
}

// Forward hands the writer a report owns to a function that formats into
// it and keeps nothing of it.
//
// @Requires r != nil And r.out != nil
// @Modifies r
// @Ensures True
func Forward(r *Report) (err error) {
	_, err = fmt.Fprint(r.out, "x")
	return err
}

// Reopen gives the report a new writer.
//
// @Requires r != nil
// @Modifies r
// @Ensures True
func (r *Report) Reopen() {
	r.out = os.Stderr
}

// Reopened claims the writer is the same after Reopen, which it is not:
// what an owned interface field holds may change to a new value.
//
// @Requires r != nil
// @Modifies r
// @Ensures r.out' = r.out
func Reopened(r *Report) {
	r.Reopen()
} // want `vego: postcondition may not hold: r.out' = r.out`

// sink writes nothing anywhere.
type sink struct {
	n int
}

// Write records the length.
//
// @Requires s != nil
// @Modifies s
// @Ensures n = |p| And err = nil
func (s *sink) Write(p []byte) (n int, err error) {
	s.n = len(p)
	return len(p), nil
}

// HeldWriter makes a writer in a variable and gives it to a report (F34
// of the review of step 3b).
//
// @Ensures r != nil
func HeldWriter() (r *Report) {
	w := io.Writer(&sink{})
	return &Report{out: w}
}

// HeldPointer converts a new sink held in a variable where it is stored.
//
// @Ensures r != nil
func HeldPointer() (r *Report) {
	s := &sink{}
	return &Report{out: s}
}
