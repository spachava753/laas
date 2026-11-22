package guide

import "io"

// Recorder keeps the lines it is given in memory of its own.
type Recorder interface {
	// Record adds a line.
	//
	// @Receiver r
	// @Requires |line| <= 100
	// @Modifies r
	// @Ensures True
	Record(line string)
}

// Lines counts what was logged.
type Lines struct {
	Total int
}

// @Requires r != nil And t != nil And 0 <= t.Total < 1000 And |line| <= 100
// @Modifies r, t
// @Ensures t.Total' = t.Total + 1
func Log(r Recorder, t *Lines, line string) {
	r.Record(line)
	t.Total++
}

// @Requires r != nil
// @Ensures True
func Forgot(r Recorder) {
	r.Record("start") // want `r.Record may modify the footprint of r, which Forgot may not modify; list it in a // @Modifies clause`
}

// @Requires r != nil And t != nil And 0 <= t.Total < 1000
// @Modifies r, t
// @Ensures True
func Start(r Recorder, t *Lines) {
	Log(r, t, "start")
}

// @Requires r != nil
// @Modifies r
// @Ensures True
func Note(r Recorder, t *Lines) {
	r.Record("note")
}

// LineCounts hands out a count it holds.
type LineCounts interface {
	// @Ensures t != nil
	Current() (t *Lines)
}

// @Requires r != nil And s != nil
// @Modifies r
// @Ensures True
func NoteFrom(r Recorder, s LineCounts) {
	Note(r, s.Current()) // want `the footprint of what is passed to Note as r may hold memory that what is passed as s.Current\(\) reaches, and Note relies on it not doing so: it comes from the call of s.Current at footprints.go:\d+:\d+, whose contract does not say that it is new or lies within an argument`
}

// @Requires r != nil And c != nil And ~closed(c)
// @Modifies r, c
// @Ensures True
func RecordThenClose(r Recorder, c io.Closer) {
	r.Record("done")
	c.Close() // want `precondition of c.Close may not hold: ~closed\(c\)`
}

// Recorders makes recorders whose footprints are new.
type Recorders interface {
	// @Ensures r != nil And fresh(r)
	New() (r Recorder)
}

// @Requires f != nil And t != nil
// @Ensures t.Total' = t.Total
func LogToNew(f Recorders, t *Lines) {
	r := f.New()
	r.Record("start")
}

// teeRecorder makes a recorder that records into r and memory of its own.
func teeRecorder(r Recorder) (s Recorder) { return r }

// @Requires r != nil
// @Modifies r
// @Ensures True
func LogThroughTee(r Recorder) {
	s := teeRecorder(r)
	s.Record("tee")
}

// @Requires r != nil
// @Ensures True
func LogThroughTeeUnlisted(r Recorder) {
	s := teeRecorder(r)
	s.Record("tee") // want `vego: s.Record may modify the footprint of s, which LogThroughTeeUnlisted may not modify; list it in a // @Modifies clause`
}
