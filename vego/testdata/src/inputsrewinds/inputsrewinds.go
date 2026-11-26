package inputsrewinds

import "rewindlib"

// Back rewinds through a Rewinder, whose entry says that Rewind rewinds.
//
// @Requires s != nil
// @Modifies s
// @Ensures True
func Back(s rewindlib.Rewinder) {
	s.Rewind() // want `the trusted contract of \(rewindlib.Rewinder\).Rewind .*cannot be used: it may make a reader yield again what it already yielded, through s, as its rewinds says`
}

// Later defers the same call.
//
// @Requires s != nil
// @Modifies s
// @Ensures True
func Later(s rewindlib.Rewinder) {
	defer s.Rewind() // want `the trusted contract of \(rewindlib.Rewinder\).Rewind .*cannot be used: it may make a reader yield again`
}

// Direct calls the method of File, whose entry says that it rewinds.
//
// @Requires f != nil
// @Modifies f
// @Ensures True
func Direct(f *rewindlib.File) {
	f.Rewind() // want `the trusted contract of \(\*rewindlib.File\).Rewind .*cannot be used: it may make a reader yield again what it already yielded, through f`
}

// Action is something done to a File.
//
// @Requires f != nil
// @Modifies f
// @Ensures True
type Action func(f *rewindlib.File)

// Value makes a function value of Restart, whose entry says that it
// rewinds.
//
// @Ensures True
func Value() (a Action) {
	return rewindlib.Restart // want `Restart .*it may make a reader yield again`
}

// Handed hands a method value of the method of File to each, which calls
// it under calls.
//
// @Requires f != nil
// @Modifies f
// @Ensures True
func Handed(f *rewindlib.File) {
	each(f.Rewind) // want `Rewind .*it may make a reader yield again`
}

func each(g func()) { g() }

// AsRewinder converts a File to a Rewinder, which checks the entry of
// File's method against the entry of Rewinder's.
//
// @Requires f != nil
// @Ensures True
func AsRewinder(f *rewindlib.File) (s rewindlib.Rewinder) {
	return f // want `Rewind .*it may make a reader yield again` `Rewind .*it may make a reader yield again`
}

// AsResetter converts a Rewinder to a Resetter, by contract: Resetter's
// entry says Rewind does not rewind, so it is refused either way.
//
// @Requires s != nil
// @Ensures True
func AsResetter(s rewindlib.Rewinder) (r rewindlib.Resetter) {
	return s // want `converting s, a rewindlib.Rewinder, to rewindlib.Resetter is not supported: Rewinder.Rewind may make a reader yield again what it already yielded, through its receiver, as its rewinds says, and Resetter.Rewind does not`
}

// FromResetter converts a Resetter to a Rewinder: Rewinder's entry says
// that Rewind may rewind, which claims less.
//
// @Requires r != nil
// @Ensures True
func FromResetter(r rewindlib.Resetter) (s rewindlib.Rewinder) {
	return r // want `Rewind .*it may make a reader yield again`
}

func misnamed(f *rewindlib.File) {}

// Misnamed calls a function whose rewinds names no parameter.
//
// @Requires f != nil
// @Modifies f
// @Ensures True
func Misnamed(f *rewindlib.File) {
	misnamed(f) // want `the trusted contract of inputsrewinds.misnamed .*cannot be used: its rewinds "q": q is not a parameter`
}
