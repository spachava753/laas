package rewindsplain

import "rewindlib"

// Back rewinds through a Rewinder, whose entry says that Rewind rewinds.
//
// @Requires s != nil
// @Modifies s
// @Ensures True
func Back(s rewindlib.Rewinder) {
	s.Rewind()
}

// Later defers the same call.
//
// @Requires s != nil
// @Modifies s
// @Ensures True
func Later(s rewindlib.Rewinder) {
	defer s.Rewind()
}

// Direct calls the method of File, whose entry says that it rewinds.
//
// @Requires f != nil
// @Modifies f
// @Ensures True
func Direct(f *rewindlib.File) {
	f.Rewind()
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
	return rewindlib.Restart
}

// Handed hands a method value of the method of File to each, which calls
// it under calls.
//
// @Requires f != nil
// @Modifies f
// @Ensures True
func Handed(f *rewindlib.File) {
	each(f.Rewind)
}

func each(g func()) { g() }

// AsRewinder converts a File to a Rewinder, which checks the entry of
// File's method against the entry of Rewinder's.
//
// @Requires f != nil
// @Ensures True
func AsRewinder(f *rewindlib.File) (s rewindlib.Rewinder) {
	return f
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
	return r
}
