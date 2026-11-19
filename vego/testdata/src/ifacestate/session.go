package ifacestate

import "io"

// Session is a transaction, whose protocol its state open says.
//
// @State open
type Session interface {
	io.Closer

	// Begin opens the session.
	//
	// @Receiver s
	// @Requires ~open(s) And ~closed(s)
	// @Modifies s
	// @Ensures (err = nil <-> open(s')) And ~closed(s')
	Begin() (err error)

	// Commit ends it.
	//
	// @Receiver s
	// @Requires open(s)
	// @Modifies s
	// @Ensures ~open(s') And ~closed(s')
	Commit() (err error)

	// Rows counts what the session holds, and keeps every state.
	//
	// @Ensures n >= 0
	Rows() (n int)
}

// Transact runs the protocol.
//
// @Requires s != nil And ~open(s) And ~closed(s)
// @Modifies s
// @Ensures err = nil -> ~open(s')
func Transact(s Session) (err error) {
	if err := s.Begin(); err != nil {
		return err
	}
	if s.Rows() > 1000 {
		s.Commit()
		return nil
	}
	return s.Commit()
}

// CloseEnds closes after committing; Close may change open too.
//
// @Requires s != nil And open(s) And ~closed(s)
// @Modifies s
// @Ensures closed(s')
func CloseEnds(s Session) {
	s.Commit()
	s.Close()
}

// AfterClose commits after closing, which Close may have ended.
//
// @Requires s != nil And open(s) And ~closed(s)
// @Modifies s
// @Ensures True
func AfterClose(s Session) {
	s.Close()
	s.Commit() // want `precondition of s.Commit may not hold: open\(s\)`
}

// CommitUnopened commits a session that Begin may not have opened.
//
// @Requires s != nil And ~open(s) And ~closed(s)
// @Modifies s
// @Ensures True
func CommitUnopened(s Session) {
	s.Begin()
	s.Commit() // want `precondition of s.Commit may not hold: open\(s\)`
}

// AsCloser closes a session through io.Closer.
//
// @Requires s != nil And ~closed(s)
// @Modifies s
// @Ensures closed(s')
func AsCloser(s Session) {
	var c io.Closer = s
	c.Close()
}

// Stated has states of its own and gets closed from io.Closer.
//
// @Requires s != nil
// @Ensures True
func Stated(s Session) (b bool) {
	return true
}

// Succeeds says when it succeeds by the states of its argument, which a
// sample of an input gives values of their own.
//
// @Requires s != nil
// @Ensures (~closed(s) And open(s)) -> err = nil
func Succeeds(s Session) (err error) {
	return nil
}

// Never says it succeeds only for a state no value has.
//
// @Requires s != nil
// @Ensures (~closed(s) And closed(s)) -> err = nil
func Never(s Session) (err error) { // want `the contract of Never may also be met by a function that always returns an error`
	return nil
}
