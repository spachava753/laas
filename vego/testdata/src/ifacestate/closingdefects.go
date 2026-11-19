package ifacestate

import "io"

// Twice closes twice.
//
// @Requires c != nil And ~closed(c)
// @Modifies c
// @Ensures True
func Twice(c io.Closer) {
	c.Close()
	c.Close() // want `precondition of c.Close may not hold: ~closed\(c\)`
}

// Unrequired closes a value that may have been closed.
//
// @Requires c != nil
// @Modifies c
// @Ensures True
func Unrequired(c io.Closer) {
	c.Close() // want `precondition of c.Close may not hold: ~closed\(c\)`
}

// Unlisted closes a value without saying so.
//
// @Requires c != nil And ~closed(c)
// @Ensures True
func Unlisted(c io.Closer) {
	c.Close() // want `c.Close may modify the states of c, which Unlisted may not modify; list it in a // @Modifies clause`
}

// ThroughConversion closes through one interface and again through the other.
//
// @Requires rc != nil And ~closed(rc)
// @Modifies rc
// @Ensures True
func ThroughConversion(rc io.ReadCloser) {
	var c io.Closer = rc
	c.Close()
	rc.Close() // want `precondition of rc.Close may not hold: ~closed\(c\)`
}

// Elements closes two elements, which may hold one value.
//
// @Requires |rs| = 2 And rs[0] != nil And rs[1] != nil And ~closed(rs[0]) And ~closed(rs[1])
// @Modifies rs[0], rs[1]
// @Ensures True
func Elements(rs []io.Closer) {
	rs[0].Close()
	rs[1].Close() // want `precondition of rs\[1\].Close may not hold: ~closed\(c\)`
}

// FieldAndParam closes a parameter and then a body that may be the same.
//
// @Requires resp != nil And resp.Body != nil And c != nil And ~closed(resp.Body) And ~closed(c)
// @Modifies resp.Body, c
// @Ensures True
func FieldAndParam(resp *Response, c io.Closer) {
	c.Close()
	resp.Body.Close() // want `precondition of resp.Body.Close may not hold: ~closed\(c\)`
}

// CallsBothShared hands a value and a body that may be the same value.
//
// @Requires resp != nil And resp.Body != nil And c != nil And ~closed(resp.Body) And ~closed(c)
// @Modifies resp.Body, c
// @Ensures True
func CallsBothShared(resp *Response, c io.Closer) {
	Both(c, resp.Body) // want `the interface values passed to Both as a and b may share their states`
}

// WrongEnsures says the value is open on return.
//
// @Requires c != nil And ~closed(c)
// @Modifies c
// @Ensures ~closed(c')
func WrongEnsures(c io.Closer) {
	c.Close()
} // want `postcondition may not hold: ~closed\(c'\)`

// Reassign assigns the body under an entry for its states.
//
// @Requires resp != nil
// @Modifies resp.Body
// @Ensures True
func Reassign(resp *Response, rc io.ReadCloser) {
	resp.Body = rc // want `resp.Body is assigned, which Reassign may not modify: // @Modifies resp.Body covers the states of what the interface value resp.Body holds, not the place that holds it; to assign it, list the struct that holds it`
}

// NoStates lists a writer, which has no states.
//
// @Requires w != nil
// @Modifies w // want `in Modifies annotation: w has type io.Writer, which has no states`
// @Ensures True
func NoStates(w io.Writer) {
}

// CallsBothSame hands one value twice, which Both may not be given.
//
// @Requires rc != nil And ~closed(rc)
// @Modifies rc
// @Ensures True
func CallsBothSame(rc io.ReadCloser) {
	var c io.Closer = rc
	CloseOne(c, rc) // want `the interface values passed to CloseOne as a and b may share their states`
}

// NilBoth passes two nil values, which share a home and are not reported
// as sharing their states.
//
// @Ensures True
func NilBoth() {
	CloseOne(nil, nil) // want `precondition of CloseOne may not hold: a != nil`
}

// LoopTwice closes in a loop more than once.
//
// @Requires c != nil And ~closed(c)
// @Modifies c
// @Ensures True
func LoopTwice(c io.Closer, n int) {
	// @Variant n - i
	for i := 0; i < n; i++ {
		c.Close() // want `precondition of c.Close may not hold: ~closed\(c\)`
	}
}

// file stands for a closer of the project.
type file struct{}

// @Ensures err = nil
func (file) Close() (err error) {
	return nil
}

// Make converts a closer of its own to io.Closer.
//
// @Ensures True
func Make() (c io.Closer) {
	return file{} // want `cannot verify Make: converting a value of type file to io.Closer is not supported yet: io.Closer has the states closed, and the contract of Closer.Close speaks of them`
}

// Fresh says a parameter is new.
//
// @Requires c != nil
// @Ensures fresh(c) // want `fresh\(c\): c was passed in, so the call did not create it`
func Fresh(c io.Closer) {
}

// Unknown names a state that io.Closer does not have.
//
// @Requires c != nil And ~held(c) // want `held\(c\): c has type io.Closer, which has the states closed`
// @Ensures True
func Unknown(c io.Closer) {
}
