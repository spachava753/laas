// Package ifacestatelib stands for a package of another module: its own
// go.mod puts it in a module of its own. The trust file of the tests gives
// its interfaces states and contracts.
package ifacestatelib

import "io"

// Response holds a body.
type Response struct {
	Status int
	Body   io.ReadCloser
}

// Fetch returns a response whose body is new and open.
func Fetch(url string) (resp *Response, err error) { return nil, nil }

// Stale returns a response whose body the entry says nothing new of.
func Stale(url string) (resp *Response, err error) { return nil, nil }

// Conn is a connection with a protocol.
type Conn interface {
	Start() error
	Finish() error
	Abort()
}

// Wrapped is a connection with a method of its own.
type Wrapped interface {
	Conn
	Ping()
}

// Alias is another name for Conn, which declares nothing.
type Alias interface{ Conn }

// Consume may close what it reads through an assertion.
func Consume(r io.Reader) {}
