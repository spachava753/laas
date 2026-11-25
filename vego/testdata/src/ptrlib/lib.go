// Package ptrlib stands for a library whose connection's Close, trusted by
// an entry, closes the file the connection holds in an exported field.
package ptrlib

import "os"

// Conn holds a file.
type Conn struct{ FD *os.File }

// Close closes the file.
func (c *Conn) Close() error { return c.FD.Close() }

// Quiet is a connection whose Close, trusted by an entry that lists nothing,
// closes nothing the entry admits to.
type Quiet struct{ FD *os.File }

// Close closes the file.
func (c *Quiet) Close() error { return c.FD.Close() }
