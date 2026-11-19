// Package statelib stands for a package of another module, whose
// interface two modules built together declare different states for.
package statelib

// Conn is a connection.
type Conn interface {
	Start() error
	Stop()
}
