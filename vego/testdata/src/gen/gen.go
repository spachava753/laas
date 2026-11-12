// Package gen calls a method of whatever type it is instantiated with.
package gen

// Call runs the Ready method of the zero value of T.
func Call[T interface{ Ready() bool }]() bool {
	var t T
	return t.Ready()
}

// Checker is something Run can ask.
type Checker interface{ Check() bool }

// Box holds a Checker for Run.
var Box struct{ Value Checker }

// GetBox returns what Box holds.
func GetBox() Checker { return Box.Value }

// Run asks a Checker.
func Run(c Checker) bool { return c != nil && c.Check() }
