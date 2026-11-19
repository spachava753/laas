// Package interfacesinitok asserts at package level that its types
// implement an interface. The conversion runs no code and hands nothing to
// another package, so ErrX keeps its value for every function.
package interfacesinitok

import (
	"errors"
	"fmt"
)

// Namer names things.
type Namer interface {
	// @Ensures True
	Name() (s string)
}

type Level int

// @Ensures True
func (Level) Name() (s string) { return "level" }

func (Level) String() string { return "level" }

type Box struct{}

// @Ensures True
func (*Box) Name() (s string) { return "box" }

var _ Namer = Level(0)
var _ Namer = (*Box)(nil)
var _ fmt.Stringer = Level(0)

var ErrX = errors.New("x")

// @Ensures n = 1
func Known() (n int) {
	if ErrX != nil {
		return 1
	}
	return 0
}
