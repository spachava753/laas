// Package libr holds a Shower whose Show calls a method of what it holds
// by reflection.
package libr

import "reflect"

// Shower shows.
type Shower interface {
	// @Ensures True
	Show()
}

// Reflected is not verified.
type Reflected struct{ V any }

func (r Reflected) Show() {
	if m := reflect.ValueOf(r.V).MethodByName("String"); m.IsValid() {
		m.Call(nil)
	}
}

// Mark is verified, so that the package publishes what its functions run.
//
// @Ensures True
func Mark() {}
