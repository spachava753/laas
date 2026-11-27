package stops

import (
	"fmt"
	"reflect"
)

// Cycles of calls that no Variant can be checked across, each through an
// edge of another kind the call graph cannot follow (F28 of the review).

// Rec reaches Inspect, which hands it to reflect.ValueOf, which may run
// its exported methods: a call of another package.
type Rec struct{}

func (r *Rec) Visit() { Inspect(r) }

func Inspect(v any) { _ = reflect.ValueOf(v) }

// Item calls a function value it is handed with itself, and Show, used as
// such a value, calls Each: a call through a value.
type Item struct{}

func (i *Item) Each(cb func(v any)) { cb(i) }

func Show(v any) {
	if it, ok := v.(*Item); ok {
		it.Each(Show)
	}
}

// Sizer is an interface of the package that List implements by calling
// it: a call of an interface method.
type Sizer interface{ Size() int }

type List struct{ inner Sizer }

func (l *List) Size() int { return l.inner.Size() }

// Tree formats itself through errorf: formatting.
type Tree struct{ name string }

func errorf(format string, args ...any) string { return fmt.Sprintf(format, args...) }

func (t *Tree) String() string { return errorf("tree %v", t) }
