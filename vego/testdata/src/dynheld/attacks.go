package dynheld

import (
	"bytes"
	"io"
	"os"
	"sync"
)

// What is refused or not proved, and the cases the design names (S1 of
// F34).

// The one-result form panics when the value holds another type.
//
// @Ensures True
func MustInt(v any) (n int) {
	return v.(int) // want `the type assertion v.\(int\) may panic: v may not hold an int; use the form v, ok := v.\(int\), or show that it holds one, as a contract does with holds\(x, T\)`
}

// A contract that says too much of what a value holds.
//
// @Ensures holds(v, int) -> n = 1
func Claims(v any) (n int) {
	if x, ok := v.(int); ok {
		return x // want `postcondition may not hold: holds\(v, int\) -> n = 1`
	}
	return 0
}

// Two named types with one underlying type are two types, and an alias
// is the type it stands for.
type A int
type B int
type AA = A

// @Ensures ~ok
func NamedApart() (ok bool) {
	var v any = A(1)
	_, ok = v.(B)
	return ok
}

// @Ensures ok And n = 1
func AliasSame() (n A, ok bool) {
	var v any = A(1)
	n, ok = v.(AA)
	return n, ok
}

// @Ensures ok
func NamedWrong() (ok bool) {
	var v any = A(1)
	_, ok = v.(B)
	return ok // want `postcondition may not hold: ok`
}

// A type declared inside a function has no tag.
//
// @Ensures True
func LocalType(v any) (ok bool) {
	type L int
	_, ok = v.(L) // want `cannot verify LocalType: asserting an interface value to L is not supported: it is declared inside a function`
	return ok
}

// A generic instantiation is a type of its own.
type Box[T any] struct{ V T }

// @Ensures ~ok
func Instances() (ok bool) {
	var v any = Box[int]{V: 1}
	_, ok = v.(Box[string])
	return ok
}

// A pointer taken out writes memory the function must list.
//
// @Requires holds(v, *Point) And v.(*Point) != nil
// @Ensures True
func WriteThrough(v any) {
	p := v.(*Point)
	p.X = 1 // want `p.X is assigned, which WriteThrough may not modify`
}

// What a value taken out reaches is not known apart from what the other
// parameters reach (F5 of the design review).
//
// @Requires w != nil
// @Modifies w
// @Ensures r = 0
func Grew(w io.Writer, a any) (r int) {
	b, ok := a.(*bytes.Buffer)
	if !ok || b == nil {
		return 0
	}
	n := b.Len()
	w.Write([]byte("x"))
	return b.Len() - n // want `postcondition may not hold: r = 0`
}

// The states of a file taken out of an interface value are those of the
// interface value (F11 of the design review).
//
// @Requires c != nil And ~closed(c)
// @Modifies c
// @Ensures True
func Twice(c io.Closer) (err error) {
	if f, ok := c.(*os.File); ok && f != nil {
		f.Close() // want `Close may modify f, which Twice may not modify`
	}
	return c.Close() // want `precondition of c.Close may not hold: ~closed\(c\)`
}

// The same through an any that shares the reference of c.
//
// @Requires c != nil And ~closed(c)
// @Modifies c
// @Ensures True
func TwiceThroughAny(c io.Closer) (err error) {
	var a any = c
	if f, ok := a.(*os.File); ok && f != nil {
		f.Close() // want `Close may modify f, which TwiceThroughAny may not modify`
	}
	return c.Close() // want `precondition of c.Close may not hold: ~closed\(c\)`
}

// A value with a contract cannot be taken out of an any, which code that
// is not verified may have filled (R1).

// Logged holds a writer.
type Logged struct{ w io.Writer }

// @Ensures True
func TakesLogged(v any) (ok bool) {
	l, ok := v.(Logged) // want `cannot verify TakesLogged: asserting an interface value to Logged is not supported: it holds in field w a value of type io.Writer, whose method Write has a contract`
	_ = l
	return ok
}

// @Ensures True
func IsLogged(v any) (ok bool) {
	_, ok = v.(Logged)
	return ok
}

// A value that holds a state is not copied out.

// Locked holds a mutex.
type Locked struct {
	mu sync.Mutex
	n  int
}

// @Ensures True
func CopiesLocked(v any) (n int) {
	if l, ok := v.(Locked); ok { // want `the type assertion v.\(Locked\) copies what v holds, a value of type Locked, which holds a sync.Mutex; hold a pointer to it in the interface value instead`
		return l.n
	}
	return 0
}

// @Ensures True
func CopiesLockedCase(v any) (n int) {
	switch l := v.(type) {
	case Locked: // want `the case Locked of the type switch copies what the operand holds, a value of type Locked, which holds a sync.Mutex; hold a pointer to it in the interface value instead`
		return l.n
	}
	return 0
}

// A field rewritten after it was read, and claims about the wrong field
// or element (F14 of the review of S1).
//
// @Ensures n = 2
func Rewritten() (n int) {
	e := &Event{}
	e.Payload = any(1)
	old := e.Payload
	e.Payload = any(2)
	return old.(int) // want `postcondition may not hold: n = 2`
}

// @Ensures n = 1
func RewrittenHonest() (n int) {
	e := &Event{}
	e.Payload = any(1)
	old := e.Payload
	e.Payload = any(2)
	return old.(int)
}

// @Requires |xs| > 1 And holds(xs[1], int)
// @Ensures n = xs[0].(int)
func WrongElement(xs []any) (n int) {
	if m, ok := xs[0].(int); ok {
		return m
	}
	return 0 // want `postcondition may not hold: n = xs\[0\].\(int\)`
}

// @Requires |xs| > 0
// @Ensures True
func Undescribed(xs []any) (n int) {
	return xs[0].(int) // want `the type assertion xs\[0\].\(int\) may panic: xs\[0\] may not hold an int`
}

// @Requires e != nil And holds(e.Payload, string)
// @Ensures True
func WrongField(e *Event) (n int) {
	return e.Payload.(int) // want `the type assertion e.Payload.\(int\) may panic: e.Payload may not hold an int`
}

// A slice of the wrong element type.
//
// @Ensures holds(v, []byte) -> n = 0
func WrongSlice(v any) (n int) {
	if b, ok := v.([]byte); ok {
		return len(b) // want `postcondition may not hold: holds\(v, \[\]byte\) -> n = 0`
	}
	return 0
}
