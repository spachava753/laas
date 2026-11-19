package interfaces

// @Ensures t != nil
func KeepsNil(s Shape) (t Shape) {
	return s // want `postcondition may not hold: t != nil`
}

// A nil pointer converted to an interface makes one that is not nil.
//
// @Ensures a = nil
func NilPointer() (a any) {
	a = (*Holder)(nil)
	return a // want `postcondition may not hold: a = nil`
}

// @Ensures a = nil
func ErrorIsNotNil(err error) (a any) {
	return err // want `postcondition may not hold: a = nil`
}

// @Ensures same
func Compared(s, t Shape) (same bool) {
	return s == t // want `cannot verify Compared: comparing interface values is not supported yet`
}

// @Ensures True
func ComparedWithValue(a any) (same bool) {
	return a == 3 // want `cannot verify ComparedWithValue: comparing interface values is not supported yet`
}

// @Ensures True
func SwitchedOn(a any, s Shape) (n int) {
	switch a {
	case s: // want `cannot verify SwitchedOn: comparing interface values is not supported yet`
		return 1
	}
	return 0
}

// @Ensures True
func Asserted(a any) (n int) {
	return a.(int) // want `cannot verify Asserted: type assertions and type switches are not supported yet`
}

// @Ensures True
func TypeSwitched(a any) (n int) {
	switch a.(type) { // want `cannot verify TypeSwitched: type assertions and type switches are not supported yet`
	case int:
		return 1
	}
	return 0
}

// @Ensures u = s // want `in Ensures annotation: an interface value can only be compared with nil`
func InFormula(s Shape) (u Shape) {
	return s
}

type Other interface {
	Area() (a int)
}

// @Ensures True
func OwnDeclaration(s Shape) (o Other) {
	return s // want `cannot verify OwnDeclaration: converting s, a interfaces.Shape, to interfaces.Other is not supported: interfaces.Other declares Area itself`
}

type Square struct{ side int }

func (q Square) Area() (a int) { return q.side * q.side }

// @Ensures True
func Concrete(q Square) (s Shape) {
	return q // want `cannot verify Concrete: converting a interfaces.Square to the interface interfaces.Shape is not supported yet`
}

type Stringish interface {
	String() (s string)
}

// @Ensures True
func ErrorToMethods(err error) (s interface{ Error() string }) {
	return err // want `cannot verify ErrorToMethods: converting an error to interface\{Error\(\) string\} is not supported; only any can hold an error`
}

type Coded interface {
	error
	Code() (c int)
}

// @Ensures True
func EmbedsError(c Coded) (n int) { // want `cannot verify EmbedsError: parameter c has unsupported type interfaces.Coded`
	return 0
}

func describe(s Shape) (n int) { return 0 }

func describeRuns(s Shape) (n int) { return 0 }

func loadShape() (s Shape) { return nil }

// @Ensures True
func Described(s Shape) (n int) {
	return describe(s) // want `cannot verify Described: s is passed to describe, which is trusted, and is a value of type interfaces.Shape, which can hold an error, an interface, or a function`
}

// @Ensures s = nil -> n = 0
func DescribedRuns(s Shape) (n int) {
	if s == nil {
		return 0
	}
	n = describeRuns(s)
	return n
}

// @Ensures s != nil
func Loaded() (s Shape) {
	return loadShape() // want `postcondition may not hold: s != nil`
}

// @Ensures True
type Report func(s Shape)

// @Requires r != nil
// @Ensures True
func Reported(r Report, s Shape) {
	r(s) // want `cannot verify Reported: s is passed to the function value r and is a value of type interfaces.Shape, which can hold an error, or another interface`
}

type Gen[T any] interface {
	Get() (t T)
}

// @Ensures True
func Generic(g Gen[int]) (n int) { // want `cannot verify Generic: parameter g has unsupported type interfaces.Gen\[int\]`
	return 0
}

// The search for an input on which the contract forces success offers a
// shape that is not nil.
//
// @Ensures err = nil <-> s != nil
func NeedsShape(s Shape) (err error) {
	if s == nil {
		return errNoShape
	}
	return nil
}
