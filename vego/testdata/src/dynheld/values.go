package dynheld

// Values out of an any.

// @Ensures ok <-> v != nil And holds(v, int)
// @Ensures ok -> n = v.(int)
// @Ensures ~ok -> n = 0
func Int(v any) (n int, ok bool) {
	n, ok = v.(int)
	return n, ok
}

// Point is a struct held in an any.
type Point struct{ X, Y int }

// @Ensures holds(v, int) -> k = 1
// @Ensures holds(v, string) -> k = 2
// @Ensures holds(v, Point) -> k = 4
// @Ensures v = nil -> k = 0
func Classify(v any) (k int) {
	switch v.(type) {
	case int:
		return 1
	case string:
		return 2
	case []byte:
		return 3
	case Point:
		return 4
	case nil:
		return 0
	}
	return 5
}

// @Ensures holds(v, string) -> n = |v.(string)|
func Length(v any) (n int) {
	switch x := v.(type) {
	case string:
		return len(x)
	case []byte:
		return len(x)
	}
	return 0
}

// @Requires holds(v, Point)
// @Ensures s = v.(Point).X
func XOf(v any) (s int) {
	return v.(Point).X
}

// Two values in both orders.
//
// @Ensures k = 12
func TwoValues() (k int) {
	var a any = 7
	var b any = "seven"
	return Classify(a)*10 + Classify(b) - 1 + Length(b) - 4
}

// @Ensures k = 12
func TwoValuesSwapped() (k int) {
	var b any = "seven"
	var a any = 7
	n, ok := Int(a)
	m, no := Int(b)
	if !ok || no || m != 0 {
		return 0
	}
	return n + Length(b)
}

// @Ensures r = 5
func PointBack() (r int) {
	var v any = Point{X: 5, Y: 6}
	return XOf(v)
}

// A field of type any and an element of a []any.

// Event carries what happened.
type Event struct {
	Name    string
	Payload any
}

// @Requires e != nil And holds(e.Payload, int)
// @Ensures n = e.Payload.(int)
func Count(e *Event) (n int) {
	return e.Payload.(int)
}

// @Requires |xs| > 0 And (Forall i in [0, |xs|) : holds(xs[i], int))
// @Ensures n = xs[0].(int)
func First(xs []any) (n int) {
	return xs[0].(int)
}

// @Requires |xs| <= 100 And (Forall i in [0, |xs|) : holds(xs[i], int) And 0 <= xs[i].(int) <= 100)
// @Ensures 0 <= n
func Sum(xs []any) (n int) {
	// @Invariant 0 <= i <= |xs|
	// @Invariant 0 <= n <= 100 * i
	// @Variant |xs| - i
	for i := 0; i < len(xs); i++ {
		n += xs[i].(int)
	}
	return n
}

// @Ensures n = 3
func Counted() (n int) {
	e := &Event{Name: "a", Payload: 3}
	return Count(e)
}

// An error converted to any holds what the error holds.

// CodeErr is an error of the package.
type CodeErr struct{ Code int }

// @Ensures True
func (e *CodeErr) Error() (s string) { return "code" }

// @Requires holds(err, *CodeErr) And err.(*CodeErr) != nil
// @Ensures c = err.(*CodeErr).Code
func CodeThroughAny(err error) (c int) {
	var a any = err
	return a.(*CodeErr).Code
}

// @Ensures c = 7
func CodeMade() (c int) {
	var err error = &CodeErr{Code: 7}
	var a any = err
	if e, ok := a.(*CodeErr); ok && e != nil {
		return e.Code
	}
	return 0
}
