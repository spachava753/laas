package typederrors

// FErr is a float error: == on floats is not identity, since NaN differs
// from itself.
type FErr float64

// @Ensures True
func (e FErr) Error() (s string) { return "f" }

// Empty has size zero, so two pointers to two of its values may or may not
// be equal (F1 of the design review).
type Empty struct{}

// @Ensures True
func (e *Empty) Error() (s string) { return "empty" }

// ErrEmpty holds a pointer to a value of size zero, so comparing it with
// an error is not identity: the narrowing of F1 for opaque variables.
var ErrEmpty error = &Empty{}

// @Ensures True
func Floats(x float64) (r bool) {
	var a error = FErr(x)
	var b error = FErr(x)
	return a == b // want `comparing two errors can panic`
}

// @Ensures True
func ZeroSize() (r bool) {
	var a, b error = &Empty{}, &Empty{}
	return a == b // want `comparing two errors can panic`
}

// @Ensures True
func ZeroSizeVariable(err error) (r bool) {
	return err == ErrEmpty // want `comparing two errors can panic`
}

// @Ensures True
func Unknown(a, b error) (r bool) {
	return a == b // want `comparing two errors can panic`
}
