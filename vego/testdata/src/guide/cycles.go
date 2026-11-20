package guide

// The programs of Calls that go round through a value, in Recursion.

// Source reads a number.
type Source interface {
	// @Ensures n >= 0
	Next() (n int)
}

// Retry calls back into Pull through a Source it holds.
type Retry struct{ src Source }

// @Requires r != nil
// @Variant 1
// @Ensures n >= 0
func (r *Retry) Next() (n int) {
	if r.src == nil {
		return 0
	}
	return Pull(r.src) // want `this call may not end: \(\*Retry\).Next calls Pull at cycles.go:\d+:\d+, Pull calls s.Next\(\) at cycles.go:\d+:\d+, which may run \(\*Retry\).Next; a cycle that goes through a call with no static callee`
}

// @Requires s != nil
// @Variant 0
// @Ensures n >= 0
func Pull(s Source) (n int) {
	return s.Next() // want `this call may not end: Pull calls s.Next\(\) at cycles.go:\d+:\d+, which may run \(\*Retry\).Next, \(\*Retry\).Next calls Pull at cycles.go:\d+:\d+; a cycle that goes through a call with no static callee`
}

// Stepper has a Next of another signature, which a call of Source.Next
// cannot reach.
type Stepper struct{}

// @Ensures True
func (Stepper) Next(step int) (n int) {
	return Pulled(nil)
}

// @Ensures n >= 0
func Pulled(s Source) (n int) {
	if s == nil {
		return 0
	}
	return s.Next()
}
