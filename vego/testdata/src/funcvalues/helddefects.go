package funcvalues

// NotNil claims more than is known of a value that was passed in.
//
// @Ensures h != nil
func NotNil(f func(int) int) (h func(int) int) {
	return f // want `vego: postcondition may not hold: h != nil`
}

// ComparesTwo compares two function values in a formula, which Go does not
// allow in code either.
//
// @Ensures f = g // want `vego: in Ensures annotation: a function value can only be compared with nil`
func ComparesTwo(f, g func()) {
}

// AsCondition uses a function value as a formula.
//
// @Requires f // want `vego: in Requires annotation: .*`
func AsCondition(f func()) {
}

// Fresh asks whether a function value was created by the call.
//
// @Ensures fresh(h) // want `vego: in Ensures annotation: fresh\(h\): h is not a pointer, a slice, or a map`
func Fresh() (h func()) {
	return nil
}

// Within asks whether a function value lies inside a slice.
//
// @Requires within(f, A) // want `vego: in Requires annotation: within\(f\): f is not a pointer, a slice, or a map`
func Within(f func(), A []int) {
}

// Has asks a function value for a key.
//
// @Requires has(f, 1) // want `vego: in Requires annotation: has\(f, ...\): f is not a map`
func Has(f func()) {
}

// Calls a value of a type without a contract.
//
// @Ensures True
func Calls(f func(int) int) (n int) {
	return f(1) // want `vego: cannot verify Calls: .*`
}
