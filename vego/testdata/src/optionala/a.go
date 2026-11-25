// Package optionala imports nothing, so io is not in its build: its Sink is
// not O-typed, and a conversion to it is not checked against io.Writer
// (F1 of the design review of F35).
package optionala

// Sink is filled through Put, which writes behind its receiver.
type Sink interface {
	// @Receiver s
	// @Modifies s
	// @Ensures True
	Put()
}

// T counts, and has a Write of io.Writer's signature that returns -1.
type T struct{ N int }

// @Requires t != nil
// @Modifies t
// @Ensures True
func (t *T) Put() {
	if t.N < 100 {
		t.N++
	}
}

// @Requires t != nil
// @Ensures n = -1 And err = nil
func (t *T) Write(p []byte) (n int, err error) { return -1, nil }

// @Ensures s != nil And fresh(s)
func Make() (s Sink) {
	return &T{}
}
