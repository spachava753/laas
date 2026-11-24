// Package closedq is not verified. Its functions take an address beside a
// value that can carry code, which their entries describe nothing of (F15
// of the review of step 3 of F32).
package closedq

// Show hands v to the Hold method of x, when x has one.
func Show(v any, x any) {
	if h, ok := x.(interface{ Hold(any) }); ok {
		h.Hold(v)
	}
}

// Shared is what Run hands on.
type Shared struct{ N int }

// Run hands v to the Take method of x, when x has one.
func Run(v *Shared, x any) {
	if t, ok := x.(interface{ Take(*Shared) }); ok {
		t.Take(v)
	}
}

// Poke writes to v, when it is a writer.
func Poke(v any) {
	if w, ok := v.(interface{ Write([]byte) (int, error) }); ok {
		_, _ = w.Write([]byte("x"))
	}
}
