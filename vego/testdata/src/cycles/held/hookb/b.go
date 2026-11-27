// Package hookb keeps a hook in a package-level variable and runs it
// later (m2 of the review of the design of F43). Fire is verified and is
// handed nothing that holds code.
package hookb

// Hook runs.
//
// @Ensures True
type Hook func() (n int)

var cur Hook

// Register keeps h.
//
// @Modifies cur
// @Ensures True
func Register(h Hook) {
	cur = h
}

// Fire runs what was registered.
//
// @Ensures True
func Fire(k int) (n int) {
	if cur != nil {
		return cur()
	}
	return 0
}
