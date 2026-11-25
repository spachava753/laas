// Package optionalc is another module with an interface of one method, to
// which the corpus trust file gives an entry, so that it is an interface
// of O.
package optionalc

// Sizer reports a size.
type Sizer interface {
	Size() (n int)
}

// Rec is a writer of another module; the corpus trust file gives its
// methods entries, of which WriteString requires its receiver not nil.
type Rec struct{ n int }

func (r *Rec) Write(p []byte) (int, error) {
	if r == nil {
		return 0, errNil
	}
	return len(p), nil
}

func (r *Rec) WriteString(s string) (int, error) {
	r.n++
	return len(s), nil
}

// Over is a writer of another module whose WriteString reports a byte too
// many, as its entry in the corpus trust file says.
type Over struct{}

func (Over) Write(p []byte) (int, error) { return len(p), nil }

func (Over) WriteString(s string) (int, error) { return len(s) + 1, nil }

type nilError struct{}

func (nilError) Error() string { return "nil Rec" }

var errNil error = nilError{}
