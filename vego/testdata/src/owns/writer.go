package owns

import "io"

// Remembers writes by keeping the slice it is handed, which no
// implementation of io.Writer may do.
type Remembers struct {
	last []byte
}

// Write keeps p.
//
// @Requires r != nil
// @Modifies r
// @Ensures n = |p| And err = nil
func (r *Remembers) Write(p []byte) (n int, err error) {
	r.last = p
	return len(p), nil
}

// Copies writes by recording how much it was handed.
type Copies struct {
	last int
}

// Write records the length.
//
// @Requires c != nil
// @Modifies c
// @Ensures n = |p| And err = nil
func (c *Copies) Write(p []byte) (n int, err error) {
	c.last = len(p)
	return len(p), nil
}

// AsWriters converts both to io.Writer.
//
// @Ensures True
func AsWriters() {
	var w io.Writer = &Remembers{} // want `vego: \(\*Remembers\).Write keeps p, which an implementation of a method of io.Writer may not, since its entry lists no keeps; copy what it needs of p`
	_ = w
	var c io.Writer = &Copies{}
	_ = c
}
