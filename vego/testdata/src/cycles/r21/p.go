// r21: precision. A method of the same name and another signature is no edge.
package r21

type Store interface {
	// @Ensures True
	Read() (n int)
}

// @Requires s != nil
// @Ensures True
func F(s Store) (n int) {
	return s.Read()
}

type T struct{}

func (T) Read(x int) int { return F(nil) }

func init() { var _ = F }
