package guideclaims

import (
	"testing"

	"guide"
)

// closesOnce panics on a second Close.
type closesOnce struct{ closed bool }

func (c *closesOnce) Write(p []byte) (int, error) { return len(p), nil }

func (c *closesOnce) Close() error {
	if c.closed {
		panic("closed twice")
	}
	c.closed = true
	return nil
}

// TestShutThenClose shows that the entry of shutWriter in the corpus trust
// file is false: guide.ShutThenClose, proved under it, closes its writer
// twice.
func TestShutThenClose(t *testing.T) {
	defer func() {
		if recover() == nil {
			t.Fatal("ShutThenClose closed its writer once")
		}
	}()
	guide.ShutThenClose(&closesOnce{})
}
