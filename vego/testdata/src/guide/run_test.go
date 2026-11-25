package guide

import "testing"

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

// TestShutThenClose shows that the entry of shutWriter is false:
// ShutThenClose, proved under it, closes its writer twice.
func TestShutThenClose(t *testing.T) {
	defer func() {
		if recover() == nil {
			t.Fatal("ShutThenClose closed its writer once")
		}
	}()
	ShutThenClose(&closesOnce{})
}
