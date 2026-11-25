// Package optionalsink is another module that imports nothing, so io is
// not in its build. The corpus trust file gives Sink.Write the entry of
// (io.Writer).Write, which makes Sink an interface of O whose O is itself.
package optionalsink

// Sink is written to.
type Sink interface {
	Write(p []byte) (n int, err error)
}
