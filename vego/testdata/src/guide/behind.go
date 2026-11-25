package guide

import (
	"bufio"
	"io"
)

// The programs of the section "Functions that write through what they are
// handed".

// @Requires wc != nil And ~closed(wc)
// @Modifies wc
// @Ensures closed(wc')
func WriteThenClose(wc io.WriteCloser, s string) (err error) {
	_, _ = io.WriteString(wc, s)
	return wc.Close()
}

// @Requires wc != nil And ~closed(wc)
// @Modifies wc
// @Ensures True
func BufferThenClose(wc io.WriteCloser, s string) (err error) {
	bw := bufio.NewWriter(wc)
	_, _ = bw.WriteString(s)
	_ = bw.Flush()
	return wc.Close() // want `precondition of wc.Close may not hold: ~closed\(c\); the state may have been changed by WriteString at behind.go:\d+:\d+, which writes through what it is handed or what a value it is handed keeps, and nothing says that what it writes through is not this value, so its states count as those of another value, which a write may change; close or use the value only where nothing was written through what keeps it since its state was known, or write to the value itself`
}

// closeAll is trusted, and its entry is refused.
func closeAll(wc io.WriteCloser) { wc.Close() }

// @Requires wc != nil
// @Modifies wc
// @Ensures True
func CloseAll(wc io.WriteCloser) {
	closeAll(wc) // want `the trusted contract of guide.closeAll \(trusted.yaml:\d+\) cannot be used: in its modifies "behind\(wc\)": behind\(wc\) claims`
}

// shutWriter is trusted, under a false entry: it closes what it is handed,
// by an assertion its entry does not list, while its entry claims
// behind(w).
func shutWriter(w io.Writer) {
	if c, ok := w.(io.Closer); ok {
		c.Close()
	}
}

// ShutThenClose is proved under that entry, and it closes wc twice, as
// run_test.go shows.
//
// @Requires wc != nil And ~closed(wc)
// @Modifies wc
// @Ensures True
func ShutThenClose(wc io.WriteCloser) {
	shutWriter(wc)
	_ = wc.Close()
}
