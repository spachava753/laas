// r33: a *bufio.Writer that holds a writer of the package, whose Write calls back.
package r33

import "bufio"

// W writes by calling F.
type W struct{ bw *bufio.Writer }

func (w W) Write(p []byte) (int, error) { F(w.bw); return len(p), nil }

// @Requires bw != nil And ready(bw)
// @Modifies bw
// @Ensures True
func F(bw *bufio.Writer) (err error) {
	return bw.Flush() // want `this\ call\ may\ not\ end:\ F\ hands\ bw\ to\ bw\.Flush\(\)\ at\ p\.go:\d+:\d+,\ which\ may\ run\ W\.Write,\ W\.Write\ calls\ F\ at\ p\.go:\d+:\d+`
}

// wire is not verified.
func wire() {
	var w W
	bw := bufio.NewWriter(&w)
	w.bw = bw
	bw.WriteString("x")
	F(bw)
}
