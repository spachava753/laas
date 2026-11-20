// Package trackfail calls a trusted function whose contract never says
// that it succeeds, from a function that returns an error and from one
// that does not.
package trackfail

// parse is trusted; see the trust file of the tests.
func parse(s string) (v int, err error) { return len(s), nil }

// Passes returns what parse returns.
//
// @Ensures True
func Passes(s string) (v int, err error) {
	return parse(s)
}

// Ignores drops the error of parse.
//
// @Ensures True
func Ignores(s string) (n int) {
	v, err := parse(s)
	if err != nil {
		return 0
	}
	return v
}
