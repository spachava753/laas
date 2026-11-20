// Package trackquiet calls a trusted function whose contract never says
// that it succeeds only from a function that returns no error.
package trackquiet

// parse is trusted; see the trust file of the tests.
func parse(s string) (v int, err error) { return len(s), nil }

// Length drops the error of parse.
//
// @Ensures True
func Length(s string) (n int) {
	v, err := parse(s)
	if err != nil {
		return 0
	}
	return v
}
