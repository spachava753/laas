// Package slowhttp calls a trusted function that returns a *http.Response,
// the slowest case measured with speed: verifying Fetch took 101 s at
// 35dca07 and 79 s after it, almost all in Z3. Since its questions are
// solved without the axiom of extensionality it takes under a second, and
// the main corpus run keeps it there through the table of costs; see The
// prover in the ROADMAP.
package slowhttp

import "net/http"

// get is trusted; see the trust file of the tests.
func get(url string) (resp *http.Response, err error) { return http.Get(url) }

// Fetch returns the status of a response and closes its body.
//
// @Ensures True
func Fetch(url string) (code int, err error) {
	resp, err := get(url)
	if err != nil {
		return 0, err
	}
	defer resp.Body.Close()
	return resp.StatusCode, nil
}
