// Package slowresp reproduces the cost of the call in slowhttp without
// net/http, an interface, or a pointer field: a trusted function returns a
// struct with the fields of http.Response that hold strings, slices of
// strings, maps of them, integers, and booleans. The reviewer of speed
// measured Code at 84 s. Since its questions are solved without the axiom
// of extensionality it takes under a second, and the main corpus run keeps
// it there through the table of costs; see The prover in the ROADMAP.
package slowresp

import "slowresplib"

// Code fetches and returns the status code.
//
// @Ensures True
func Code(url string) (code int, err error) {
	r, err := slowresplib.Get(url)
	if err != nil {
		return 0, err
	}
	return r.StatusCode, nil
}
