// Package sizesbig declares 4TB, for which 3 * R + 81 * M and 2^20 is more
// than one allocation can be on amd64, so encoding is held to its bound as
// without a declaration, while an append still fits (step 3 of F38).
package sizesbig

import "encoding/json"

// @Ensures True
func Encoded(names []string) (r []byte, err error) {
	r, err = json.Marshal(names) // want `vego: what Marshal builds from names may be more than can be allocated`
	return r, err
}

// @Modifies s
// @Ensures |r| = |s| + 1
func Push(s []int, x int) (r []int) {
	r = append(s, x)
	return r
}
