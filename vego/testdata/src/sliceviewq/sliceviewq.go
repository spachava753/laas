// Package sliceviewq is not verified: View makes a slice over the two fields
// of a sliceviewsliceviewp.S, which the assumption excludes.
package sliceviewq

import (
	"unsafe"

	"sliceviewp"
)

// View is not verified: a slice over the two fields of s, which the
// documentation of unsafe.Slice allows, since they lie in one allocation.
func View(s *sliceviewp.S) []int {
	return unsafe.Slice(&s.M, 2)
}
