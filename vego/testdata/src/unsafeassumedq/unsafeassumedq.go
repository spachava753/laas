// Package unsafeassumedq is not verified. Field makes a pointer to the
// unexported field n of an unsafeassumed.S by reflect's UnsafeAddr, which
// "What a proof assumes" excludes.
package unsafeassumedq

import (
	"reflect"
	"unsafe"

	"unsafeassumed"
)

// Field returns a pointer to the second field of s.
func Field(s *unsafeassumed.S) *int {
	return (*int)(unsafe.Pointer(reflect.ValueOf(s).Elem().Field(1).UnsafeAddr()))
}
