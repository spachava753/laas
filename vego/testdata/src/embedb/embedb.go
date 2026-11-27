// Package embedb hands embeda.Keep a pointer into the struct it gets,
// taken through the promoted method Ptr, which names no field.
package embedb

import "embeda"

// Use hands Keep a pointer into s.
func Use() int {
	s := &embeda.S{}
	p := s.Ptr()
	embeda.Keep(p, s)
	return 0
}
