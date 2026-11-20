// Package q stands for another package that reads what it is handed.
package q

import "io"

// Use reads once from r; it asserts r to nothing.
func Use(r io.Reader) int {
	n, _ := r.Read(make([]byte, 1))
	return n
}

// UseWide reads once from r too, and its entry claims nothing about what it
// asserts r to.
func UseWide(r io.Reader) int {
	n, _ := r.Read(make([]byte, 1))
	return n
}

// Plain reads once from r, and has no entry at all.
func Plain(r io.Reader) int {
	n, _ := r.Read(make([]byte, 1))
	return n
}
