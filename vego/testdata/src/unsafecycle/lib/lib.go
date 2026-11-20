// Package lib runs what it is handed, also through an unsafe.Pointer.
package lib

import "unsafe"

// Run calls the function that p points to.
func Run(p unsafe.Pointer) { (*(*func())(p))() }

// Call calls f.
func Call(f func()) { f() }

// Read reads the int that p points to.
func Read(p unsafe.Pointer) int { return *(*int)(p) }
