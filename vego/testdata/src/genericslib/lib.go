// Package genericslib holds generic functions that are not verified, whose
// contracts the trust file of the corpus gives, for the calls in generics.
package genericslib

import "fmt"

// Find returns the index of the first v in s, or -1.
func Find[S ~[]E, E comparable](s S, v E) int {
	for i := range s {
		if s[i] == v {
			return i
		}
	}
	return -1
}

// FindFunc returns the index of the first element f reports, or -1.
func FindFunc[S ~[]E, E any](s S, f func(E) bool) int {
	for i := range s {
		if f(s[i]) {
			return i
		}
	}
	return -1
}

// Top returns the largest element of a slice that is not empty.
func Top[S ~[]E, E int | int64 | string](s S) E {
	m := s[0]
	for _, x := range s[1:] {
		m = max(m, x)
	}
	return m
}

// Filter keeps the elements f reports, in place.
func Filter[S ~[]E, E any](s S, f func(E) bool) S {
	i := 0
	for _, x := range s {
		if f(x) {
			s[i] = x
			i++
		}
	}
	return s[:i]
}

// Reset sets every element to its zero value.
func Reset[S ~[]E, E any](s S) {
	var zero E
	for i := range s {
		s[i] = zero
	}
}

// GrowBy makes room for n more elements.
func GrowBy[S ~[]E, E any](s S, n int) S {
	if n -= cap(s) - len(s); n > 0 {
		s = append(s[:cap(s)], make([]E, n)...)[:len(s)]
	}
	return s
}

// Same returns its argument.
func Same[E any](x E) E { return x }

// Big returns x, which its entry claims is more than 300.
func Big[E int | uint8](x E) E { return x }

// Name returns the name of what it is given, by a field its entry names.
func Name[E any](x E) int { return 0 }

// Locked tells nothing; its entry names a state of what it is given.
func Locked[T any](x T) bool { return false }

// Address tells nothing; its entry takes the address of an element.
func Address[E any](s []E) bool { return false }

// Sized tells nothing; its entry takes the element size of an integer.
func Sized[E any](n int, x E) bool { return false }

// Show calls String on what it is given when it has one.
func Show[T any](x T) string {
	if s, ok := any(x).(fmt.Stringer); ok {
		return s.String()
	}
	return ""
}

// Bump calls the method of its constraint.
func Bump[T interface{ Inc() }](x T) { x.Inc() }

// Order sorts a slice of integers in place; it calls no method of them.
func Order[S ~[]E, E ~int](s S) {
	for i := range s {
		for j := i + 1; j < len(s); j++ {
			if s[j] < s[i] {
				s[i], s[j] = s[j], s[i]
			}
		}
	}
}

// Keep holds what it is given in a value it returns.
func Keep[T any](x T) *T { return &x }

// Count counts the elements; its entry claims types for its type
// parameter under asserts.
func Count[E any](s []E) int { return len(s) }

// Verified has annotations, but is generic, so it cannot be verified.
//
// @Ensures r = x
func Verified[E any](x E) (r E) { return x } // want `generic functions are not supported yet`

// Unentered has no entry.
func Unentered[E any](x E) E { return x }

// Equal reports whether a and b are equal.
func Equal[E comparable](a, b E) bool { return a == b }

// FindWhere is FindFunc; its entry names a field of the parameter of the
// function it is handed.
func FindWhere[S ~[]E, E any](s S, f func(E) bool) int { return FindFunc(s, f) }
