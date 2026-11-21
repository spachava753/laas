package guide

import (
	"slices"
)

// HasRole reports whether role is one of roles.
//
// @Ensures r <-> Exists i in [0, |roles|) : roles[i] = role
func HasRole(roles []string, role string) (r bool) {
	return slices.Contains(roles, role)
}

// Member is a struct, which a formula cannot compare as a whole.
type Member struct {
	Name string
	Age  int
}

// HasMember asks for a whole struct.
//
// @Ensures True
func HasMember(ms []Member, m Member) (r bool) {
	return slices.Contains(ms, m) // want `the trusted contract of slices.Contains \(slices.yaml:\d+\) cannot be used with S = \[\]Member, E = Member: in its ensures "result <-> Exists i in \[0, \|s\|\) : s\[i\] = v": a value of type E, which is Member here, is a struct, and a formula cannot compare a struct or use it as a whole; call slices.ContainsFunc instead, with a function literal that compares what you need of the elements, or write a loop`
}

// HasName looks for a member by name.
//
// @Ensures r -> |ms| > 0
func HasName(ms []Member, name string) (r bool) {
	return slices.ContainsFunc(ms, func(m Member) bool { return m.Name == name })
}

// AgeOf returns the age of the member with a name, or -1.
//
// @Ensures True
func AgeOf(ms []Member, name string) (age int) {
	i := slices.IndexFunc(ms, func(m Member) bool { return m.Name == name })
	if i < 0 {
		return -1
	}
	return ms[i].Age
}

// Pad appends n zero bytes to buf, growing it once.
//
// @Requires 0 <= n And |buf| + n <= 1000000
// @Ensures |r| = |buf| + n
func Pad(buf []byte, n int) (r []byte) {
	buf = slices.Grow(buf, n)
	r = buf[:len(buf)+n]
	return r
}

// SortedNames returns the names of the members in order, which are new.
//
// @Requires |ms| <= 1000
// @Ensures |r| = |ms|
func SortedNames(ms []Member) (r []string) {
	r = make([]string, len(ms))
	// @Invariant 0 <= i And i <= |ms| And |r| = |ms|
	// @Variant |ms| - i
	for i := 0; i < len(ms); i++ {
		r[i] = ms[i].Name
	}
	slices.Sort(r)
	return r
}

// Oldest returns the greatest age.
//
// @Requires |ages| > 0
// @Ensures Forall i in [0, |ages|) : ages[i] <= r
func Oldest(ages []int) (r int) {
	return slices.Max(ages)
}

// Last returns the name that sorts last.
//
// @Requires |names| > 0
// @Ensures True
func Last(names []string) (r string) {
	return slices.Max(names) // want `the trusted contract of slices.Max \(slices.yaml:\d+\) cannot be used with S = \[\]string, E = string: in its ensures "x\[0:\|x\|\) <= result": operator <= cannot be applied to string or slice values; a formula has no order of them; write a loop instead`
}

// Votes counts how often v occurs in s.
func Votes[S ~[]E, E comparable](s S, v E) int {
	n := 0
	for _, x := range s {
		if x == v {
			n++
		}
	}
	return n
}

// CountVotes counts the votes for a name.
//
// @Ensures 0 <= r And r <= |names|
func CountVotes(names []string, name string) (r int) {
	return Votes(names, name)
}

// CloneErrors copies a slice of errors.
//
// @Requires |errs| <= 100
// @Ensures True
func CloneErrors(errs []error) (r []error) {
	return slices.Clone(errs) // want `slices.Clone is called with S = \[\]error, which is or holds an error; a generic function cannot be called yet with a type argument that can hold code`
}

// AppendZero grows buf by one element and sets it.
//
// @Requires |buf| < 1000
// @Ensures |r| = |buf| + 1
func AppendZero(buf []byte) (r []byte) {
	r = slices.Grow(buf, 1)
	r = r[:len(r)+1]
	r[len(r)-1] = 0 // want `r\[len\(r\) - 1\] is assigned, which AppendZero may not modify; it is memory that Grow returned, which its contract places within s when it is not new, and AppendZero passed buf as s; list buf in a // @Modifies clause`
	return r
}
