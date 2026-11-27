// Package ptrmore holds ordinary programs with pointers to slices, maps,
// pointers, and errors (F42, step 2).
package ptrmore

import "errors"

// add appends s to the slice out points to.
//
// @Requires out != nil And |*out| < 1000
// @Modifies out, *out
// @Ensures |*out'| = |*out| + 1 And (*out')[|*out|] = s
// @Ensures Forall i in [0, |*out|) : (*out')[i] = (*out)[i]
// @Ensures fresh(*out) Or within(*out', *out)
func add(out *[]string, s string) {
	*out = append(*out, s)
}

// Collect fills a local slice through a pointer to it.
//
// @Ensures |r| = 2 And r[0] = "a" And r[1] = "b"
func Collect() (r []string) {
	var xs []string
	add(&xs, "a")
	add(&xs, "b")
	return xs
}

// Config holds a list.
type Config struct {
	Items []string
	n     int
}

// AddItem appends to a field through a pointer to it, and keeps n.
//
// @Requires c != nil And |c.Items| < 1000
// @Modifies c, c.Items
// @Ensures |c.Items'| = |c.Items| + 1 And c.n' = c.n
func AddItem(c *Config, s string) {
	add(&c.Items, s)
}

// Tags is a list with a method that grows it.
type Tags []string

// Add appends s.
//
// @Requires t != nil And |*t| < 1000
// @Modifies t, *t
// @Ensures |*t'| = |*t| + 1
// @Ensures fresh(*t) Or within(*t', *t)
func (t *Tags) Add(s string) {
	*t = append(*t, s)
}

// TwoTags adds two tags to a local.
//
// @Ensures |r| = 2
func TwoTags() (r Tags) {
	var t Tags
	t.Add("x")
	t.Add("y")
	return t
}

// Node is a node.
type Node struct {
	v int
}

// newNode stores a new node where out points.
//
// @Requires out != nil
// @Modifies out
// @Ensures *out' != nil And fresh(*out) And (*out').v = 1
func newNode(out **Node) {
	*out = &Node{v: 1}
}

// UseNode gets a node through an out-parameter.
//
// @Ensures r = 1
func UseNode() (r int) {
	var n *Node
	newNode(&n)
	return n.v
}

// setErr stores an error where errp points.
//
// @Requires errp != nil
// @Modifies errp
// @Ensures *errp' != nil
func setErr(errp *error) {
	*errp = errors.New("failed")
}

// Run sets its result in a deferred call when it is asked to fail.
//
// @Ensures fail = (err != nil)
func Run(fail bool) (err error) {
	if fail {
		defer setErr(&err)
	}
	return nil
}

// ensure makes the map m points to if it is nil.
//
// @Requires m != nil
// @Modifies m
// @Ensures *m' != nil
func ensure(m *map[string]int) {
	if *m == nil {
		*m = map[string]int{}
	}
}

// Counts makes a map through a pointer to it.
//
// @Ensures r != nil
func Counts() (r map[string]int) {
	var m map[string]int
	ensure(&m)
	return m
}

// AddUnlisted appends without listing the elements.
//
// @Requires out != nil And |*out| < 1000
// @Modifies out
// @Ensures True
func AddUnlisted(out *[]string, s string) {
	*out = append(*out, s) // want `vego: append may write into the capacity of \*out, which AddUnlisted may not modify`
}

// KeepsOther claims a slice unchanged that out may point to.
//
// @Requires out != nil And other != nil And |*out| < 1000
// @Modifies out, *out
// @Ensures |*other'| = |*other|
func KeepsOther(out, other *[]string) {
	add(out, "x")
} // want `vego: postcondition may not hold: \|\*other'\| = \|\*other\|`

// NodeWrong claims the node it made is nil.
//
// @Ensures r = nil
func NodeWrong() (r *Node) {
	newNode(&r)
	return r // want `vego: postcondition may not hold: r = nil`
}

// RunWrong claims that it fails when it does not.
//
// @Ensures err != nil
func RunWrong(fail bool) (err error) {
	if fail {
		defer setErr(&err)
	}
	return nil // want `vego: postcondition may not hold: err != nil`
}

// CountsWrong claims the map it made is nil.
//
// @Ensures r = nil
func CountsWrong() (r map[string]int) {
	ensure(&r)
	return r // want `vego: postcondition may not hold: r = nil`
}

// put stores a value of its own type where p points.
//
// @Requires p != nil
// @Modifies p
// @Ensures *p' != nil
func put(p *any) {
	*p = 3
}

// Any fills an interface variable through a pointer to it.
//
// @Ensures r != nil
func Any() (r any) {
	put(&r)
	return r
}

// setFn stores a function where p points: the pointer is supported, and the
// literal stored is refused, since a literal used as a value needs a named
// function type with a contract (see Function values).
//
// @Requires p != nil
// @Modifies p
// @Ensures *p' != nil
func setFn(p *func() int) {
	*p = func() int { return 1 } // want `vego: cannot verify setFn: the function literal is used as a value of type func\(\) int, which has no contract`
}

// Fn fills a function variable through a pointer to it.
//
// @Ensures r != nil
func Fn() (r func() int) {
	setFn(&r)
	return r
}

// FirstRow appends to the first row through a pointer to it, and keeps the
// others.
//
// @Requires |rows| > 1 And |rows[0]| < 1000 And apart(rows[0], rows[1])
// @Modifies rows, rows[0]
// @Ensures |rows'[0]| = |rows[0]| + 1 And |rows'[1]| = |rows[1]|
func FirstRow(rows [][]string) {
	add(&rows[0], "x")
}

// Holder holds tags.
type Holder struct {
	Tags Tags
	n    int
}

// AddTag calls the pointer method of a named slice type on a field.
//
// @Requires h != nil And |h.Tags| < 1000
// @Modifies h, h.Tags
// @Ensures |h.Tags'| = |h.Tags| + 1 And h.n' = h.n
func AddTag(h *Holder) {
	h.Tags.Add("x")
}

// List owns its items.
//
// @Owns items
type List struct {
	items []string
}

// AddOwned would hand out a pointer to an owned field.
//
// @Requires l != nil And |l.items| < 1000
// @Modifies l, l.items
// @Ensures True
func AddOwned(l *List) {
	add(&l.items, "x") // want `vego: cannot verify AddOwned: taking the address of l\.items is not supported: it is an owned field`
}
