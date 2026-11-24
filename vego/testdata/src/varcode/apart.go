package varcode

import (
	"fmt"
	"io"
)

// What the parameters of a function that lists an interface variable by
// itself reach lies outside the footprint of what the variable holds on
// entry, as for a writer that is a parameter.

var out io.Writer

// setOutTo makes out assigned.
//
// @Requires w != nil
// @Modifies out
// @Ensures out' = w
func setOutTo(w io.Writer) {
	out = w
}

// printAll writes every name, whose bound it keeps across the writes. It
// writes through the writer out holds and does not assign out, which its
// callers may rely on.
//
// @Requires out != nil And |l| <= 1000
// @Requires Forall i in [0, |l|) : |l[i]| <= 100
// @Modifies out
// @Ensures out' = out
func printAll(l []string) {
	for _, s := range l {
		fmt.Fprint(out, s)
	}
	fmt.Fprintln(out)
}

// printOwn hands on its own parameter, which lies outside that footprint
// as printAll assumes, and then a slice it makes; out holds the value it
// held on entry at both calls, as printAll ensures.
//
// @Requires out != nil And |l| <= 1000
// @Requires Forall i in [0, |l|) : |l[i]| <= 100
// @Modifies out
// @Ensures True
func printOwn(l []string) {
	printAll(l)
	printAll([]string{"a", "b"})
}

// tally counts the writes to it in its own struct.
type tally struct{ n int }

// @Requires t != nil
// @Modifies t
// @Ensures n = |p| And err = nil
func (t *tally) Write(p []byte) (n int, err error) {
	if t.n < 1000 {
		t.n++
	}
	return len(p), nil
}

// keeps claims what t refers to is kept across a write through out.
//
// @Requires out != nil And t != nil
// @Modifies out
// @Ensures t.n = old(t.n)
func keeps(t *tally) {
	out.Write([]byte("x"))
}

// redirectThenKeep hands keeps the very tally out now holds, which keeps
// would change while it claims to keep it.
//
// @Modifies out
// @Ensures True
func redirectThenKeep() {
	t := &tally{}
	out = t
	keeps(t) // want `^vego: the footprint of what out holds may hold memory that what is passed to keeps as t reaches, and keeps relies on it not doing so: out may hold here a value other than the one it held when redirectThenKeep was entered`
}

// literalKeeps calls keeps from a literal, which assumes nothing of what
// it is handed.
//
// @Requires t != nil And out != nil
// @Modifies out
// @Ensures True
func literalKeeps(t *tally) {
	f := func() {
		keeps(t) // want `^vego: the footprint of what out holds may hold memory that what is passed to keeps as t reaches, and keeps relies on it not doing so: a function literal places no footprint, in the function literal called at apart.go:\d+:\d+$`
	}
	f()
}

// printTo writes through out after assigning it the writer it lists, so
// what it writes through is that writer's footprint, which it assumes apart
// from l, as for any writer that is a parameter.
//
// @Requires w != nil And |l| <= 1000
// @Requires Forall i in [0, |l|) : |l[i]| <= 100
// @Modifies out, w
// @Ensures True
func printTo(w io.Writer, l []string) {
	out = w
	for _, s := range l {
		fmt.Fprint(out, s)
	}
}

var names []string

// setNames makes names assigned.
//
// @Modifies names
// @Ensures True
func setNames(l []string) {
	names = l
}

// printNames hands printAll what another variable refers to, which a test
// may have put in the footprint of the writer out holds.
//
// @Requires out != nil And |names| <= 1000
// @Requires Forall i in [0, |names|) : |names[i]| <= 100
// @Modifies out
// @Ensures True
func printNames() {
	printAll(names) // want `^vego: the footprint of what out holds may hold memory that what is passed to printAll as names reaches, and printAll relies on it not doing so: it is read from the package-level variable names, and code elsewhere may hold a reference to what it refers to; take it as a parameter instead$`
}
