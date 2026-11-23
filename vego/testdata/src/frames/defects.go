package frames

import "io"

// Scribble writes a long string into a tag of a task before it answers:
// what the invariant reads has changed, and it is proved again, which
// fails.
//
// @Requires s != nil And w != nil
// @Modifies s, w, s.store.tasks[id].Tags
// @Ensures True
func (s *Server) Scribble(w io.Writer, id int, x string, p []byte) {
	t := s.store.tasks[id]
	if len(t.Tags) > 0 {
		t.Tags[0] = x
	}
	w.Write(p)
} // want `vego: invariant of Store may not hold for s on return, in what it owns at store: \(Forall k in tasks : .*; it was not kept from entry, since \|tasks\[k\]\.Tags\[j\]\| may have changed: the assignment to t\.Tags\[0\] at defects\.go:15:3 may write it`

// Rewrite writes every task in a loop.
//
// @Requires st != nil
// @Modifies st
// @Ensures True
func (st *Store) Rewrite(x string) {
	for k, t := range st.tasks {
		t.Text = x
		st.tasks[k] = t
	}
} // want `vego: invariant of Store may not hold for st on return: \(Forall k in tasks : .*; it was not kept from entry, since has\(tasks, k\) may have changed: the loop at defects\.go:26:2 may write it`

// overwrite writes the first element of what it is handed.
//
// @Requires |tags| > 0
// @Modifies tags
// @Ensures True
func overwrite(tags []string, x string) {
	tags[0] = x
}

// PassTags hands a helper the tags of a task, which the helper writes.
//
// @Requires s != nil
// @Modifies s, s.store.tasks[id].Tags
// @Ensures True
func (s *Server) PassTags(id int, x string) {
	t := s.store.tasks[id]
	if len(t.Tags) > 0 {
		overwrite(t.Tags, x)
	}
} // want `vego: invariant of Store may not hold for s on return, in what it owns at store: \(Forall k in tasks : .*; it was not kept from entry, since \|tasks\[k\]\.Tags\[j\]\| may have changed: the call to overwrite at defects\.go:49:3 may write it`

// Bump has an invariant that a call made under a condition of evaluation
// restores; on the path where the condition is false it does not hold.
//
// @Invariant 0 <= n
type Bump struct{ n int }

// @Requires b != nil
// @Modifies b
// @Ensures r
func fix(b *Bump) (r bool) {
	b.n = 0
	return true
}

// Guarded breaks the invariant on one path and restores it only under
// the condition of b && fix(s) (F1 of the design review).
//
// @Requires s != nil
// @Modifies s
// @Ensures True
func Guarded(s *Bump, b bool) {
	if !b {
		s.n = -1
	}
	_ = b && fix(s)
} // want `vego: invariant of Bump may not hold for s on return: 0 <= n; it was not kept from entry, since n may have changed: the assignment to s\.n at defects\.go:75:3 may write it`

// AddBad adds a task the invariant does not allow: the domain of the
// invariant's quantifier has changed, which the frame sees.
//
// @Requires st != nil And ~has(st.tasks, 7)
// @Modifies st
// @Ensures True
func (st *Store) AddBad(x string) {
	st.tasks[7] = Task{Text: x}
} // want `vego: invariant of Store may not hold for st on return: \(Forall k in tasks : .*; it was not kept from entry, since has\(tasks, k\) may have changed: the assignment to st\.tasks\[7\] at defects\.go:87:2 may write it`

// AfterCall breaks the invariant after a call that restored it, in the
// same state: what the call's entry holds is the memory after the call,
// not what the state comes to hold.
//
// @Requires s != nil
// @Modifies s
// @Ensures True
func AfterCall(s *Bump) {
	fix(s)
	s.n = -1
} // want `vego: invariant of Bump may not hold for s on return: 0 <= n; it was not kept from the call to fix at defects\.go:98:2, since n may have changed: the assignment to s\.n at defects\.go:99:2 may write it`

// each calls f with each number below n; its entry is in the corpus's
// trust file.
func each(n int, f func(i int)) {
	for i := range n {
		f(i)
	}
}

// HandedBreak hands each a literal that calls fix: a run knows nothing of
// b, which the trusted function may have left in any state between runs,
// and what a run keeps of the invariants of b stays in the run, so the
// caller, which breaks b after the call, proves them again.
//
// @Requires b != nil
// @Modifies b
// @Ensures True
func HandedBreak(b *Bump, n int) {
	each(n, func(i int) { fix(b) }) // want `vego: invariant of Bump may not hold for what is passed to fix as b: 0 <= n, in the function literal run by each`
	if n > 0 {
		b.n = -1
	}
} // want `vego: invariant of Bump may not hold for b on return: 0 <= n; it was not kept from entry, since n may have changed: the call to each at defects\.go:119:2 may write it`

// Positive is a struct whose invariant holds only where n is set.
//
// @Invariant 0 < n
type Positive struct{ n int }

// @Requires p != nil
// @Ensures True
func usePositive(p *Positive) {}

// TwoEnds calls a literal with two ends, of which only one holds the
// invariant of x, after its own test (F9 of the review). The joined state
// keeps no entry made on one end, so the second call proves the invariant
// again, which fails when k <= 0.
//
// @Ensures True
func TwoEnds(k int) {
	x := &Positive{n: k}
	func() {
		if x.n > 0 {
			usePositive(x)
			return
		}
	}()
	usePositive(x) // want `vego: invariant of Positive may not hold for what is passed to usePositive as p: 0 < n`
}
