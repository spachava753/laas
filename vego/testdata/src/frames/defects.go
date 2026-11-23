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
} // want `vego: invariant of Store may not hold for s on return, in what it owns at store: \(Forall k in tasks : `

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
} // want `vego: invariant of Store may not hold for st on return: \(Forall k in tasks : `

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
} // want `vego: invariant of Store may not hold for s on return, in what it owns at store: \(Forall k in tasks : `

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
} // want `vego: invariant of Bump may not hold for s on return: 0 <= n`

// AddBad adds a task the invariant does not allow: the domain of the
// invariant's quantifier has changed, which the frame sees.
//
// @Requires st != nil And ~has(st.tasks, 7)
// @Modifies st
// @Ensures True
func (st *Store) AddBad(x string) {
	st.tasks[7] = Task{Text: x}
} // want `vego: invariant of Store may not hold for st on return: \(Forall k in tasks : `

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
} // want `vego: invariant of Bump may not hold for s on return: 0 <= n`

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
} // want `vego: invariant of Bump may not hold for b on return: 0 <= n`
