// Package frames holds invariants kept by frame: a goal that the
// invariants of a value hold is proved by showing that nothing they read
// has changed since a point where they held (frames.go).
package frames

import "io"

// Task is a task of the store.
type Task struct {
	ID   int
	Text string
	Tags []string
}

// Store bounds every task it holds, two quantifiers deep.
//
// @Invariant tasks != nil And (Forall k in tasks : |tasks[k].Text| <= 1000 And |tasks[k].Tags| <= 10 And (Forall j in [0, |tasks[k].Tags|) : |tasks[k].Tags[j]| <= 100))
// @Owns tasks
type Store struct {
	tasks map[int]Task
}

// Server owns its store.
//
// @Owns store
// @Invariant store != nil
type Server struct {
	store *Store
}

// Answer writes through a writer and keeps the invariants of s, which
// the writer cannot write.
//
// @Requires s != nil And w != nil
// @Modifies w
// @Ensures True
func (s *Server) Answer(w io.Writer, p []byte) {
	w.Write(p)
}

// AnswerTwice writes twice, on two paths.
//
// @Requires s != nil And w != nil
// @Modifies w
// @Ensures True
func (s *Server) AnswerTwice(w io.Writer, p []byte, both bool) {
	w.Write(p)
	if both {
		w.Write(p)
		return
	}
}

// Size reads a task, then writes.
//
// @Requires s != nil And w != nil
// @Modifies w
// @Ensures n <= 1000
func (s *Server) Size(w io.Writer, id int, p []byte) (n int) {
	t := s.store.tasks[id]
	w.Write(p)
	return len(t.Text)
}

// Longest walks the store and writes only its own result.
//
// @Requires st != nil
// @Ensures n <= 1000
func (st *Store) Longest() (n int) {
	// @Invariant n <= 1000
	for _, t := range st.tasks {
		if len(t.Text) > n {
			n = len(t.Text)
		}
	}
	return n
}

// Tagged collects the tasks with a tag, keeping valid(st) at the head of
// the loop as a loop invariant.
//
// @Requires st != nil
// @Ensures |found| <= |st.tasks|
func (st *Store) Tagged(tag string) (found []int) {
	// @Visited done
	// @Invariant valid(st) And |found| <= |done|
	for k, t := range st.tasks {
		if len(t.Tags) > 0 && t.Tags[0] == tag {
			found = append(found, k)
		}
	}
	return found
}

// tally counts into a map of its own.
//
// @Requires counts != nil
// @Modifies counts
// @Ensures True
func tally(counts map[string]int, word string) {
	counts[word] = 1
}

// Count hands a helper other memory, which the invariants of s do not read.
//
// @Requires s != nil And counts != nil And w != nil
// @Modifies counts, w
// @Ensures True
func (s *Server) Count(w io.Writer, counts map[string]int, p []byte) {
	tally(counts, "a")
	w.Write(p)
}

// AnswerAll writes in a loop and states valid(s) at its head.
//
// @Requires s != nil And w != nil
// @Modifies w
// @Ensures True
func (s *Server) AnswerAll(w io.Writer, ps [][]byte) {
	// @Invariant valid(s)
	for i := range ps {
		w.Write(ps[i])
	}
}

// AnswerAllUnsaid is AnswerAll without the loop invariant: the frame
// goes from entry through the head of the loop.
//
// @Requires s != nil And w != nil
// @Modifies w
// @Ensures True
func (s *Server) AnswerAllUnsaid(w io.Writer, ps [][]byte) {
	for i := range ps {
		w.Write(ps[i])
	}
}

// Valid says valid(s') in its Ensures, which a frame proves.
//
// @Requires s != nil And w != nil
// @Modifies w
// @Ensures valid(s')
func (s *Server) Valid(w io.Writer, p []byte) {
	w.Write(p)
	w.Write(p)
}
