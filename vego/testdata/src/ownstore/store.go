// Package ownstore is an in-memory store of tasks in the shape of the
// trial's task store: its invariant names fields that other packages
// cannot name (F27, step 2).
package ownstore

import (
	"fmt"
	"sync"
)

// Task is one task.
type Task struct {
	ID   int
	Text string
	Tags []string
}

// Store owns its map of tasks, which is never nil.
//
// @Owns tasks
// @Invariant tasks != nil And 0 <= nextID
type Store struct {
	sync.Mutex

	tasks  map[int]Task
	nextID int
}

// New makes an empty store.
//
// @Ensures result != nil And fresh(result) And ~held(result.Mutex) And |result.tasks| = 0
func New() (result *Store) {
	st := &Store{}
	st.tasks = make(map[int]Task)
	return st
}

// Create adds a task and returns its id, or -1 when the ids run out.
//
// @Requires st != nil And ~held(st.Mutex)
// @Modifies st
// @Ensures ~held(st.Mutex')
func (st *Store) Create(text string) (id int) {
	st.Lock()
	defer st.Unlock()
	if st.nextID == MaxInt {
		return -1
	}
	id = st.nextID
	st.tasks[id] = Task{ID: id, Text: text}
	st.nextID++
	return id
}

// MaxInt is the largest int.
const MaxInt = int(^uint(0) >> 1)

// Get returns the task with an id.
//
// @Requires st != nil And ~held(st.Mutex)
// @Modifies st.Mutex
// @Ensures ~held(st.Mutex')
// @Ensures (err = nil) <-> has(st.tasks, id)
func (st *Store) Get(id int) (t Task, err error) {
	st.Lock()
	defer st.Unlock()
	t, ok := st.tasks[id]
	if !ok {
		return Task{}, fmt.Errorf("task %d not found", id)
	}
	return t, nil
}

// All returns every task, in some order.
//
// @Requires st != nil And ~held(st.Mutex)
// @Modifies st.Mutex
// @Ensures ~held(st.Mutex') And |all| = |st.tasks|
func (st *Store) All() (all []Task) {
	st.Lock()
	defer st.Unlock()
	all = make([]Task, 0, len(st.tasks))
	// @Visited done
	// @Invariant |all| = |done| And cap(all) = |st.tasks|
	for _, t := range st.tasks {
		all = append(all, t)
	}
	return all
}

// ByTag returns the tasks that have a tag, ranging over the map and over
// each task's tags, as the trial's GetTasksByTag does (F32 of the review
// of step 3a): a task read from the map is outside.
//
// @Requires st != nil And ~held(st.Mutex) And |st.tasks| <= 1000000
// @Modifies st.Mutex
// @Ensures ~held(st.Mutex')
func (st *Store) ByTag(tag string) (tasks []Task) {
	st.Lock()
	defer st.Unlock()
	// @Visited done
	// @Invariant |tasks| <= |done|
	for _, task := range st.tasks {
		// @Invariant |tasks| <= |done|
		for _, taskTag := range task.Tags {
			if taskTag == tag {
				tasks = append(tasks, task)
				break
			}
		}
	}
	return tasks
}

// Clear deletes every task, with a new map.
//
// @Requires st != nil And ~held(st.Mutex)
// @Modifies st
// @Ensures ~held(st.Mutex') And |st.tasks'| = 0
func (st *Store) Clear() {
	st.Lock()
	defer st.Unlock()
	st.tasks = make(map[int]Task)
}

// Break breaks the invariant of the store it is handed, which its return
// must restore.
//
// @Requires st != nil
// @Modifies st
// @Ensures True
func (st *Store) Break() {
	st.nextID = -1
} // want `vego: invariant of Store may not hold for st on return: 0 <= nextID`

// Reset gives the store a new map. It is a helper that other packages
// hand the store to under valid, and it says valid of it on return (the
// orchestrator's program).
//
// @Requires st != nil And valid(st)
// @Modifies st
// @Ensures valid(st')
func Reset(st *Store) {
	st.tasks = make(map[int]Task)
}
