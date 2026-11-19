package vego

import (
	"fmt"
	"go/token"
	"go/types"
	"maps"
	"slices"

	"github.com/spachava753/laas/vego/internal/logic"
)

// Go fixes part of the order in which the operands of a statement are
// evaluated, and leaves the rest open. Calls, method calls, and the
// operators && and || run in lexical left-to-right order; an operation runs
// after its operands; the right of && and || runs after the left; and an
// assignment stores only once every operand has been evaluated. When the
// other reads of memory happen relative to the calls is not fixed: in
// p.n + f(p), p.n may be read before or after f runs. Built-in functions,
// append among them, are not taken to be ordered like calls, since the
// specification does not say that they are.
//
// The verifier evaluates in one order Go allows, its own: left to right,
// operands before operations, the operands of the targets of an assignment
// before the right-hand side. Memory changes inside a statement only where
// a call that may modify it runs, or an append writes into the array of its
// slice; each such write starts a new version of memory. Every read of
// memory records which versions Go would let it see, and once the statement
// has been evaluated the verifier proves that the read gives the same value
// in each of them. Then every order Go allows gives every read the same
// value: the operands a read depends on are themselves reads with one value,
// and calls run in a fixed order on the same arguments. A read whose value
// is not proved the same is reported where it is written.
//
// Variables the verifier holds itself cannot be changed by a call, which
// gets no pointer to them, so reading them is not a read of memory.

// unit is the evaluation of the operands of one statement, or of one
// condition or case expression.
type unit struct {
	// versions holds memory as it was at the start of the unit and after
	// each write, and writers describes what made each one.
	versions []memory
	writers  []string
	// events counts the calls and the decisions of && and || so far, and
	// after is the version after the latest of them.
	events int
	after  int
	// floor is the version after the && or || whose right operand is being
	// evaluated, which every read there comes after.
	floor int
	// starts holds, for each expression being evaluated, the number of
	// events before its evaluation began.
	starts []int
	// ceilings holds, innermost last, the events that the reads now being
	// evaluated come before: a call whose receiver or argument they are part
	// of, the && or || on whose left they are, or an append whose operand
	// they are.
	ceilings []*ceiling
	reads    []*recorded
	calls    []unitCall
	born     []bornRow
	// recording counts the reads being made on behalf of a recorded read,
	// and quiet the reads of memory that are not reads Go makes, such as
	// what a contract says; see table.
	recording, quiet int
	// snapshot returns what a version holds in a state: memory, and the
	// values of the variables a function literal assigns; see captured.
	snapshot func(st *state) memory
}

// ceiling is an event that reads come before. version is the latest
// version when it happened.
type ceiling struct {
	version int
	set     bool
}

// recorded is a read of memory: what is read, where, under which guard,
// how to read it in any version, and the first and last versions that Go
// lets it see. end is set when the read may also see every write up to the
// end of the unit whatever its ceiling says.
type recorded struct {
	what  string
	pos   token.Pos
	guard []*logic.Term
	read  func(sink *state, mem memory) value
	lo    int
	hi    *ceiling
	end   bool
}

// unitCall is a call made in the unit, with whether it can be moved across
// a write to memory without changing what it does; see memoryFree.
type unitCall struct {
	name string
	pos  token.Pos
	pure bool
}

// bornRow is what an allocation made in the unit put into memory for its
// new reference: in region key, the row for ref. before is the number of
// versions that existed when it was made.
type bornRow struct {
	key    string
	sort   logic.Sort
	ref    *logic.Term
	row    *logic.Term
	before int
}

// openUnit starts the evaluation of the operands of a statement.
func (v *fnVerifier) openUnit(st *state) {
	if v.unit != nil {
		panic("vego: internal error: an evaluation unit was opened inside another")
	}
	v.unit = &unit{writers: []string{""}, snapshot: v.snapshot}
	v.unit.versions = []memory{v.unit.snapshot(st)}
}

// snapshot returns memory as it is in a state, as a version of a unit has
// it. A call of a function literal can change a variable of the function
// that the literal assigns, which no other call can; a version also holds
// the value of each such variable, under a key of its own, so that a read
// of it is compared across a call like a read of memory.
func (v *fnVerifier) snapshot(st *state) memory {
	if len(v.captured) == 0 {
		return maps.Clone(st.mem)
	}
	mem := maps.Clone(st.mem)
	for variable, index := range v.captured {
		for i, leaf := range st.vals[variable] {
			mem[localKey(index, i)] = leaf
		}
	}
	return mem
}

// localKey is the key under which a version of a unit holds one leaf of a
// variable that a function literal assigns. A space keeps it apart from the
// keys of regions.
func localKey(variable, leaf int) string {
	return fmt.Sprintf("local %d.%d", variable, leaf)
}

// fork returns a copy of the unit that can be closed on a state of its own,
// for an append that continues once for each way it can turn out.
func (u *unit) fork() *unit {
	copied := *u
	copied.versions, copied.writers = slices.Clone(u.versions), slices.Clone(u.writers)
	copied.starts, copied.ceilings = slices.Clone(u.starts), slices.Clone(u.ceilings)
	copied.calls, copied.born = slices.Clone(u.calls), slices.Clone(u.born)
	copied.reads = make([]*recorded, len(u.reads))
	for i, r := range u.reads {
		read := *r
		copied.reads[i] = &read
	}
	return &copied
}

// start returns the number of events before the evaluation of the innermost
// expression being evaluated began.
func (u *unit) start() int {
	return u.starts[len(u.starts)-1]
}

// begin records that the evaluation of an expression begins, and returns
// what ends it.
func (v *fnVerifier) begin() func() {
	u := v.unit
	if u == nil {
		panic("vego: internal error: an expression is evaluated outside an evaluation unit")
	}
	u.starts = append(u.starts, u.events)
	return func() { u.starts = u.starts[:len(u.starts)-1] }
}

// pushCeiling makes the next event one that every read evaluated until then
// comes before.
func (u *unit) pushCeiling() *ceiling {
	c := &ceiling{}
	u.ceilings = append(u.ceilings, c)
	return c
}

// reach records that the event a ceiling waits for is about to happen.
func (u *unit) reach(c *ceiling) {
	if n := len(u.ceilings); n == 0 || u.ceilings[n-1] != c {
		panic("vego: internal error: ceilings of an evaluation unit are not nested")
	}
	c.version, c.set = len(u.versions)-1, true
	u.ceilings = u.ceilings[:len(u.ceilings)-1]
}

// event records that a call or a decision of && or || has happened.
func (u *unit) event() {
	u.events++
	u.after = len(u.versions) - 1
}

// wrote records that memory has changed: what made the change, and memory
// as it is afterwards.
func (u *unit) wrote(st *state, writer string) {
	u.versions = append(u.versions, u.snapshot(st))
	u.writers = append(u.writers, writer)
}

// readAt makes a read of memory that the unit records. start is the number
// of events before the evaluation of the operands of the read began; read
// reads the value in any version of memory, telling sink what it learns.
func (v *fnVerifier) readAt(st *state, guard []*logic.Term, start int, what string, pos token.Pos, read func(sink *state, mem memory) value) value {
	u := v.unit
	if u == nil {
		panic("vego: internal error: memory is read outside an evaluation unit")
	}
	r := &recorded{what: what, pos: pos, guard: slices.Clip(guard), read: read, lo: u.floor}
	// What happened while the operands were evaluated happened before the
	// read, and so did everything before it.
	if u.events > start {
		r.lo = max(r.lo, u.after)
	}
	if n := len(u.ceilings); n > 0 {
		r.hi = u.ceilings[n-1]
	}
	u.reads = append(u.reads, r)
	u.recording++
	defer func() { u.recording-- }()
	if len(v.captured) > 0 {
		return read(st, u.snapshot(st))
	}
	return read(st, st.mem)
}

// quietly runs a task whose reads of memory are not reads Go makes, such as
// resolving a contract at a call.
func (v *fnVerifier) quietly(task func()) {
	if u := v.unit; u != nil {
		u.quiet++
		defer func() { u.quiet-- }()
	}
	task()
}

// noteBorn records what an allocation made in the unit put into memory for
// its new reference, in the regions with the given keys.
func (v *fnVerifier) noteBorn(st *state, ref *logic.Term, keys map[string]logic.Sort) {
	u := v.unit
	if u == nil {
		return
	}
	for _, key := range slices.Sorted(maps.Keys(keys)) {
		sort := keys[key]
		u.born = append(u.born, bornRow{key: key, sort: sort, ref: ref, row: logic.Select(st.mem.region(key, sort), ref), before: len(u.versions)})
	}
}

// memoryFree reports whether a value of the type refers to no memory at any
// depth: it is no pointer, slice, or map, and holds none.
func memoryFree(t types.Type) bool {
	switch u := t.Underlying().(type) {
	case *types.Basic:
		return true
	case *types.Struct:
		for field := range u.Fields() {
			if !memoryFree(field.Type()) {
				return false
			}
		}
		return true
	}
	return isError(t)
}

// closeUnit ends the evaluation of the operands of a statement: for every
// read, the versions it may see must give it the same value.
func (v *fnVerifier) closeUnit(st *state) {
	u := v.unit
	v.unit = nil
	if len(u.versions) == 1 {
		return
	}
	// An allocation made in the unit is not in the versions before it.
	// Nothing could refer to it there, so it is put into them as it was
	// made, by the same terms.
	versions := slices.Clone(u.versions)
	for _, b := range u.born {
		for m := range b.before {
			if versions[m][b.key] == u.versions[m][b.key] {
				versions[m] = maps.Clone(versions[m])
			}
			versions[m][b.key] = logic.Store(versions[m].region(b.key, b.sort), b.ref, b.row)
		}
	}
	end := len(versions) - 1
	for _, r := range u.reads {
		hi := end
		if r.hi != nil && !r.end {
			if !r.hi.set {
				panic("vego: internal error: a read comes before an event that did not happen")
			}
			hi = r.hi.version
		}
		for m := r.lo + 1; m <= hi; m++ {
			before, after := r.read(st, versions[m-1]), r.read(st, versions[m])
			var same []*logic.Term
			for i := range before {
				if before[i].String() != after[i].String() {
					same = append(same, v.same(before[i], after[i]))
				}
			}
			if len(same) == 0 {
				continue
			}
			v.check(st, r.guard, logic.And(same...), r.pos,
				"%s may be read before or after %s, which may change it, and Go does not fix the order; "+
					"split the statement so that the order is the one you mean", r.what, u.writers[m])
		}
	}
}

// evaluate runs the evaluation of the operands of a statement as a unit.
func (v *fnVerifier) evaluate(st *state, task func()) {
	v.openUnit(st)
	task()
	v.closeUnit(st)
}
