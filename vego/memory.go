package vego

import (
	"fmt"
	"go/token"
	"go/types"
	"maps"
	"slices"

	"github.com/spachava753/laas/vego/internal/logic"
	"github.com/spachava753/laas/vego/internal/solver"
)

// memory holds what pointers and slices refer to. It is divided into regions
// that can never overlap: one for each leaf of each struct type, holding that
// leaf for every object of the type, and one for each leaf of each slice
// element type, holding for every backing array the sequence of that leaf
// over its elements. A region is a sequence indexed by reference. A region
// that is absent has not changed since the function was entered.
type memory map[string]*logic.Term

// entryRegion names the contents of a region when the function is entered.
const entryRegion = "mem "

// region returns the current contents of a region.
func (m memory) region(key string, sort logic.Sort) *logic.Term {
	if current, ok := m[key]; ok {
		return current
	}
	return logic.Const(entryRegion+key, sort)
}

// state is the symbolic state on one execution path: the current value of
// every variable, the contents of memory, and the facts known to hold.
type state struct {
	vals map[*types.Var]value
	mem  memory
	// brk is the number below which every object that exists lies. Objects
	// are numbered in the order they are created, so anything created from
	// here on is at or above it.
	brk  *logic.Term
	hyps []*logic.Term
	// noted holds the facts about unchanged memory already added to hyps.
	noted map[string]bool
}

func (st *state) clone() *state {
	return &state{
		vals: maps.Clone(st.vals), mem: maps.Clone(st.mem), brk: st.brk,
		hyps: slices.Clone(st.hyps), noted: maps.Clone(st.noted),
	}
}

func (st *state) assume(fact *logic.Term) {
	if fact.Op != logic.OpTrue {
		st.hyps = append(st.hyps, fact)
	}
}

// layer records how a region was forgotten at the head of a loop: the region
// got a new unknown value, of which only this is known: an object that
// existed below bound and is none of the targets is as it was in prev.
type layer struct {
	prev    *logic.Term
	bound   *logic.Term
	targets []target
	// rows is set for a region that holds a sequence for each reference:
	// the elements of an array, or what a map has for each key.
	rows bool
}

// target is a piece of memory that may be written: some fields of one
// object, a stretch of one backing array, or one map.
type target struct {
	typ    types.Type // the struct type of the object, the element type of the array, or the map type
	elems  bool
	mapped bool
	prefix string // the fields of the object that are meant; empty for all
	ref    *logic.Term
	lo, hi *logic.Term // the stretch of the array, for elems
	text   string      // how the Modifies clause spells it
	clause *clause
	// param is set when the object or array is the very one that this
	// parameter holds.
	param *types.Var
}

// owner returns the prefix shared by the keys of all regions of the target's
// type.
func (t target) owner() string {
	switch {
	case t.mapped:
		return mapOwner(t.typ)
	case t.elems:
		return "[]" + typeKey(t.typ)
	}
	return typeKey(t.typ)
}

// regions calls visit for the key and the leaf of every region the target
// reaches into, and tells whether the region holds a sequence for each
// reference or a single value.
func (t target) regions(visit func(key string, lf leaf, rows bool)) {
	if t.mapped {
		_, elem := mapParts(t.typ)
		leaves, _ := layoutOf(elem)
		visit(t.owner()+countLeaf.path, countLeaf, false)
		visit(t.owner()+hasLeaf.path, hasLeaf, true)
		for _, lf := range leaves {
			visit(t.owner()+"#val"+lf.path, lf, true)
		}
		return
	}
	leaves, _ := layoutOf(t.typ)
	for _, lf := range leaves {
		if under(lf.path, t.prefix) {
			visit(t.owner()+lf.path, lf, t.elems)
		}
	}
}

// same states that two values of one leaf are equal.
func (v *fnVerifier) same(a, b *logic.Term) *logic.Term {
	if a.Sort.IsSeq() {
		return logic.SeqEq(a, b, v.bound("k"))
	}
	return logic.Eq(a, b)
}

// bound returns a bound variable with a name not used before.
func (v *fnVerifier) bound(base string) *logic.Term {
	return logic.Bound(v.fresh(base+"#", logic.Int).Name, logic.Int)
}

// table returns the contents of a region for reading at ref. On the way it
// tells the state what is known to be unchanged about ref in every layer the
// region has; that is only stated for the references actually read, since a
// fact about all references at once is beyond the solver.
func (v *fnVerifier) table(sink *state, mem memory, key string, sort logic.Sort, ref *logic.Term) *logic.Term {
	current := mem.region(key, sort)
	if sink == nil {
		return current
	}
	for at := current; ; {
		for at.Op == logic.OpStore {
			at = at.Args[0]
		}
		known := v.layers[at.Name]
		if known == nil {
			break
		}
		note := at.Name + "|" + ref.String()
		if !sink.noted[note] {
			sink.noted[note] = true
			sink.assume(v.unchanged(at, known, ref))
		}
		at = known.prev
	}
	return current
}

// unchanged states what a layer preserves at one reference.
func (v *fnVerifier) unchanged(now *logic.Term, known *layer, ref *logic.Term) *logic.Term {
	existed := logic.Lt(ref, known.bound)
	if !known.rows {
		conditions := []*logic.Term{existed}
		for _, t := range known.targets {
			conditions = append(conditions, logic.Ne(ref, t.ref))
		}
		return logic.Implies(logic.And(conditions...), v.same(logic.Select(now, ref), logic.Select(known.prev, ref)))
	}
	index := v.bound("k")
	var untouched []*logic.Term
	for _, t := range known.targets {
		if t.lo == nil {
			// A map is written as a whole.
			untouched = append(untouched, logic.Ne(ref, t.ref))
			continue
		}
		untouched = append(untouched, logic.Not(logic.And(logic.Eq(ref, t.ref), logic.Le(t.lo, index), logic.Lt(index, t.hi))))
	}
	kept := v.same(logic.Select(logic.Select(now, ref), index), logic.Select(logic.Select(known.prev, ref), index))
	return logic.Implies(existed, logic.Forall(index, logic.Implies(logic.And(untouched...), kept)))
}

// cell reads one leaf of the object at ref.
func (v *fnVerifier) cell(sink *state, mem memory, key string, lf leaf, ref *logic.Term) *logic.Term {
	return logic.Select(v.table(sink, mem, key, logic.SeqOf(lf.sort), ref), ref)
}

// row reads the sequence that one leaf forms over the elements of the
// backing array at ref.
func (v *fnVerifier) row(sink *state, mem memory, key string, lf leaf, ref *logic.Term) *logic.Term {
	return logic.Select(v.table(sink, mem, key, logic.SeqOf(logic.SeqOf(lf.sort)), ref), ref)
}

// member reads field index of a struct value, or of the object a pointer
// refers to. It reports false for a field of a type that is not modelled.
func (v *fnVerifier) member(sink *state, mem memory, cur value, t types.Type, index int) (value, types.Type, bool) {
	object, viaPointer := pointee(t)
	if !viaPointer {
		object = t
	}
	field := object.Underlying().(*types.Struct).Field(index)
	lo, hi, ok := fieldLeaves(object, index)
	if !ok {
		return nil, field.Type(), false
	}
	if !viaPointer {
		return cur[lo:hi], field.Type(), true
	}
	leaves, _ := layoutOf(object)
	result := make(value, 0, hi-lo)
	for _, lf := range leaves[lo:hi] {
		result = append(result, v.cell(sink, mem, typeKey(object)+lf.path, lf, cur[0]))
	}
	v.noteTyped(sink, result, field.Type())
	return result, field.Type(), true
}

// element reads the element at index of a slice. It reports false when the
// element type is not modelled.
func (v *fnVerifier) element(sink *state, mem memory, header value, t types.Type, index *logic.Term) (value, bool) {
	elem := elemType(t)
	leaves, ok := layoutOf(elem)
	result := make(value, 0, len(leaves))
	for _, lf := range leaves {
		row := v.row(sink, mem, "[]"+typeKey(elem)+lf.path, lf, header[0])
		result = append(result, logic.Select(row, logic.Add(header[1], index)))
	}
	if !hasBound(index) {
		v.noteTyped(sink, result, elem)
	}
	return result, ok
}

// noteTyped records, once, what the type of a value read from memory
// guarantees. Everything in memory is a value of its type, whether or not
// the read that found it was a sensible one, so this holds unconditionally.
func (v *fnVerifier) noteTyped(sink *state, val value, t types.Type) {
	if sink == nil || len(val) == 0 {
		return
	}
	fact := v.wellFormed(val, t, sink.brk)
	if note := "typed " + fact.String(); !sink.noted[note] {
		sink.noted[note] = true
		sink.assume(fact)
	}
}

// view returns the elements of a slice as a sequence, which is how an
// annotation sees a slice whose elements are single values.
func (v *fnVerifier) view(sink *state, mem memory, header value, t types.Type) (*logic.Term, bool) {
	// A struct with one field is not a single value: its field has a
	// region of its own.
	elem := elemType(t)
	sort, single := sortOf(elem)
	if !single {
		return nil, false
	}
	row := v.row(sink, mem, "[]"+typeKey(elem), leaf{sort: sort, typ: elem}, header[0])
	return logic.Subseq(row, header[1], logic.Add(header[1], header[2])), true
}

// storeCell writes one leaf of the object at ref.
func (st *state) storeCell(key string, lf leaf, ref, written *logic.Term) {
	st.mem[key] = logic.Store(st.mem.region(key, logic.SeqOf(lf.sort)), ref, written)
}

// storeRow replaces the sequence one leaf forms over the backing array at ref.
func (st *state) storeRow(key string, lf leaf, ref, written *logic.Term) {
	st.mem[key] = logic.Store(st.mem.region(key, logic.SeqOf(logic.SeqOf(lf.sort))), ref, written)
}

// alloc creates a new object or backing array and returns its reference. An
// object of size zero need not be distinct from every other one, so of it
// only this is known: it is not nil.
func (v *fnVerifier) alloc(st *state, sized bool) *logic.Term {
	ref := v.fresh("new", logic.Ref)
	if sized {
		st.assume(logic.Le(st.brk, ref))
		st.brk = logic.Add(ref, logic.IntLit(1))
		return ref
	}
	later := v.fresh("brk", logic.Ref)
	st.assume(logic.And(logic.Lt(logic.IntLit(0), ref), logic.Lt(ref, later), logic.Le(st.brk, later)))
	st.brk = later
	return ref
}

// allocSlice creates a backing array holding the given rows, one for each
// leaf of the element type, and returns a slice of its first length elements.
func (v *fnVerifier) allocSlice(st *state, elem types.Type, rows []*logic.Term, length, capacity *logic.Term) value {
	ref := v.alloc(st, true)
	leaves, _ := layoutOf(elem)
	for i, lf := range leaves {
		st.storeRow("[]"+typeKey(elem)+lf.path, lf, ref, rows[i])
	}
	return value{ref, logic.IntLit(0), length, capacity}
}

// quickSteps bounds a proof whose failure is an ordinary outcome and decides
// nothing by itself, such as whether an append can happen in place.
const quickSteps = 400

// quickly is prove with a small budget.
func (v *fnVerifier) quickly(st *state, guard []*logic.Term, goal *logic.Term) bool {
	opts := solver.Options{Preds: v.res.Preds, MaxSteps: quickSteps}
	return solver.Prove(append(slices.Clip(st.hyps), guard...), goal, opts) == solver.Proved
}

// prove reports whether a goal follows from the facts of a state together
// with the conditions under which the current expression is evaluated.
func (v *fnVerifier) prove(st *state, guard []*logic.Term, goal *logic.Term) bool {
	opts := solver.Options{Preds: v.res.Preds, MaxSteps: v.maxSteps}
	return solver.Prove(append(slices.Clip(st.hyps), guard...), goal, opts) == solver.Proved
}

// checkWrite requires that a write is one the function may make: to an
// object or array created since the function was entered, or to something a
// Modifies clause lists. key names what is written, as a target does; for
// elements, lo and hi bound the stretch of the array. A listed target that no
// write ever needs is reported when the function has been verified, so each
// write records the targets it could not do without.
func (v *fnVerifier) checkWrite(st *state, guard []*logic.Term, key string, ref, lo, hi *logic.Term, pos token.Pos, what string) {
	created := logic.Le(v.entryBrk, ref)
	var candidates []int
	var allowed []*logic.Term
	for i, t := range v.frame {
		if !under(key, t.owner()+t.prefix) || (t.elems && lo == nil) || (!t.elems && lo != nil) {
			continue
		}
		candidates = append(candidates, i)
		if t.elems {
			allowed = append(allowed, logic.And(logic.Eq(ref, t.ref), logic.Le(t.lo, lo), logic.Le(hi, t.hi)))
		} else {
			allowed = append(allowed, logic.Eq(ref, t.ref))
		}
	}
	goal := logic.Or(append([]*logic.Term{created}, allowed...)...)
	if !v.prove(st, guard, goal) {
		for _, i := range candidates {
			v.used[i] = true
		}
		v.report(pos, "%s, which %s may not modify; list it in a //@ Modifies clause", what, v.fn.obj.Name())
		st.assume(logic.Implies(logic.And(guard...), goal))
		return
	}
	// An entry counts as needed unless the write is quickly shown to be
	// allowed without it.
	if len(candidates) == 0 || v.quickly(st, guard, created) {
		return
	}
	for n, i := range candidates {
		others := slices.Delete(slices.Clone(allowed), n, n+1)
		if len(candidates) == 1 || !v.quickly(st, guard, logic.Or(append([]*logic.Term{created}, others...)...)) {
			v.used[i] = true
		}
	}
}

// havoc forgets what a target holds: a call that may write it has run.
// Everything else stays as it was, which is what makes a Modifies clause
// useful to the caller.
func (v *fnVerifier) havoc(st *state, t target) {
	t.regions(func(key string, lf leaf, rows bool) {
		switch {
		case !rows:
			// What the type guarantees of the new value is noted where
			// the value is read.
			st.storeCell(key, lf, t.ref, v.fresh("written", lf.sort))
		case t.lo == nil:
			st.storeRow(key, lf, t.ref, v.fresh("written", logic.SeqOf(lf.sort)))
		default:
			before := logic.Select(st.mem.region(key, logic.SeqOf(logic.SeqOf(lf.sort))), t.ref)
			unknown := v.fresh("written", logic.SeqOf(lf.sort))
			index := v.bound("k")
			outside := logic.Or(logic.Lt(index, t.lo), logic.Le(t.hi, index))
			st.assume(logic.Forall(index, logic.Implies(outside, v.same(logic.Select(unknown, index), logic.Select(before, index)))))
			st.storeRow(key, lf, t.ref, unknown)
		}
	})
	if !t.mapped {
		return
	}
	// Nothing can be put into the nil map, so if that is what the target
	// is, it is as empty afterwards as it was.
	index := v.bound("k")
	has := logic.Select(st.mem.region(t.owner()+hasLeaf.path, logic.SeqOf(logic.SeqOf(logic.Bool))), t.ref)
	count := logic.Select(st.mem.region(t.owner()+countLeaf.path, logic.SeqOf(logic.Int)), t.ref)
	empty := logic.And(logic.Eq(count, logic.IntLit(0)), logic.Forall(index, logic.Not(logic.Select(has, index))))
	st.assume(logic.Implies(logic.Eq(t.ref, logic.RefLit(0)), empty))
}

// separate states that two slices share no element, counting the capacity
// beyond their lengths: they refer to different arrays, or to stretches of
// one array that do not meet, or one of them has no capacity at all.
func separate(a, b value) *logic.Term {
	zero := logic.IntLit(0)
	return logic.Or(
		logic.Lt(a[0], b[0]), logic.Lt(b[0], a[0]),
		logic.Le(logic.Add(a[1], a[3]), b[1]), logic.Le(logic.Add(b[1], b[3]), a[1]),
		logic.Le(a[3], zero), logic.Le(b[3], zero),
	)
}

// overlapping lists the pairs of slice parameters with the same element type,
// which a function may assume, and its callers must show, to be separate.
func overlapping(fn *funcInfo) [][2]*types.Var {
	var pairs [][2]*types.Var
	for i, first := range fn.params {
		for _, second := range fn.params[i+1:] {
			if isSlice(first.Type()) && isSlice(second.Type()) && types.Identical(elemType(first.Type()), elemType(second.Type())) {
				pairs = append(pairs, [2]*types.Var{first, second})
			}
		}
	}
	return pairs
}

// describe names a parameter in a diagnostic.
func describe(param *types.Var) string {
	if param.Name() == "" || param.Name() == "_" {
		return fmt.Sprintf("an unnamed %s", param.Type())
	}
	return param.Name()
}
