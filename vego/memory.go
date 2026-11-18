package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"maps"
	"slices"

	"github.com/spachava753/laas/vego/internal/logic"
	"github.com/spachava753/laas/vego/internal/solver"
)

// memory holds what pointers, slices, and maps refer to. It is divided into
// regions: one for each field of each struct type, one for each kind of
// value a slice can hold that is not a struct, and a few for each map type.
// A region holds, for every allocation, a sequence indexed by position: the
// byte offset of a field, or the number of an element. A region that is
// absent has not changed since the function was entered.
//
// A struct that is part of something larger, as an element of a slice or a
// field of another struct, lies in the allocation of what it is part of, at
// its offset there. Its fields are found in the same regions whichever way
// they are reached, so a write through a pointer into a slice is seen
// through the slice.
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
	// chosen holds the branches taken to get here, whose conditions are
	// among hyps too.
	chosen []choice
	// noted holds the facts about unchanged memory already added to hyps.
	noted map[string]bool
	// deferred holds the calls that defer statements have put off until the
	// function returns, in the order the statements ran.
	deferred []deferredCall
}

// deferredCall is a call that a defer statement put off: the call, the
// contract of what it calls, and the receiver and arguments as they were
// when the defer statement ran.
type deferredCall struct {
	call *ast.CallExpr
	fn   *funcInfo
	args map[*types.Var]value
}

func (st *state) clone() *state {
	return &state{
		vals: maps.Clone(st.vals), mem: maps.Clone(st.mem), brk: st.brk,
		hyps: slices.Clone(st.hyps), chosen: slices.Clone(st.chosen), noted: maps.Clone(st.noted),
		deferred: slices.Clone(st.deferred),
	}
}

// choice is a branch that execution took: its condition, and how many facts
// were known before it was taken.
type choice struct {
	cond   *logic.Term
	before int
}

// decide records that execution took the branch with the given condition.
func (st *state) decide(cond *logic.Term) {
	st.chosen = append(st.chosen, choice{cond, len(st.hyps)})
	st.assume(cond)
}

func (st *state) assume(fact *logic.Term) {
	if fact.Op != logic.OpTrue {
		st.hyps = append(st.hyps, fact)
	}
}

// layer records how a region was forgotten at the head of a loop: the region
// got a new unknown value, of which only this is known: what existed below
// bound and lies in none of the targets is as it was in prev.
type layer struct {
	prev    *logic.Term
	bound   *logic.Term
	targets []target
	// flat is set for the region that holds one number for each map: how
	// many keys it has. Every other region holds a sequence per reference.
	flat bool
}

// target is a piece of memory that may be written: a stretch of positions in
// one allocation, in some regions, or one map.
type target struct {
	// cells are the regions the target reaches into. For a single struct
	// they give the position of each leaf from at; for the elements of a
	// slice the positions repeat with every element.
	cells []cell
	ref   *logic.Term
	// lo and hi bound the positions; they are nil for a map.
	lo, hi *logic.Term
	// single is set when the target is one struct value at lo, whose leaves
	// can be named one by one.
	single bool
	// elem is set for the elements of a slice, and mapType for a map.
	elem    types.Type
	mapType types.Type
	text    string // how the Modifies clause spells it
	clause  *clause
	// param is set when the object or array is the very one that this
	// parameter holds.
	param *types.Var
}

// regions calls visit for every region the target reaches into, with the
// sort of what the region holds at one position.
func (t target) regions(visit func(key string, sort logic.Sort)) {
	if t.mapType != nil {
		_, elem := mapParts(t.mapType)
		leaves, _ := layoutOf(elem)
		visit(mapOwner(t.mapType)+countLeaf.path, countLeaf.sort)
		visit(mapOwner(t.mapType)+hasLeaf.path, hasLeaf.sort)
		for _, lf := range leaves {
			visit(mapOwner(t.mapType)+"#val"+lf.path, lf.sort)
		}
		return
	}
	seen := map[string]bool{}
	for _, c := range t.cells {
		if !seen[c.key] {
			seen[c.key] = true
			visit(c.key, c.sort)
		}
	}
}

// reaches reports whether the target reaches into every one of the regions.
func (t target) reaches(keys []string) bool {
	found := map[string]bool{}
	t.regions(func(key string, _ logic.Sort) { found[key] = true })
	return !slices.ContainsFunc(keys, func(key string) bool { return !found[key] })
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
// region has; that is only stated for the references actually read. A fact
// about all references at once would be a quantifier in every problem that
// reads memory, which Z3 decides less often and slows Z3 down, while facts
// about the references read keep such problems free of quantifiers.
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
	if known.flat {
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

// cell reads the one number a flat region has for a reference.
func (v *fnVerifier) cell(sink *state, mem memory, key string, lf leaf, ref *logic.Term) *logic.Term {
	return logic.Select(v.table(sink, mem, key, logic.SeqOf(lf.sort), ref), ref)
}

// row reads the sequence a region has for a reference.
func (v *fnVerifier) row(sink *state, mem memory, key string, sort logic.Sort, ref *logic.Term) *logic.Term {
	return logic.Select(v.table(sink, mem, key, logic.SeqOf(logic.SeqOf(sort)), ref), ref)
}

// fetch reads the leaves with the given cells of a value stored at a
// position of an allocation.
func (v *fnVerifier) fetch(sink *state, mem memory, cells []cell, ref, at *logic.Term) value {
	val := make(value, len(cells))
	for i, c := range cells {
		val[i] = logic.Select(v.row(sink, mem, c.key, c.sort, ref), logic.Add(at, logic.IntLit(c.off)))
	}
	return val
}

// put writes the leaves with the given cells of a value stored at a position
// of an allocation.
func (v *fnVerifier) put(st *state, cells []cell, ref, at *logic.Term, val value) {
	for i, c := range cells {
		row := logic.Select(st.mem.region(c.key, logic.SeqOf(logic.SeqOf(c.sort))), ref)
		st.storeRow(c.key, c.sort, ref, logic.Store(row, logic.Add(at, logic.IntLit(c.off)), val[i]))
	}
}

// member reads field index of a struct value, or of the struct a pointer
// points to. It reports false for a field of a type that is not modelled.
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
	result := v.fetch(sink, mem, v.cellsOf(object)[lo:hi], cur[0], cur[1])
	v.noteTyped(sink, result, field.Type())
	return result, field.Type(), true
}

// elementAt returns the position of the element at index of a slice.
func (v *fnVerifier) elementAt(header value, t types.Type, index *logic.Term) *logic.Term {
	return logic.Add(header[1], logic.Mul(index, logic.IntLit(v.span(elemType(t)))))
}

// element reads the element at index of a slice. It reports false when the
// element type is not modelled.
func (v *fnVerifier) element(sink *state, mem memory, header value, t types.Type, index *logic.Term) (value, bool) {
	elem := elemType(t)
	_, ok := layoutOf(elem)
	result := v.fetch(sink, mem, v.cellsOf(elem), header[0], v.elementAt(header, t, index))
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
	// position of its own.
	elem := elemType(t)
	if _, single := sortOf(elem); !single {
		return nil, false
	}
	only := v.cellsOf(elem)[0]
	row := v.row(sink, mem, only.key, only.sort, header[0])
	return logic.Subseq(row, header[1], logic.Add(header[1], header[2])), true
}

// storeCell writes the one number a flat region has for a reference.
func (st *state) storeCell(key string, lf leaf, ref, written *logic.Term) {
	st.mem[key] = logic.Store(st.mem.region(key, logic.SeqOf(lf.sort)), ref, written)
}

// storeRow replaces the sequence a region has for a reference.
func (st *state) storeRow(key string, sort logic.Sort, ref, written *logic.Term) {
	st.mem[key] = logic.Store(st.mem.region(key, logic.SeqOf(logic.SeqOf(sort))), ref, written)
}

// alloc creates a new allocation and returns its reference. One of size zero
// need not be distinct from every other one, so of it only this is known: it
// is not nil.
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

// allocSlice creates an array of the given element type whose every position
// holds zero values, puts the given elements at its start, and returns a
// slice of the array with the given length and capacity.
func (v *fnVerifier) allocSlice(st *state, elem types.Type, elements []value, length, capacity *logic.Term) value {
	// An array of elements without size takes no memory and need not be
	// apart from any other.
	ref := v.alloc(st, v.pass.TypesSizes.Sizeof(elem) > 0)
	cells, leaves := v.cellsOf(elem), mustLayout(elem)
	zeroed := map[string]bool{}
	for i, c := range cells {
		if !zeroed[c.key] {
			zeroed[c.key] = true
			st.storeRow(c.key, c.sort, ref, logic.Fill(logic.IntLit(0), zeroLeaf(leaves[i])))
		}
	}
	for i, element := range elements {
		v.put(st, cells, ref, logic.IntLit(int64(i)*v.span(elem)), element)
	}
	return value{ref, logic.IntLit(0), length, capacity}
}

// mustLayout returns the leaves of a type that is known to be modelled.
func mustLayout(t types.Type) []leaf {
	leaves, _ := layoutOf(t)
	return leaves
}

// stretch is the part of a write, or of a target, that lies in one region:
// the positions from lo up to hi, which are nil for a map.
type stretch struct {
	key    string
	lo, hi *logic.Term
	// one is set when the stretch is the single position lo.
	one bool
}

// written describes a write for the check against the frame: the allocation
// or the map, and what it writes in each region.
type written struct {
	ref   *logic.Term
	parts []stretch
}

// stretches returns what a target covers in each region it reaches into.
// For a single struct value that is exactly the positions of its leaves,
// one stretch for each.
func (t target) stretches() []stretch {
	if !t.single {
		var parts []stretch
		t.regions(func(key string, _ logic.Sort) { parts = append(parts, stretch{key: key, lo: t.lo, hi: t.hi}) })
		return parts
	}
	return stretchesOf(t.cells, t.lo)
}

// stretchesOf returns what the cells of a value stored at a position cover:
// one position for each cell. Two cells in one region, such as the same
// field of two structs that lie side by side, stay two stretches, since
// what lies between them is not part of the value.
func stretchesOf(cells []cell, at *logic.Term) []stretch {
	parts := make([]stretch, len(cells))
	for i, c := range cells {
		parts[i] = stretch{c.key, logic.Add(at, logic.IntLit(c.off)), logic.Add(at, logic.IntLit(c.off+1)), true}
	}
	return parts
}

// checkWrite requires that a write is one the function may make: to an
// allocation or a map created since the function was entered, or to
// something a Modifies clause lists. A listed target that no write ever
// needs is reported when the function has been verified, so each write
// records the targets it could not do without.
//
// Every position a write reaches must be covered by some listed target,
// which need not be the same for all of them: a write of a whole struct is
// allowed when each of its fields is listed, and a write of a run of
// elements when each element is. Nothing can be written through a nil
// pointer, a nil slice, or a nil map, so a call that may modify what one of
// them refers to changes nothing there and needs no permission for it.
func (v *fnVerifier) checkWrite(st *state, guard []*logic.Term, w written, pos token.Pos, what string) {
	if len(w.parts) == 0 {
		return
	}
	created := logic.Or(logic.Le(v.entryBrk, w.ref), logic.Eq(w.ref, logic.RefLit(0)))
	covers := make([][]stretch, len(v.frame))
	var candidates []int
	for i, t := range v.frame {
		covers[i] = t.stretches()
		if slices.ContainsFunc(covers[i], func(c stretch) bool {
			return slices.ContainsFunc(w.parts, func(part stretch) bool { return part.key == c.key })
		}) {
			candidates = append(candidates, i)
		}
	}
	// allowed states that the write is covered without the target left out.
	allowed := func(without int) *logic.Term {
		whole := []*logic.Term{}
		for _, part := range w.parts {
			// A part of one position is covered when that position is; a
			// longer one when every position in it is.
			position, ranged := part.lo, part.lo != nil && !part.one
			if ranged {
				position = v.bound("k")
			}
			var by []*logic.Term
			for _, i := range candidates {
				for _, c := range covers[i] {
					switch {
					case i == without || c.key != part.key || (c.lo == nil) != (part.lo == nil):
					case c.lo == nil:
						by = append(by, logic.Eq(w.ref, v.frame[i].ref))
					default:
						by = append(by, logic.And(logic.Eq(w.ref, v.frame[i].ref), logic.Le(c.lo, position), logic.Lt(position, c.hi)))
					}
				}
			}
			covered := logic.Or(by...)
			if ranged {
				inside := logic.And(logic.Le(part.lo, position), logic.Lt(position, part.hi))
				covered = logic.Forall(position, logic.Implies(inside, covered))
			}
			whole = append(whole, covered)
		}
		return logic.Or(created, logic.And(whole...))
	}
	goal := allowed(-1)
	if result := v.attempt(st, guard, goal); result != solver.Proved {
		for _, i := range candidates {
			v.used[i] = true
		}
		if len(candidates) == 0 {
			v.report(pos, "%s, which %s may not modify; list it in a // @Modifies clause%s", what, v.fn.obj.Name(), limitNote(result))
		} else {
			// Something of the kind is listed, so telling the reader to
			// list it would send them in a circle.
			v.report(pos, "%s, which %s may not modify: nothing its // @Modifies clauses list is known to cover it; "+
				"a clause covers what its path referred to when %s was called%s", what, v.fn.obj.Name(), v.fn.obj.Name(), limitNote(result))
		}
		st.assume(logic.Implies(logic.And(guard...), goal))
		return
	}
	// An entry counts as needed unless the write is quickly shown to be
	// allowed without it.
	if len(candidates) == 0 || v.quickly(st, guard, created) {
		return
	}
	for _, i := range candidates {
		if !v.quickly(st, guard, allowed(i)) {
			v.used[i] = true
		}
	}
}

// reach describes a target as a write of everything it covers.
func (t target) reach() written {
	return written{ref: t.ref, parts: t.stretches()}
}

// havoc forgets what a target holds: a call that may write it has run.
// Everything else stays as it was, which is what makes a Modifies clause
// useful to the caller.
func (v *fnVerifier) havoc(st *state, t target) {
	switch {
	case t.mapType != nil:
		owner := mapOwner(t.mapType)
		t.regions(func(key string, sort logic.Sort) {
			if key == owner+countLeaf.path {
				st.storeCell(key, countLeaf, t.ref, v.fresh("written", sort))
				return
			}
			st.storeRow(key, sort, t.ref, v.fresh("written", logic.SeqOf(sort)))
		})
		// Nothing can be put into the nil map, so if that is what the
		// target is, it is as empty afterwards as it was.
		index := v.bound("k")
		has := logic.Select(st.mem.region(owner+hasLeaf.path, logic.SeqOf(logic.SeqOf(logic.Bool))), t.ref)
		count := logic.Select(st.mem.region(owner+countLeaf.path, logic.SeqOf(logic.Int)), t.ref)
		empty := logic.And(logic.Eq(count, logic.IntLit(0)), logic.Forall(index, logic.Not(logic.Select(has, index))))
		st.assume(logic.Implies(logic.Eq(t.ref, logic.RefLit(0)), empty))
	case t.single:
		// What the types guarantee of the new values is noted where they
		// are read.
		unknown := make(value, len(t.cells))
		for i, c := range t.cells {
			unknown[i] = v.fresh("written", c.sort)
		}
		v.put(st, t.cells, t.ref, t.lo, unknown)
	default:
		t.regions(func(key string, sort logic.Sort) {
			before := logic.Select(st.mem.region(key, logic.SeqOf(logic.SeqOf(sort))), t.ref)
			unknown := v.fresh("written", logic.SeqOf(sort))
			index := v.bound("k")
			outside := logic.Or(logic.Lt(index, t.lo), logic.Le(t.hi, index))
			st.assume(logic.Forall(index, logic.Implies(outside, v.same(logic.Select(unknown, index), logic.Select(before, index)))))
			st.storeRow(key, sort, t.ref, unknown)
		})
	}
}

// extent returns the positions a slice may reach, from its start up to the
// end of its capacity, or the positions of the struct a pointer points to.
func (pv *pkgVerifier) extent(val value, t types.Type) (lo, hi *logic.Term) {
	if object, isPointer := pointee(t); isPointer {
		return val[1], logic.Add(val[1], logic.IntLit(pv.span(object)))
	}
	return val[1], logic.Add(val[1], logic.Mul(val[3], logic.IntLit(pv.span(elemType(t)))))
}

// separate states that two slices of one type share no element, counting
// the capacity beyond their lengths: they lie in different arrays, or in
// stretches of one array that do not meet, or one of them has no capacity.
func (pv *pkgVerifier) separate(a, b value, t types.Type) *logic.Term {
	zero := logic.IntLit(0)
	_, endA := pv.extent(a, t)
	_, endB := pv.extent(b, t)
	return logic.Or(
		logic.Lt(a[0], b[0]), logic.Lt(b[0], a[0]),
		logic.Le(endA, b[1]), logic.Le(endB, a[1]),
		logic.Le(a[3], zero), logic.Le(b[3], zero),
	)
}

// overlapping lists the pairs of slice parameters with the same element type,
// which a function may assume, and its callers must show, to be separate.
func overlapping(fn *funcInfo) [][2]*types.Var {
	var pairs [][2]*types.Var
	for i, first := range fn.params {
		for _, second := range fn.params[i+1:] {
			if isSlice(first.Type()) && isSlice(second.Type()) && typeKey(elemType(first.Type())) == typeKey(elemType(second.Type())) {
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
