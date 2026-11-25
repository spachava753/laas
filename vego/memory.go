package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"maps"
	"slices"
	"strings"

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
	if current := m.inEpoch(key, sort); current != nil {
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
	// snapshots holds the values of the Snapshot annotations taken on the
	// path; see takeSnapshot. A map is never changed once a state holds it.
	snapshots map[*clause]*logic.Term
	// visited holds, for each Visited clause of a range over a map that
	// the path is inside, where the range has come to; see visited.go. A
	// map is never changed once a state holds it.
	visited map[*clause]*visitedSet
	// collecting is set for a state that only gathers the facts of reads
	// under a quantifier, which may mention its variables; the quantifier
	// takes them as premises and states them on their own (see
	// specEnv.OpenBound).
	collecting bool
	// kept holds where the invariants of values held on this path: each
	// entry says that a struct's invariants held of a value in a memory
	// of the path, so that a later goal can be proved by showing that
	// nothing they read has changed since (frames.go).
	kept []*keptEntry
	// writes logs the statements after which memory changed on this path,
	// for the message of a frame that did not hold (frames.go).
	writes []loggedWrite
	// loops holds the heads of the loops this path is inside or has left,
	// where their invariants were assumed (frames.go).
	loops []*loopKept
}

// deferredCall is a call that a defer statement put off: the call, the
// contract of what it calls, and the receiver and arguments as they were
// when the defer statement ran. For a function literal, lit is the literal
// and litArgs its arguments, in order.
type deferredCall struct {
	call *ast.CallExpr
	fn   *funcInfo
	args map[*types.Var]value
	// runs are the methods that formatting what the call is given calls,
	// with the values given at the defer statement; see checkFormatRuns.
	runs []fmtRun
	// held holds the values of what it formats at the defer statement,
	// for the bound on what it builds when it runs.
	held    map[ast.Expr]value
	lit     *ast.FuncLit
	litArgs []value
	// writer and write are set for a call that printedInto names, with the
	// writer evaluated as it is; see prints.go.
	writer ast.Expr
	write  *funcInfo
}

func (st *state) clone() *state {
	return &state{
		vals: maps.Clone(st.vals), mem: maps.Clone(st.mem), brk: st.brk,
		hyps: slices.Clone(st.hyps), chosen: slices.Clone(st.chosen), noted: maps.Clone(st.noted),
		deferred: slices.Clone(st.deferred), snapshots: st.snapshots, visited: st.visited,
		kept: slices.Clip(st.kept), writes: slices.Clip(st.writes), loops: slices.Clip(st.loops),
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
	// key is the region the layer is of.
	key string
	// flat is set for the region that holds one number for each map: how
	// many keys it has. Every other region holds a sequence per reference.
	flat bool
	// growth is set for a layer of the footprint region: every allocation
	// below bound keeps its cells, unless skipped holds, and every cell lies
	// below after, once that is known; see grow.
	growth  bool
	skipped *logic.Term
	after   *logic.Term
	// apart, when not nil, is set for the growth layer of a call that
	// writes no footprint (GR, frames.go): the row of a home that existed
	// before the call keeps its cells, new allocations' included, unless a
	// cell of one of these targets lay in it before the call.
	apart []target
	// emptied is set for a layer of the footprint region that defines the
	// row of one new home, as a conversion makes it, and keeps every other
	// row. defines says which cells the row holds, with the facts that
	// reading other rows needs; nil, the row is empty, as for a value whose
	// methods write nothing behind their receiver.
	emptied *logic.Term
	defines func(alloc, pos *logic.Term) (*logic.Term, []*logic.Term)
	// follows is set for a layer of the footprint region that a store into
	// an owned field leaves (step 4 of ownership in source): a row that
	// holds the owned field's cell now holds what the stored value's
	// structural footprint holds too, and every row keeps its cells.
	follows *followLayer
}

// followLayer is what a store into an owned field adds to the rows that
// hold the field's cell.
type followLayer struct {
	ref, pos *logic.Term
	stored   func(alloc, pos *logic.Term) (*logic.Term, []*logic.Term)
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
	// can be named one by one. base, when set, is the struct value the
	// target lies in, for the fact between struct values: the struct a
	// pointer points to, or the one a path to some of its fields went
	// through.
	single bool
	base   *structValue
	// elem is set for the elements of a slice, and mapType for a map. key
	// is set for one entry of a map: the number of its key.
	elem    types.Type
	mapType types.Type
	key     *logic.Term
	text    string // how the Modifies clause spells it
	clause  *clause
	// param is set when the object or array is the very one that this
	// parameter holds.
	param *types.Var
	// row is set when the target is every state of an interface value:
	// the whole row of its key in the region of states, which ref is.
	// lo and hi are nil, as for a map. holder is set to the cells of the
	// interface value when it lies in memory, which the target does not
	// cover; see checkWriteOr.
	row    bool
	holder []cell
	// fp is set when the target is the footprint of an interface value:
	// every cell that rows holds at the home ref, in every region; see
	// footprint.go. skipped, when not nil, is when the call that writes it
	// did not run.
	fp      bool
	rows    *logic.Term
	skipped *logic.Term
	// skey is, for the footprint of an interface value, the key of the
	// value's states, whose row the footprint's epoch keeps; and, for an
	// entry that covers both, the row of states that targets spreads into
	// a target of its own (S0b of F34).
	skey *logic.Term
	// besideFootprint is set for the states of an entry whose footprint is
	// a target of its own, the one before it in the list.
	besideFootprint bool
	// besideStruct is set for the states of what a pointer points to, of
	// an entry whose struct is the target before it (A5 of S0b of F34).
	besideStruct bool
	// owned holds, for a struct that owns some of its fields, a target for
	// what each owned field refers to; targets spreads them into the list.
	// owner and ownerType are the pointer to that struct and its type.
	owned     []target
	owner     value
	ownerType types.Type
	// part is set for a target that an owner's clause gives for what one
	// of its owned fields refers to, and ownerParam is then the parameter
	// the clause names, when it names one.
	part       bool
	ownerParam *types.Var
	// sourcePart is set for a part an owned field of a declaration in
	// source gives, which C3 separates (owns.go, separateParts); what a
	// shipped owner owns keeps part 1's separation.
	sourcePart bool
	// also holds, for an entry that names an assigned package-level
	// variable, the target of what its value refers to, beside its
	// storage, which targets spreads into the list.
	also []target
	// fromVar is set on the footprint of what an interface variable that
	// an entry names by itself holds: the variable whose value it is. A
	// declared function assumes what its parameters reach apart from it
	// (enterReaches), and a caller proves it (checkReachedApart).
	fromVar *types.Var
	// reached is set for a target that code of the package a call may run
	// writes, which no Modifies clause of the callee lists (F7).
	reached bool
	// mod is the index of the Modifies clause the target comes from: a
	// clause that names an owner gives a target for the struct and one
	// for what each owned field refers to.
	mod int
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
	return v.tableAt(sink, mem, key, sort, ref, nil)
}

// tableAt is table for a read of one position of the row at ref, when
// position is not nil: what a layer keeps is then stated of that cell
// alone, with no quantifier.
func (v *fnVerifier) tableAt(sink *state, mem memory, key string, sort logic.Sort, ref, position *logic.Term) *logic.Term {
	// While an evaluation unit is open, every read of memory must be a
	// recorded read or a quiet one, whether or not it tells a state what
	// it learns; a read made any other way is one whose order has not been
	// looked at.
	if u := v.unit; u != nil && u.recording == 0 && u.quiet == 0 {
		panic("vego: internal error: memory is read without being recorded in the evaluation unit")
	}
	// What a package-level variable refers to that nothing writes and no
	// other reference reaches is the same in every state; see readOnlyHere.
	if ref != nil && ref.Op == logic.OpConst {
		if variable, ok := v.readOnlyRefs[ref.Name]; ok {
			return readOnlyRegion(variable, key, sort)
		}
	}
	current := mem.region(key, sort)
	if sink == nil {
		return current
	}
	// A region is a chain of writes on a region a loop forgot or a join
	// made, or on the region on entry. Every such region on the way is
	// looked at once: what a layer keeps, and what a join chose, are true
	// at the reference read.
	seen := map[string]bool{}
	for pending := []*logic.Term{current}; len(pending) > 0; {
		at := pending[len(pending)-1]
		pending = pending[:len(pending)-1]
		for at.Op == logic.OpStore || at.Op == logic.OpWrite || at.Op == logic.OpSpliceAt {
			at = at.Args[0]
		}
		if seen[at.Name] {
			continue
		}
		seen[at.Name] = true
		v.materialize(at.Name, at.Sort)
		note := at.Name + "|" + ref.String()
		// What gathers the facts of reads under a quantifier wants only
		// what a write through a footprint keeps; the other layers and
		// joins were never stated under a quantifier and are not now.
		if sink.collecting {
			if known := v.layers[at.Name]; known != nil {
				if hasFootprintTarget(known.targets) || hasSourcePart(known.targets) {
					v.distinctStructs(sink, known, key, ref, position)
				}
				if (hasFootprintTarget(known.targets) || hasSourcePart(known.targets)) && !sink.noted[note] {
					sink.noted[note] = true
					sink.assume(v.unchanged(sink, at, known, ref, nil))
				}
				pending = append(pending, known.prev)
			}
			if joined := v.joins[at.Name]; joined != nil {
				pending = append(pending, joined.alternatives...)
			}
			continue
		}
		if known := v.layers[at.Name]; known != nil {
			v.distinctStructs(sink, known, key, ref, position)
			cellNote := note
			if position != nil && !known.flat && !hasBound(position) {
				cellNote = note + "@" + position.String()
			} else {
				position = nil
			}
			if !sink.noted[note] && !sink.noted[cellNote] {
				sink.noted[cellNote] = true
				sink.assume(v.unchanged(sink, at, known, ref, position))
			}
			pending = append(pending, known.prev)
		}
		if joined := v.joins[at.Name]; joined != nil {
			if !sink.noted[note] {
				sink.noted[note] = true
				fact := v.joinedAt(at, joined, ref)
				sink.assume(fact)
				// What a frame reads is a premise of its own question
				// only, and no failure is tied through it.
				if v.frameNames == nil {
					v.forwards[joined.forward].facts = append(v.forwards[joined.forward].facts, fact)
				}
			}
			pending = append(pending, joined.alternatives...)
		}
	}
	return current
}

// unchanged states what a layer preserves at one reference.
func (v *fnVerifier) unchanged(sink *state, now *logic.Term, known *layer, ref, position *logic.Term) *logic.Term {
	if known.growth {
		panic("vego: internal error: the footprint region is read through table")
	}
	existed := logic.Lt(ref, known.bound)
	var instances []*logic.Term
	if known.flat {
		conditions := []*logic.Term{existed}
		for _, t := range known.targets {
			if t.fp {
				outside, facts := v.outsideFootprint(t, known.key, ref, logic.IntLit(0))
				conditions = append(conditions, outside)
				instances = append(instances, facts...)
				continue
			}
			if t.row && known.key != stateRegion {
				// A row of states lies in the region of states alone.
				continue
			}
			conditions = append(conditions, logic.Ne(ref, t.ref))
		}
		fact := logic.Implies(logic.And(conditions...), v.same(logic.Select(now, ref), logic.Select(known.prev, ref)))
		if (hasFootprintTarget(known.targets) || hasSourcePart(known.targets)) {
			fact = logic.And(fact, logic.And(instances...), v.reachApart(ref, logic.IntLit(0)))
		}
		return fact
	}
	index := position
	if index == nil {
		index = v.bound("k")
	}
	var untouched []*logic.Term
	for _, t := range known.targets {
		switch {
		case t.fp:
			position := index
			if isMapRegion(known.key) {
				position = logic.IntLit(0)
			}
			outside, facts := v.outsideFootprint(t, known.key, ref, position)
			untouched = append(untouched, outside)
			instances = append(instances, facts...)
		case t.row && known.key != stateRegion:
			// A row of states lies in the region of states alone (S0b of
			// F34, where a row's key stopped being a home).
		case t.lo == nil:
			// A map is written as a whole.
			untouched = append(untouched, logic.Ne(ref, t.ref))
		case t.single:
			// One struct value, or some of its fields: what may change is
			// the position of each of its cells in this region, as havoc
			// writes them, and nothing between them.
			for _, c := range t.cells {
				if c.key == known.key {
					at := logic.Add(t.lo, logic.IntLit(c.off))
					untouched = append(untouched, logic.Not(logic.And(logic.Eq(ref, t.ref), logic.Le(at, index), logic.Lt(index, logic.Add(at, logic.IntLit(1))))))
				}
			}
		default:
			untouched = append(untouched, logic.Not(logic.And(logic.Eq(ref, t.ref), logic.Le(t.lo, index), logic.Lt(index, t.hi))))
		}
	}
	kept := v.same(logic.Select(logic.Select(now, ref), index), logic.Select(logic.Select(known.prev, ref), index))
	body := logic.Implies(logic.And(untouched...), kept)
	if (hasFootprintTarget(known.targets) || hasSourcePart(known.targets)) {
		position := index
		if isMapRegion(known.key) {
			position = logic.IntLit(0)
		}
		// What the footprints and the separation say of the cell is true
		// of every cell, so it stands beside the implication.
		body = logic.And(logic.And(instances...), v.reachApart(ref, position), body)
	}
	if index == position {
		return logic.Implies(existed, body)
	}
	return logic.Implies(existed, logic.Forall(index, body))
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
	return v.fetchIn(sink, mem, cells, ref, at, nil)
}

// fetchIn is fetch for cells of a struct of type base at ref and at, when
// base is not nil: each read then also states, against the struct targets
// of the layers it meets and the structs the function converted, that two
// struct values of one type are one or lie apart (distinctStructs).
func (v *fnVerifier) fetchIn(sink *state, mem memory, cells []cell, ref, at *logic.Term, base types.Type) value {
	if base != nil {
		saved := v.readBase
		v.readBase = &structValue{t: base, ref: ref, at: at}
		defer func() { v.readBase = saved }()
		v.noteStruct(sink, *v.readBase)
	}
	val := make(value, len(cells))
	for i, c := range cells {
		position := logic.Add(at, logic.IntLit(c.off))
		val[i] = logic.Select(logic.Select(v.tableAt(sink, mem, c.key, logic.SeqOf(logic.SeqOf(c.sort)), ref, position), ref), position)
	}
	return val
}

// put writes the leaves with the given cells of a value stored at a position
// of an allocation.
func (v *fnVerifier) put(st *state, cells []cell, ref, at *logic.Term, val value) {
	checkGrowth(val)
	for i, c := range cells {
		v.writeAt(st, c.key, c.sort, ref, logic.Add(at, logic.IntLit(c.off)), val[i])
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
	result := v.fetchIn(sink, mem, v.cellsOf(object)[lo:hi], cur[0], cur[1], object)
	v.noteTyped(sink, result, field.Type())
	v.noteReached(sink, v.cellsOf(object)[lo:hi], cur[0], cur[1], field.Type(), object)
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
	var base types.Type
	if _, isStruct := elem.Underlying().(*types.Struct); isStruct {
		base = elem
	}
	result := v.fetchIn(sink, mem, v.cellsOf(elem), header[0], v.elementAt(header, t, index), base)
	// What the types say of the element, and what the other parameters
	// reach from it, are stated of one element; under a quantifier they
	// go to what gathers its facts.
	notes := sink
	if hasBound(index) && (sink == nil || !sink.collecting) {
		notes = v.boundSink
	}
	if notes != nil {
		v.noteTyped(notes, result, elem)
		v.noteReached(notes, v.cellsOf(elem), header[0], v.elementAt(header, t, index), elem, t)
	}
	return result, ok
}

// typedRead is a value read from memory with its type; see canBeMet.
type typedRead struct {
	val value
	t   types.Type
}

// noteTyped records, once, what the type of a value read from memory
// guarantees. Everything in memory is a value of its type, whether or not
// the read that found it was a sensible one, so this holds unconditionally.
func (v *fnVerifier) noteTyped(sink *state, val value, t types.Type) {
	// Under a quantifier only what a value that refers to memory is
	// matters to what a write through a footprint keeps; the range of a
	// number read there is what quantified facts said before.
	if sink == nil || len(val) == 0 || sink.collecting && !holdsMemory(t) {
		return
	}
	fact := v.wellFormed(val, t, sink.brk)
	if note := "typed " + fact.String(); !sink.noted[note] {
		sink.noted[note] = true
		sink.assume(fact)
		// A read under a quantifier is restated nowhere else: its value
		// mentions the quantifier's variable.
		if v.typedReads != nil && !sink.collecting {
			*v.typedReads = append(*v.typedReads, typedRead{val: val, t: t})
		}
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

// writeAt replaces one position of the sequence a region has for a
// reference. What is written, and where, may have been read from the same
// region; see apart.
func (v *fnVerifier) writeAt(st *state, key string, sort logic.Sort, ref, at, written *logic.Term) {
	table := logic.SeqOf(logic.SeqOf(sort))
	ref, at, written = v.apart(st, ref, table), v.apart(st, at, table), v.apart(st, written, table)
	st.mem[key] = logic.Write(st.mem.region(key, table), ref, at, written)
}

// apart returns a term that stands for t and holds no region of the given
// sort: t itself, or t named. A write puts what it writes, and where, into
// the region it writes; if those held the region, as A[0] = A[1] does, a
// run of such writes would double the region at every step.
func (v *fnVerifier) apart(st *state, t *logic.Term, region logic.Sort) *logic.Term {
	seen := map[*logic.Term]bool{}
	var holds func(t *logic.Term) bool
	holds = func(t *logic.Term) bool {
		if seen[t] {
			return false
		}
		seen[t] = true
		if t.Sort == region {
			return true
		}
		return slices.ContainsFunc(t.Args, holds)
	}
	if !holds(t) {
		return t
	}
	return v.named(st, "written", t)
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
	v.noteBorn(st, ref, rowKeys(cells))
	return value{ref, logic.IntLit(0), length, capacity}
}

// rowKeys returns the regions that the cells lie in, with the sort of each.
func rowKeys(cells []cell) map[string]logic.Sort {
	keys := map[string]logic.Sort{}
	for _, c := range cells {
		keys[c.key] = logic.SeqOf(logic.SeqOf(c.sort))
	}
	return keys
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
	// entry is set for one entry of a map, which lo and hi are nil for: the
	// number of its key.
	entry *logic.Term
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
		t.regions(func(key string, _ logic.Sort) { parts = append(parts, stretch{key: key, lo: t.lo, hi: t.hi, entry: t.key}) })
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
		parts[i] = stretch{key: c.key, lo: logic.Add(at, logic.IntLit(c.off)), hi: logic.Add(at, logic.IntLit(c.off+1)), one: true}
	}
	return parts
}

// returned is a result of a call: the contract called and which result.
type returned struct {
	fn     *funcInfo
	result int
	// call is how the call is written, for one through a function value
	// or an interface value.
	call string
	// within is, when the contract says that the result lies within a
	// parameter, as within(result, s), the argument passed there as the
	// caller wrote it, and param that parameter's name.
	within, param string
	// unlessNew is set when the contract places it there only when it is
	// not new, as in fresh(result) Or within(result, s).
	unlessNew bool
	// freshIn holds the arguments, as the caller wrote them, in whose
	// footprints the contract says what the result refers to may lie, as
	// fresh(result, w) does, and at is where the call is. spread is the
	// slice of such values the caller handed whole, as rs in
	// io.MultiReader(rs...), whose elements no clause can list.
	freshIn []string
	spread  string
	at      token.Pos
}

// freshArguments returns the arguments, as the call wrote them, that a
// conjunct fresh(result, w...) of the ensures of a callee names after the
// result, each argument a call packed into a variadic slice among them, and
// the slice a call handed whole in place of them.
func freshArguments(fn *funcInfo, result int, args []passedArg) (found []string, spread string) {
	name := spelledResult(fn, result)
	for _, c := range fn.ensures {
		if c.node == nil {
			continue
		}
		for _, conjunct := range c.node.Conjuncts() {
			if conjunct.Kind != logic.NCall || conjunct.Name != "fresh" || len(conjunct.Kids) < 2 ||
				conjunct.Kids[0].Kind != logic.NIdent || conjunct.Kids[0].Name != name {
				continue
			}
			for _, kid := range conjunct.Kids[1:] {
				for _, arg := range args {
					switch {
					case kid.Kind != logic.NIdent || arg.param.Name() != kid.Name:
					case arg.packed:
						for _, e := range arg.pack {
							found = append(found, types.ExprString(e))
						}
					case arg.spread:
						spread = types.ExprString(arg.expr)
					case arg.expr != nil:
						found = append(found, types.ExprString(arg.expr))
					}
				}
			}
		}
	}
	return found, spread
}

// withinArgument finds, in the ensures of a callee, a conjunct that places
// one of its results within a parameter, and returns the parameter and
// the argument the call passed for it, when that argument is a variable or
// a path of fields from one; otherwise it returns "".
func withinArgument(fn *funcInfo, result int, args []passedArg) (param, argument string, unlessNew bool) {
	name := spelledResult(fn, result)
	for _, c := range fn.ensures {
		if c.node == nil {
			continue
		}
		for _, conjunct := range c.node.Conjuncts() {
			unlessNew = false
			// A result that is new or within a parameter, as what
			// slices.Grow returns, lies within it whenever it is not new.
			if conjunct.Kind == logic.NBinary && conjunct.Op == "Or" {
				fresh, within := conjunct.Kids[0], conjunct.Kids[1]
				if within.Kind == logic.NCall && within.Name == "fresh" {
					fresh, within = within, fresh
				}
				if fresh.Kind == logic.NCall && fresh.Name == "fresh" && len(fresh.Kids) == 1 && fresh.Kids[0].Kind == logic.NIdent && fresh.Kids[0].Name == name {
					conjunct, unlessNew = within, true
				}
			}
			if conjunct.Kind != logic.NCall || conjunct.Name != "within" || len(conjunct.Kids) != 2 ||
				conjunct.Kids[0].Kind != logic.NIdent || conjunct.Kids[0].Name != name || conjunct.Kids[1].Kind != logic.NIdent {
				continue
			}
			for _, arg := range args {
				if arg.param.Name() != conjunct.Kids[1].Name || arg.expr == nil {
					continue
				}
				switch e := ast.Unparen(arg.expr).(type) {
				case *ast.Ident, *ast.SelectorExpr:
					return arg.param.Name(), types.ExprString(e), unlessNew
				}
			}
		}
	}
	return "", "", false
}

// contractTitle names the contract of a function type or of an interface
// method, or returns "" for any other contract.
func (v *fnVerifier) contractTitle(fn *funcInfo) string {
	switch {
	case fn.methodOf != nil:
		return methodTitle(fn.methodOf)
	case fn.valueOf != nil:
		return fn.valueOf.Name()
	}
	return ""
}

// parameterPath names, after the advice to list a write, the path from a
// parameter that reaches the memory written, as in ", as s.From.X": the
// first field of a struct a pointer parameter points to, or the elements
// of a slice parameter, that the write is quickly shown to be. It returns
// "" when none is.
func (v *fnVerifier) parameterPath(st *state, guard []*logic.Term, w written) string {
	if len(w.parts) == 0 || v.fn.decl == nil {
		return ""
	}
	part := w.parts[0]
	for _, param := range v.fn.params {
		entry := v.entry[param]
		if entry == nil || param.Name() == "" || param.Name() == "_" {
			continue
		}
		t := param.Type()
		if isSlice(t) {
			if v.quickly(st, guard, logic.Eq(w.ref, entry[0])) {
				return ", as " + param.Name()
			}
			continue
		}
		object, isPointer := pointee(t)
		if !isPointer {
			continue
		}
		leaves, _ := layoutOf(object)
		for i, c := range v.cellsOf(object) {
			if c.key != part.key || part.lo == nil {
				continue
			}
			at := logic.And(logic.Eq(w.ref, entry[0]), logic.Eq(part.lo, logic.Add(entry[1], logic.IntLit(c.off))))
			if v.quickly(st, guard, at) {
				path, _, _ := strings.Cut(leaves[i].path, "#")
				return ", as " + param.Name() + v.nameablePrefix(object, path)
			}
		}
	}
	return ""
}

// nameablePrefix returns the part of a path of fields, as ".From.X", into a
// struct of type t that a formula of this package can name: it stops before
// the first unexported field of a struct of another package, as
// ".file" of os.File, so that the advice it ends names memory that a
// Modifies clause can list.
func (v *fnVerifier) nameablePrefix(t types.Type, path string) string {
	kept := ""
	for _, name := range strings.Split(strings.TrimPrefix(path, "."), ".") {
		st, ok := t.Underlying().(*types.Struct)
		if !ok || name == "" {
			return kept
		}
		var field *types.Var
		for f := range st.Fields() {
			if f.Name() == name {
				field = f
			}
		}
		if field == nil || (!field.Exported() && field.Pkg() != v.pass.Pkg) {
			return kept
		}
		kept += "." + name
		t = field.Type()
	}
	return kept
}

// notListable returns what a report of a write that nothing covers says to
// do, in place of the advice to list the write, when the written memory is
// reached through a local variable or a result: a Modifies clause names
// memory by a path from a parameter, so that advice could not be followed.
// It returns "" when the path starts at a parameter or cannot be told.
func (v *fnVerifier) notListable(e ast.Expr, pos token.Pos) string {
	root := e
	for {
		switch x := ast.Unparen(root).(type) {
		case *ast.SelectorExpr:
			root = x.X
			continue
		case *ast.IndexExpr:
			root = x.X
			continue
		case *ast.SliceExpr:
			root = x.X
			continue
		case *ast.StarExpr:
			root = x.X
			continue
		}
		break
	}
	id, ok := ast.Unparen(root).(*ast.Ident)
	if !ok {
		return ""
	}
	variable, ok := v.info.Uses[id].(*types.Var)
	if !ok || variable.Pkg() == nil || variable.Parent() == variable.Pkg().Scope() || slices.Contains(v.fn.params, variable) || v.fn.decl == nil {
		return ""
	}
	// A local variable that a loop around the write assigns may hold
	// memory the loop forgot the origin of; one that is not still holds
	// what it was given, which is the caller's through a parameter or the
	// function's own, and the advice to list it can be followed.
	what, looped := "a local variable", v.assignedInLoopAround(variable, pos)
	switch {
	case slices.Contains(v.fn.results, variable):
		what = "a result"
	case !looped:
		return ""
	}
	remedy := fmt.Sprintf("%s is %s, and a // @Modifies clause names memory only by a path from a parameter: if what %s refers to may be memory of the caller, "+
		"list it by the parameter it comes from; if it is memory that %s made, nothing here shows that", id.Name, what, id.Name, v.fn.obj.Name())
	if looped {
		remedy += fmt.Sprintf(", since a loop that assigns %s forgets where its memory came from", id.Name)
		if through := v.writtenThrough(e); through != "" {
			remedy += fmt.Sprintf(": say so with // @Invariant fresh(%s) on the loop", through)
		}
	}
	return remedy
}

// writtenThrough spells the pointer, slice, map, or interface value through
// which an expression writes memory, the one a fresh clause would be about:
// p for p.next, s.items for s.items[i], and the expression itself when it
// is such a value. It returns "" when there is none.
func (v *fnVerifier) writtenThrough(e ast.Expr) string {
	for {
		switch x := ast.Unparen(e).(type) {
		case *ast.SelectorExpr:
			if _, isPointer := pointee(v.info.TypeOf(x.X)); isPointer {
				return types.ExprString(x.X)
			}
			e = x.X
			continue
		case *ast.IndexExpr:
			if isSlice(v.info.TypeOf(x.X)) {
				return types.ExprString(x.X)
			}
			e = x.X
			continue
		case *ast.StarExpr:
			return types.ExprString(x.X)
		}
		t := v.info.TypeOf(e)
		if _, isPointer := pointee(t); isPointer || isSlice(t) || isMap(t) || isIface(t) {
			return types.ExprString(e)
		}
		return ""
	}
}

// assignedInLoopAround reports whether a loop of the function around a
// position assigns a variable.
func (v *fnVerifier) assignedInLoopAround(variable *types.Var, pos token.Pos) bool {
	found := false
	ast.Inspect(v.fn.decl.Body, func(n ast.Node) bool {
		if found || n == nil || pos < n.Pos() || pos >= n.End() {
			return !found && n != nil && (pos >= n.Pos() && pos < n.End())
		}
		var body ast.Node
		switch loop := n.(type) {
		case *ast.ForStmt:
			body = loop
		case *ast.RangeStmt:
			body = loop
		}
		if body != nil {
			ast.Inspect(body, func(m ast.Node) bool {
				if assign, ok := m.(*ast.AssignStmt); ok {
					for _, lhs := range assign.Lhs {
						if id, ok := ast.Unparen(lhs).(*ast.Ident); ok && v.info.ObjectOf(id) == variable {
							found = true
						}
					}
				}
				return !found
			})
		}
		return !found
	})
	return found
}

// checkWriteOr requires that a write is one the function may make: to an
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
//
// remedy, when not empty, is what a report says to do in place of the
// advice to list the write: for a write that no clause could list.
//
// unlisted, when not empty, takes the place of the advice to list the
// write in a Modifies clause, and only of that; see notListable.
func (v *fnVerifier) checkWriteOr(st *state, guard []*logic.Term, w written, pos token.Pos, what, remedy, unlisted string) {
	if len(w.parts) == 0 {
		return
	}
	v.checkNotForbidden(st, guard, w, pos, what)
	created := logic.Or(logic.Le(v.entryBrk, w.ref), logic.Eq(w.ref, logic.RefLit(0)))
	covers := make([][]stretch, len(v.frame))
	var candidates []int
	for i, t := range v.frame {
		covers[i] = t.stretches()
		// A footprint may hold a cell of any region but the storage of an
		// assigned package-level variable (V1).
		if t.fp && slices.ContainsFunc(w.parts, func(part stretch) bool { return isVarRegion(part.key) }) {
			continue
		}
		if t.fp {
			candidates = append(candidates, i)
			continue
		}
		if slices.ContainsFunc(covers[i], func(c stretch) bool {
			return slices.ContainsFunc(w.parts, func(part stretch) bool { return part.key == c.key })
		}) {
			candidates = append(candidates, i)
		}
	}
	// allowed states that the write is covered without the targets of the
	// clause left out, whose index without is, or with every target for -1.
	allowed := func(without int) *logic.Term {
		whole := []*logic.Term{}
		for _, part := range w.parts {
			// A part of one position is covered when that position is; a
			// longer one when every position in it is.
			position, ranged := part.lo, part.lo != nil && !part.one
			if ranged {
				position = v.bound("k")
			}
			var by, premises []*logic.Term
			for _, i := range candidates {
				if t := v.frame[i]; t.fp && t.mod != without {
					at := position
					if part.lo == nil || isMapRegion(part.key) {
						at = logic.IntLit(0)
					}
					cell, facts := v.rowAt(t.rows, t.ref, w.ref, at)
					by = append(by, logic.And(append(facts, cell)...))
					// What the row holds now, as a call may have grown it
					// (F34 of the review of step 4): a cell in it lies in
					// the row on entry or in memory made since, which the
					// layers of the region say of the cell.
					_, grown := v.rowAt(st.mem.region(footprintRegion, footprintSort), t.ref, w.ref, at)
					premises = append(premises, grown...)
				}
				for _, c := range covers[i] {
					switch {
					case v.frame[i].mod == without || c.key != part.key || (c.lo == nil) != (part.lo == nil):
					case c.lo == nil && c.entry != nil && part.entry == nil:
						// One entry covers no write of the whole map.
					case c.lo == nil && c.entry != nil:
						by = append(by, logic.And(logic.Eq(w.ref, v.frame[i].ref), logic.Eq(part.entry, c.entry)))
					case c.lo == nil:
						by = append(by, logic.Eq(w.ref, v.frame[i].ref))
					default:
						by = append(by, logic.And(logic.Eq(w.ref, v.frame[i].ref), logic.Le(c.lo, position), logic.Lt(position, c.hi)))
					}
				}
			}
			covered := logic.Or(by...)
			if len(premises) > 0 {
				covered = logic.Implies(logic.And(premises...), covered)
			}
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
			v.markClause(i)
		}
		// A Modifies entry that ends in an interface value covers the
		// states of what it holds, and not where the value lies.
		// The message is chosen by what Modifies lists other than
		// footprints, which may hold any cell and so are candidates for
		// every write.
		var listed []int
		for _, i := range candidates {
			// The states of an entry whose footprint is listed count as
			// the footprint does (S0b of F34).
			if !v.frame[i].fp && !v.frame[i].besideFootprint {
				listed = append(listed, i)
			}
		}
		var stated *target
		for i, t := range v.frame {
			if t.row && slices.ContainsFunc(t.holder, func(c cell) bool {
				return slices.ContainsFunc(w.parts, func(part stretch) bool { return part.key == c.key })
			}) {
				stated = &v.frame[i]
			}
		}
		// Memory that a package-level variable refers to cannot be
		// listed, so telling the reader to list it would mislead.
		if variable := v.fixedRefs[w.ref.Name]; remedy == "" && w.ref.Op == logic.OpConst && variable != "" {
			remedy = fmt.Sprintf("it is memory that the package-level variable %s refers to; list %s in a // @Modifies clause", variable, variable)
		}
		// Memory that a function returned without saying that it is new
		// may have existed when the function was called, as what
		// bufio.NewWriter returns when it is given a large enough Writer.
		if from, ok := v.returnedBy[w.ref.Name]; remedy == "" && len(listed) == 0 && w.ref.Op == logic.OpConst && ok {
			callee := from.fn.obj.Name()
			remedy = fmt.Sprintf("it is memory that %s returned, and its contract does not say that this is new memory, so it may have existed when %s "+
				"was called; take it as a parameter and list it in a // @Modifies clause", callee, v.fn.obj.Name())
			if len(from.freshIn) > 0 {
				remedy = fmt.Sprintf("it is memory that %s returned, which its contract places in the footprint of %s when it is not new; list %s in a // @Modifies clause",
					callee, strings.Join(from.freshIn, " or "), strings.Join(from.freshIn, " and "))
			}
			if from.within != "" {
				unless := ""
				if from.unlessNew {
					unless = " when it is not new"
				}
				remedy = fmt.Sprintf("it is memory that %s returned, which its contract places within %s%s, and %s passed %s as %s; list %s in a // @Modifies clause",
					callee, from.param, unless, v.fn.obj.Name(), from.within, from.param, from.within)
				if from.within == from.param {
					remedy = fmt.Sprintf("it is memory that %s returned, which its contract places within %s%s; list %s in a // @Modifies clause",
						callee, from.param, unless, from.within)
				}
			}
			switch contract := v.contractTitle(from.fn); {
			case from.fn.trust != nil || len(from.freshIn) > 0:
			case contract != "":
				remedy = fmt.Sprintf("it is memory that a call of %s returned, and the contract of %s does not say that this is new memory, so it may have existed when %s "+
					"was called; if it is new, say so in the contract of %s, with // @Ensures fresh(%s), or take it as a parameter and list it in a // @Modifies clause",
					from.call, contract, v.fn.obj.Name(), contract, spelledResult(from.fn, from.result))
			default:
				remedy = fmt.Sprintf("it is memory that %s returned, and its contract does not say that this is new memory, so it may have existed when %s "+
					"was called; if it is new, say so in the contract of %s, with // @Ensures fresh(%s), or take it as a parameter and list it in a // @Modifies clause",
					callee, v.fn.obj.Name(), callee, from.fn.results[from.result].Name())
			}
		}
		switch {
		case remedy != "":
			v.report(pos, "%s, which %s may not modify; %s%s", what, v.fn.obj.Name(), remedy, limitNote(result))
		case len(listed) == 0 && stated != nil:
			v.report(pos, "%s, which %s may not modify: // @Modifies %s covers the states of what the interface value %s holds, not the place that holds it; "+
				"to assign it, list the struct that holds it%s", what, v.fn.obj.Name(), stated.text, stated.text, limitNote(result))
		case len(listed) == 0 && (v.fn.spelling().valueOf != nil || v.fn.spelling().methodOf != nil):
			// What is checked against the contract of a type cannot add to
			// it: the clause it would need is in the contract.
			contract := "the contract of " + v.fn.obj.Name()
			if entry := v.fn.spelling().trust; entry != nil {
				contract = "the entry " + entry.key + " in the trust file"
			}
			v.report(pos, "%s, which %s may not modify; %s does not list it, so code that writes it cannot be used there%s",
				what, v.fn.obj.Name(), contract, limitNote(result))
		case len(listed) == 0 && unlisted != "":
			v.report(pos, "%s, which %s may not modify; %s%s", what, v.fn.obj.Name(), unlisted, limitNote(result))
		case len(listed) == 0:
			v.report(pos, "%s, which %s may not modify; list it in a // @Modifies clause%s%s", what, v.fn.obj.Name(), v.parameterPath(st, guard, w), limitNote(result))
		default:
			// Something of the kind is listed, so telling the reader to
			// list it would send them in a circle. A listed variable that
			// refers to memory may have been assigned since entry, by the
			// function or by a call that lists it (F19 of the review of
			// step 2 of package-level variables).
			hint := ""
			for _, t := range v.frame {
				variable := v.variableOfCells(t.cells)
				if variable == nil || !t.single || !holdsMemory(variable.Type()) || isStructType(variable.Type()) {
					continue
				}
				if _, written := st.mem[t.cells[0].key]; written {
					name := v.spelling(variable)
					hint = fmt.Sprintf("; %s may have been assigned since, by a statement or by a call that lists it, so it may no longer refer to that; "+
						"a call that keeps it can say so in its contract with %s' = %s", name, name, name)
					break
				}
			}
			v.report(pos, "%s, which %s may not modify: nothing its // @Modifies clauses list is known to cover it; "+
				"a clause covers what its path referred to when %s was called%s%s", what, v.fn.obj.Name(), v.fn.obj.Name(), hint, limitNote(result))
		}
		st.assume(logic.Implies(logic.And(guard...), goal))
		return
	}
	// An entry counts as needed unless the write is quickly shown to be
	// allowed without it.
	defer v.asking(modifiesCheck)()
	// Whether the write is to memory made since entry matters only for a
	// clause not yet known to be needed.
	if !slices.ContainsFunc(candidates, func(i int) bool { return !v.used[i] }) || v.quickly(st, guard, created) {
		return
	}
	v.markNeeded(candidates, func(mod int) bool { return v.quickly(st, guard, allowed(mod)) })
}

// markNeeded records which clauses among the targets that may cover a
// write it could not do without: once a clause, with all of its targets
// left out together, since what is reported is whether a clause is needed
// (an owner gives several targets, and an interface value its footprint and
// its states), and not at all a clause already known to be needed.
func (v *fnVerifier) markNeeded(candidates []int, coveredWithout func(mod int) bool) {
	asked := map[int]bool{}
	for _, i := range candidates {
		mod := v.frame[i].mod
		if asked[mod] {
			continue
		}
		asked[mod] = true
		// A clause already known to be needed need not be asked of again.
		if v.used[i] {
			continue
		}
		if !coveredWithout(mod) {
			v.markClause(i)
		}
	}
}

// markClause records that the clause of a target of the frame is needed:
// every target it gives, the footprint of an interface value and its states
// alike, which since S0b of F34 are two targets of one clause.
func (v *fnVerifier) markClause(i int) {
	mod := v.frame[i].mod
	for j, t := range v.frame {
		if j == i || mod >= 0 && t.mod == mod {
			v.used[j] = true
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
//
// guard holds the conditions under which the call runs at all, as on the
// right of && or ||. Where they do not hold, the call did not run, and what
// the target holds is what it held before.
func (v *fnVerifier) havoc(st *state, t target, guard []*logic.Term) {
	skipped := logic.False()
	if len(guard) > 0 {
		skipped = logic.Not(logic.And(guard...))
	}
	// kept states that a sequence holds what another held, everywhere or
	// where the call did not run.
	kept := func(now, before *logic.Term) {
		if len(guard) == 0 {
			return
		}
		index := v.bound("k")
		st.assume(logic.Implies(skipped, logic.Forall(index, v.same(logic.Select(now, index), logic.Select(before, index)))))
	}
	switch {
	case t.fp:
		if len(guard) > 0 {
			t.skipped = skipped
		}
		v.startEpoch(st, st.brk, []target{t})
		var notRun *logic.Term
		if len(guard) > 0 {
			notRun = skipped
		}
		v.growing = append(v.growing, v.grow(st, st.brk, notRun))
		if t.row {
			panic("internal error: a footprint target that covers states too; targets gives them a target of their own")
		}
	case t.mapType != nil && t.key != nil:
		v.havocEntry(st, t, skipped, len(guard) > 0)
	case t.mapType != nil:
		owner := mapOwner(t.mapType)
		t.regions(func(key string, sort logic.Sort) {
			if key == owner+countLeaf.path {
				before := logic.Select(st.mem.region(key, logic.SeqOf(sort)), t.ref)
				written := v.fresh("written", sort)
				if len(guard) > 0 {
					st.assume(logic.Implies(skipped, logic.Eq(written, before)))
				}
				st.storeCell(key, countLeaf, t.ref, written)
				return
			}
			before := logic.Select(st.mem.region(key, logic.SeqOf(logic.SeqOf(sort))), t.ref)
			written := v.fresh("written", logic.SeqOf(sort))
			kept(written, before)
			st.storeRow(key, sort, t.ref, written)
		})
		// Nothing can be put into the nil map, so if that is what the
		// target is, it is as empty afterwards as it was.
		index := v.bound("k")
		has := logic.Select(st.mem.region(owner+hasLeaf.path, logic.SeqOf(logic.SeqOf(logic.Bool))), t.ref)
		count := logic.Select(st.mem.region(owner+countLeaf.path, logic.SeqOf(logic.Int)), t.ref)
		empty := logic.And(logic.Eq(count, logic.IntLit(0)), logic.Forall(index, logic.Not(logic.Select(has, index))))
		st.assume(logic.Implies(logic.And(append(slices.Clip(guard), logic.Eq(t.ref, logic.RefLit(0)))...), empty))
	case t.row:
		// Every state of the value, whoever declared it, may change.
		before := v.row(nil, st.mem, stateRegion, logic.Bool, t.ref)
		unknown := v.fresh("written", logic.BoolSeq)
		kept(unknown, before)
		st.storeRow(stateRegion, logic.Bool, t.ref, unknown)
	case t.single:
		if t.base != nil {
			v.noteStruct(st, *t.base)
		}
		// What the types guarantee of the new values is noted where they
		// are read.
		before := v.fetch(nil, st.mem, t.cells, t.ref, t.lo)
		unknown := make(value, len(t.cells))
		for i, c := range t.cells {
			unknown[i] = v.fresh("written", c.sort)
			if len(guard) > 0 {
				st.assume(logic.Implies(skipped, v.same(unknown[i], before[i])))
			}
		}
		v.put(st, t.cells, t.ref, t.lo, unknown)
	default:
		t.regions(func(key string, sort logic.Sort) {
			before := logic.Select(st.mem.region(key, logic.SeqOf(logic.SeqOf(sort))), t.ref)
			unknown := v.fresh("written", logic.SeqOf(sort))
			if t.part && !sort.IsSeq() {
				// What an owner owns is written as a row that holds unknown
				// values in the stretch and what it held everywhere else: a
				// term, where the fact below is a quantifier, of which Z3
				// cannot build a model in the questions of the always-fails
				// check after a call. The row is a definition that Z3
				// expands, so a quantified fact whose pattern reads it loses
				// its pattern; a part is memory nothing in the caller names,
				// so few facts read it, while a slice of the caller has
				// facts over its elements that would.
				hi := t.hi
				if len(guard) > 0 {
					hi = logic.Ite(skipped, t.lo, t.hi)
				}
				table := logic.SeqOf(logic.SeqOf(sort))
				ref, lo := v.apart(st, t.ref, table), v.apart(st, t.lo, table)
				hi = v.apart(st, hi, table)
				st.mem[key] = logic.SpliceAt(st.mem.region(key, table), ref, unknown, lo, hi)
				return
			}
			index := v.bound("k")
			outside := logic.Or(skipped, logic.Lt(index, t.lo), logic.Le(t.hi, index))
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

// isStructType reports whether t is a struct type.
func isStructType(t types.Type) bool {
	_, isStruct := t.Underlying().(*types.Struct)
	return isStruct
}

// structValue is a struct value in memory: its type, its allocation, and
// its position.
type structValue struct {
	t       types.Type
	ref, at *logic.Term
}

// structAt is a struct value of non-zero size that a value of a type holds:
// the key of its type, which types that share regions share, its offset in
// the value, and its size.
type structAt struct {
	key       string
	off, size int64
}

// structsWithin returns the struct values of non-zero size that a value of
// type t holds in itself: t, when it is a struct, at offset 0, and every
// field of struct type at any depth at its offset.
func (pv *pkgVerifier) structsWithin(t types.Type) []structAt {
	u, isStruct := t.Underlying().(*types.Struct)
	if !isStruct {
		return nil
	}
	var found []structAt
	if size := pv.pass.TypesSizes.Sizeof(t); size > 0 {
		found = append(found, structAt{key: typeKey(u), size: size})
	}
	fields := slices.Collect(u.Fields())
	offsets := pv.pass.TypesSizes.Offsetsof(fields)
	for i, field := range fields {
		for _, inner := range pv.structsWithin(field.Type()) {
			inner.off += offsets[i]
			found = append(found, inner)
		}
	}
	return found
}

// statePairs states, for the struct values x and y and each pair of
// structs they hold of one type, of every type when all is set and
// otherwise of the types that hold two leaves in one region, that the two
// are one value or lie apart: in one allocation, at one position or at
// least the size of the type apart. That is true of every state Go makes
// without unsafe: a pointer to a struct points to a value of its type, a
// variable, a field at any depth, or an element of a slice, and two values
// of one struct type never overlap otherwise, since one would have to hold
// the other, and a struct type cannot hold itself; fields of one struct,
// and elements of one array, are disjoint. Types that share regions
// (identical underlying structs, tags ignored) have one key, so they count
// as one type, as a conversion between them needs. A struct of size zero
// has no identity and is never given one (structsWithin). A nil pointer
// points to no value, so the fact holds only of an allocation other than
// 0.
//
// Only a type that holds two leaves in one region, as struct{ A, B Inner }
// does, needs it where a write of a struct target, a store, or a loop's
// layer compares cells region by region: only then can a cell of one value
// of the type be taken, position by position, for another cell of another.
// The stretch of a conversion's footprint compares positions in every
// region, so there every type needs it.
func (v *fnVerifier) statePairs(sink *state, x, y structValue, all bool) {
	for _, a := range v.structsWithin(x.t) {
		if !all && !v.repeats[a.key] {
			continue
		}
		for _, b := range v.structsWithin(y.t) {
			if a.key != b.key {
				continue
			}
			pa, pb := logic.Add(x.at, logic.IntLit(a.off)), logic.Add(y.at, logic.IntLit(b.off))
			size := logic.IntLit(a.size)
			fact := logic.Or(logic.Eq(x.ref, logic.RefLit(0)), logic.Ne(x.ref, y.ref), logic.Eq(pa, pb),
				logic.Le(logic.Add(pa, size), pb), logic.Le(logic.Add(pb, size), pa))
			if note := "distinct|" + fact.String(); !sink.noted[note] {
				sink.noted[note] = true
				sink.assume(fact)
			}
		}
	}
}

// noteStruct records a struct value the function reads or writes, whose
// type holds two leaves in one region, and states the fact between struct
// values of it and each one recorded before, so that a read of one keeps
// what a write of the other did not write.
func (v *fnVerifier) noteStruct(sink *state, s structValue) {
	if sink == nil || !v.holdsRepeated(s.t) {
		return
	}
	for _, other := range v.structsSeen {
		v.statePairs(sink, s, other, false)
	}
	v.structsSeen = append(v.structsSeen, s)
}

// holdsRepeated reports whether a value of type t holds, at any depth, a
// struct whose type holds two leaves in one region, and records which
// struct types do.
func (v *fnVerifier) holdsRepeated(t types.Type) bool {
	if v.repeats == nil {
		v.repeats = map[string]bool{}
	}
	found := false
	u, isStruct := t.Underlying().(*types.Struct)
	if !isStruct {
		return false
	}
	for field := range u.Fields() {
		found = v.holdsRepeated(field.Type()) || found
	}
	key := typeKey(u)
	if known, ok := v.repeats[key]; ok {
		return known || found
	}
	seen := map[string]bool{}
	repeated := false
	for _, c := range v.cellsOf(t) {
		repeated = repeated || seen[c.key]
		seen[c.key] = true
	}
	v.repeats[key] = repeated
	return repeated || found
}

// leafOnly states, of a cell of a region read at ref and position, that
// it lies in the stretch of the struct value s only where the type of s
// has a leaf in that region: a cell Go holds lies in a struct value only as
// one of its leaves, since what lies in the bytes of a value is its fields
// and what they hold, and a value that holds the struct has its own leaves
// elsewhere. So the stretch a conversion's footprint is, which counts
// positions in every region, holds of another region only its own leaves:
// the slot of a slice of pointers, read beside the struct one of them
// points to, never lies in it. It is a fact about where the cells of a
// region can be, not about the row, which keeps its definition.
func (v *fnVerifier) leafOnly(sink *state, s structValue, key string, ref, position *logic.Term) {
	size := v.pass.TypesSizes.Sizeof(s.t)
	if size == 0 {
		return
	}
	options := []*logic.Term{logic.Ne(ref, s.ref), logic.Lt(position, s.at), logic.Le(logic.Add(s.at, logic.IntLit(size)), position)}
	for _, c := range v.cellsOf(s.t) {
		if c.key == key {
			options = append(options, logic.Eq(position, logic.Add(s.at, logic.IntLit(c.off))))
		}
	}
	fact := logic.Or(options...)
	if note := "leaf|" + fact.String(); !sink.noted[note] {
		sink.noted[note] = true
		sink.assume(fact)
	}
}

// distinctStructs states, for the struct the read under way reads a cell
// of, the fact between struct values against each struct target of a layer
// it meets, for the types that hold two leaves in one region, and, when
// the layer writes a footprint, against each struct the function converted,
// for every type, since the footprint of a conversion is the struct's
// stretch of positions in every region.
func (v *fnVerifier) distinctStructs(sink *state, known *layer, key string, ref, position *logic.Term) {
	if sink == nil {
		return
	}
	if hasFootprintTarget(known.targets) && position != nil {
		for _, converted := range v.convertedStructs {
			v.leafOnly(sink, converted, key, ref, position)
		}
	}
	if v.readBase == nil {
		return
	}
	for _, t := range known.targets {
		if t.base != nil {
			v.statePairs(sink, *v.readBase, *t.base, false)
		}
	}
	if hasFootprintTarget(known.targets) {
		for _, converted := range v.convertedStructs {
			v.statePairs(sink, *v.readBase, converted, true)
		}
	}
}
