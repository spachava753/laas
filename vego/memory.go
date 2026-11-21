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
}

func (st *state) clone() *state {
	return &state{
		vals: maps.Clone(st.vals), mem: maps.Clone(st.mem), brk: st.brk,
		hyps: slices.Clone(st.hyps), chosen: slices.Clone(st.chosen), noted: maps.Clone(st.noted),
		deferred: slices.Clone(st.deferred), snapshots: st.snapshots, visited: st.visited,
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
	// row is set when the target is every state of an interface value:
	// the whole row of its home in the region of states, which ref is.
	// lo and hi are nil, as for a map. holder is set to the cells of the
	// interface value when it lies in memory, which the target does not
	// cover; see checkWriteOr.
	row    bool
	holder []cell
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
		for at.Op == logic.OpStore || at.Op == logic.OpWrite {
			at = at.Args[0]
		}
		if seen[at.Name] {
			continue
		}
		seen[at.Name] = true
		note := at.Name + "|" + ref.String()
		if known := v.layers[at.Name]; known != nil {
			if !sink.noted[note] {
				sink.noted[note] = true
				sink.assume(v.unchanged(at, known, ref))
			}
			pending = append(pending, known.prev)
		}
		if joined := v.joins[at.Name]; joined != nil {
			if !sink.noted[note] {
				sink.noted[note] = true
				fact := v.joinedAt(at, joined, ref)
				sink.assume(fact)
				v.forwards[joined.forward].facts = append(v.forwards[joined.forward].facts, fact)
			}
			pending = append(pending, joined.alternatives...)
		}
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
		switch {
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

// typedRead is a value read from memory with its type; see canBeMet.
type typedRead struct {
	val value
	t   types.Type
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
		if v.typedReads != nil {
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
	v.checkWriteOr(st, guard, w, pos, what, "", "")
}

// checkWriteOr is checkWrite, with what a report says to do in place of the
// advice to list the write, when remedy is not empty: for a write that no
// clause could list.
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
		// A Modifies entry that ends in an interface value covers the
		// states of what it holds, and not where the value lies.
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
			remedy = fmt.Sprintf("it is memory that the package-level variable %s refers to, which a Modifies clause cannot name yet", variable)
		}
		// Memory that a function returned without saying that it is new
		// may have existed when the function was called, as what
		// bufio.NewWriter returns when it is given a large enough Writer.
		if from, ok := v.returnedBy[w.ref.Name]; remedy == "" && len(candidates) == 0 && w.ref.Op == logic.OpConst && ok {
			callee := from.fn.obj.Name()
			remedy = fmt.Sprintf("it is memory that %s returned, and its contract does not say that this is new memory, so it may have existed when %s "+
				"was called; take it as a parameter and list it in a // @Modifies clause", callee, v.fn.obj.Name())
			if from.within != "" {
				unless := ""
				if from.unlessNew {
					unless = " when it is not new"
				}
				remedy = fmt.Sprintf("it is memory that %s returned, which its contract places within %s%s, and %s passed %s as %s; list %s in a // @Modifies clause",
					callee, from.param, unless, v.fn.obj.Name(), from.within, from.param, from.within)
			}
			switch contract := v.contractTitle(from.fn); {
			case from.fn.trust != nil:
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
		case len(candidates) == 0 && stated != nil:
			v.report(pos, "%s, which %s may not modify: // @Modifies %s covers the states of what the interface value %s holds, not the place that holds it; "+
				"to assign it, list the struct that holds it%s", what, v.fn.obj.Name(), stated.text, stated.text, limitNote(result))
		case len(candidates) == 0 && (v.fn.spelling().valueOf != nil || v.fn.spelling().methodOf != nil):
			// What is checked against the contract of a type cannot add to
			// it: the clause it would need is in the contract.
			contract := "the contract of " + v.fn.obj.Name()
			if entry := v.fn.spelling().trust; entry != nil {
				contract = "the entry " + entry.key + " in the trust file"
			}
			v.report(pos, "%s, which %s may not modify; %s does not list it, so code that writes it cannot be used there%s",
				what, v.fn.obj.Name(), contract, limitNote(result))
		case len(candidates) == 0 && unlisted != "":
			v.report(pos, "%s, which %s may not modify; %s%s", what, v.fn.obj.Name(), unlisted, limitNote(result))
		case len(candidates) == 0:
			v.report(pos, "%s, which %s may not modify; list it in a // @Modifies clause%s%s", what, v.fn.obj.Name(), v.parameterPath(st, guard, w), limitNote(result))
		default:
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
	defer v.asking(modifiesCheck)()
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
