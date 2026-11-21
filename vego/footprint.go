package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"strings"

	"github.com/spachava753/laas/vego/internal/logic"
	"github.com/spachava753/laas/vego/internal/solver"
)

// The footprint of an interface value is the memory that the methods of
// what it holds may write behind its receiver. It is a set of cells, each
// an allocation and a position, as the memory model has them, and it lies
// in a ghost region, footprintRegion, at the row of the value's home: the
// row holds, for each allocation and position, whether the cell is part of
// the footprint. Nothing in Go reads or writes the region.
//
// A call of a method whose contract lists its receiver in Modifies may write
// every cell of the footprint, in every region, also one not yet in the
// memory map; so such a call starts an epoch (see epoch), and every region
// read after it starts from a layer that keeps what lies outside the
// footprint. The footprint itself grows during such a call only by memory
// the call creates (growth layers), which is what a value from code that is
// not verified is assumed to do and what a verified callee proves.
//
// These facts are the only ones ever stated about a row, so no fact makes a
// row smaller than what the value's methods may write:
//
//   - a row holds only allocations that exist in the state it belongs to;
//   - a growth layer keeps every allocation that existed before its call;
//   - the separation of a listed footprint parameter from what the other
//     parameters reach without going through an interface value (reach),
//     which is the assumption about callers.
//
// In this first part a value has a footprint only when its interface type
// is declared in source, has no states, and has a method whose contract
// lists its receiver; every other interface value keeps the meaning of
// states only.

// footprintRegion is the ghost region of footprints.
const footprintRegion = "footprint"

// footprintSort is the sort of the footprint region: home, then allocation,
// then position.
var footprintSort = logic.SeqOf(logic.SeqOf(logic.SeqOf(logic.Bool)))

// reachSort is the sort of a reach predicate: allocation, then position.
var reachSort = logic.SeqOf(logic.SeqOf(logic.Bool))

// epochKey is the key under which memory holds the epoch it is in, when a
// call that writes a footprint has run; see region. A space keeps it apart
// from the keys of regions.
const epochKey = "epoch "

// epochMark begins the name of a region read in an epoch, which is
// epochMark, the name of the epoch, a space, and the key of the region.
const epochMark = "mem~"

// epoch is what a call or a loop that writes footprints left of memory:
// every region read after it is a new unknown of which a layer keeps what
// the targets do not cover, or, after a join of ends in different epochs, a
// join of what each end had.
type epoch struct {
	before  memory
	bound   *logic.Term
	targets []target
	// join is set for an epoch that a join of the ends of a function
	// literal made: each end's memory, which joined chooses between.
	ends   []memory
	joined *joinedRegion
}

// inEpoch returns the region a key has in the epoch memory is in, or nil
// when memory is in none.
func (m memory) inEpoch(key string, sort logic.Sort) *logic.Term {
	if key == footprintRegion {
		return nil
	}
	e, ok := m[epochKey]
	if !ok {
		return nil
	}
	return logic.Const(epochMark+e.Name+" "+key, sort)
}

// materialize registers what is known of a region read in an epoch, the
// first time it is read: a layer over the region before the epoch, or a
// join of the regions of the ends.
func (v *fnVerifier) materialize(name string, sort logic.Sort) {
	if !strings.HasPrefix(name, epochMark) || v.layers[name] != nil || v.joins[name] != nil {
		return
	}
	rest := strings.TrimPrefix(name, epochMark)
	space := strings.IndexByte(rest, ' ')
	e := v.epochs[rest[:space]]
	key := rest[space+1:]
	if e == nil {
		panic(fmt.Sprintf("vego: internal error: %s is read in an epoch that was never made", key))
	}
	if e.joined != nil {
		alternatives := make([]*logic.Term, len(e.ends))
		for i, end := range e.ends {
			alternatives[i] = end.region(key, sort)
		}
		joined := *e.joined
		joined.alternatives = alternatives
		v.joins[name] = &joined
		v.forwards[joined.forward].produced = append(v.forwards[joined.forward].produced, name)
		return
	}
	flat := !sort.Elem().IsSeq()
	v.layers[name] = &layer{prev: e.before.region(key, sort), bound: e.bound, targets: e.targets, key: key, flat: flat}
}

// startEpoch makes every region of memory, also one not yet in the map, a
// new unknown that keeps what the targets do not cover. The footprint
// region itself is not part of it; see grow.
func (v *fnVerifier) startEpoch(st *state, bound *logic.Term, targets []target) {
	e := v.fresh("epoch", logic.Int)
	v.epochs[e.Name] = &epoch{before: st.mem, bound: bound, targets: targets}
	mem := memory{epochKey: e}
	if rows, ok := st.mem[footprintRegion]; ok {
		mem[footprintRegion] = rows
	}
	st.mem = mem
}

// grow gives the footprint region a new unknown in which every allocation
// below bound has the cells it had, which is all a call that may write
// footprints changes of them: a footprint grows only by memory the call
// creates. skipped, when not nil, is when the call did not run. It returns
// the layer, whose after the caller sets once the bound after the call is
// known.
func (v *fnVerifier) grow(st *state, bound, skipped *logic.Term) *layer {
	grown := v.fresh("mem'"+footprintRegion, footprintSort)
	known := &layer{prev: st.mem.region(footprintRegion, footprintSort), bound: bound, key: footprintRegion, growth: true, skipped: skipped}
	v.layers[grown.Name] = known
	st.mem[footprintRegion] = grown
	return known
}



// rowAt reads whether a cell is in the footprint at a home, in the rows
// given, and returns with it what the layers of the footprint region say
// of that very cell: each growth layer keeps it if its allocation is old
// enough and holds it only if its allocation exists, a join holds what the
// end it took held, and on entry it lies in an allocation that existed.
// The facts are about the cell alone, so they need no quantifier; alloc
// and pos may be bound variables, and the facts are then true for every
// value of them, to be conjoined inside the quantifier.
func (v *fnVerifier) rowAt(rows, home, alloc, pos *logic.Term) (*logic.Term, []*logic.Term) {
	cellOf := func(t *logic.Term) *logic.Term {
		return logic.Select(logic.Select(logic.Select(t, home), alloc), pos)
	}
	var facts []*logic.Term
	seen := map[string]bool{}
	for pending := []*logic.Term{rows}; len(pending) > 0; {
		at := pending[len(pending)-1]
		pending = pending[:len(pending)-1]
		if seen[at.Name] {
			continue
		}
		seen[at.Name] = true
		switch {
		case at.Name == entryRegion+footprintRegion:
			facts = append(facts, logic.Implies(cellOf(at), logic.And(logic.Lt(logic.IntLit(0), alloc), logic.Lt(alloc, v.entryBrk))))
		case v.layers[at.Name] != nil:
			known := v.layers[at.Name]
			if !known.growth {
				panic("vego: internal error: the footprint region has a layer that is not a growth layer")
			}
			kept := logic.Lt(alloc, known.bound)
			if known.skipped != nil {
				kept = logic.Or(kept, known.skipped)
			}
			facts = append(facts, logic.Implies(kept, logic.Iff(cellOf(at), cellOf(known.prev))))
			if known.after != nil {
				facts = append(facts, logic.Implies(cellOf(at), logic.And(logic.Lt(logic.IntLit(0), alloc), logic.Lt(alloc, known.after))))
			}
			pending = append(pending, known.prev)
		case v.joins[at.Name] != nil:
			joined := v.joins[at.Name]
			for i, alternative := range joined.alternatives {
				facts = append(facts, logic.Implies(joined.which[i], logic.Iff(cellOf(at), cellOf(alternative))))
				pending = append(pending, alternative)
			}
		default:
			panic(fmt.Sprintf("vego: internal error: the footprint region %s has no layer, join, or entry", at.Name))
		}
	}
	return cellOf(rows), facts
}

// hasFootprint reports whether values of a type have a footprint: an
// interface type that has no states and has a method whose contract lists
// its receiver in Modifies; see the comment at the top.
func (pv *pkgVerifier) hasFootprint(t types.Type) bool {
	if !isIface(t) || pv.hasStates(t) {
		return false
	}
	for method := range t.Underlying().(*types.Interface).Methods() {
		if writesBehind(pv.methodContract(method)) {
			return true
		}
	}
	return false
}

// writesBehind reports whether the contract of a method of an interface,
// written in source, lists its receiver in Modifies.
func writesBehind(fn *funcInfo) bool {
	if fn == nil || fn.trust != nil || fn.receiver == nil {
		return false
	}
	for _, m := range fn.modifies {
		if m.name == fn.receiver.Name() {
			return true
		}
	}
	return false
}

// isMapRegion reports whether a region holds the memory of maps, which a
// footprint holds whole: the cell of a map in a row is at position 0.
func isMapRegion(key string) bool {
	return strings.HasPrefix(key, "map ")
}

// hasFootprintTarget reports whether a list of targets has a footprint.
func hasFootprintTarget(targets []target) bool {
	for _, t := range targets {
		if t.fp {
			return true
		}
	}
	return false
}

// outsideFootprint states that a cell is not written by a footprint
// target: the call did not run, the cell is not in the footprint, or it is
// a state of the value itself, whose own row the contract governs (F7 of
// the design review: a method declared on an interface without states
// changes none of them). It returns with it the facts of rowAt.
func (v *fnVerifier) outsideFootprint(t target, key string, ref, position *logic.Term) (*logic.Term, []*logic.Term) {
	cell, facts := v.rowAt(t.rows, t.ref, ref, position)
	conditions := []*logic.Term{logic.Not(cell)}
	if key == stateRegion {
		conditions = append(conditions, logic.Eq(ref, t.ref))
	}
	if t.skipped != nil {
		conditions = append(conditions, t.skipped)
	}
	return logic.Or(conditions...), facts
}

// separation is what a function assumes of a parameter whose
// footprint its Modifies lists: on entry, the footprint holds no cell that
// the other parameters reach without going through an interface value.
// rel holds, for every allocation and position, whether the cell is so
// reached; home is the home of the parameter on entry.
type separation struct {
	param *types.Var
	rel   *logic.Term
	home  *logic.Term
}

// reachApart states, at one cell, what the separation of every listed
// footprint parameter says there.
func (v *fnVerifier) reachApart(ref, position *logic.Term) *logic.Term {
	var facts []*logic.Term
	for _, r := range v.reaches {
		reached := logic.Select(logic.Select(r.rel, ref), position)
		inRow, rowFacts := v.rowAt(logic.Const(entryRegion+footprintRegion, footprintSort), r.home, ref, position)
		facts = append(facts, rowFacts...)
		facts = append(facts, logic.Implies(reached, logic.And(logic.Not(inRow), logic.Lt(logic.IntLit(0), ref), logic.Lt(ref, v.entryBrk))))
	}
	return logic.And(facts...)
}

// checkFootprintWrite requires that a call may write the footprint of an
// interface value: every cell of it lies in memory created since the
// function was entered, or in a footprint that a Modifies clause lists.
// remedy and unlisted are as for checkWriteOr. The cell is one of which
// nothing is known, so what is proved of it holds of every cell.
func (v *fnVerifier) checkFootprintWrite(st *state, guard []*logic.Term, t target, pos token.Pos, what, remedy, unlisted string) {
	if len(v.forbidden) > 0 {
		v.unsupported(pos, what+", and a function handed to a trusted function cannot write the footprint of an interface value yet")
	}
	var candidates []int
	for i, f := range v.frame {
		if f.fp {
			candidates = append(candidates, i)
		}
	}
	alloc, position := v.fresh("cell", logic.Ref), v.fresh("at", logic.Int)
	probe := st.clone()
	cell, facts := v.rowAt(t.rows, t.ref, alloc, position)
	framed := make([]*logic.Term, len(v.frame))
	for _, i := range candidates {
		var more []*logic.Term
		framed[i], more = v.rowAt(v.frame[i].rows, v.frame[i].ref, alloc, position)
		facts = append(facts, more...)
	}
	for _, fact := range facts {
		probe.assume(fact)
	}
	allowed := func(without int) *logic.Term {
		covered := []*logic.Term{logic.Le(v.entryBrk, alloc)}
		for _, i := range candidates {
			if i != without {
				covered = append(covered, framed[i])
			}
		}
		return logic.Implies(cell, logic.Or(covered...))
	}
	if result := v.attempt(probe, guard, allowed(-1)); result != solver.Proved {
		for _, i := range candidates {
			v.used[i] = true
		}
		switch {
		case remedy != "":
			v.report(pos, "%s, which %s may not modify; %s%s", what, v.fn.obj.Name(), remedy, limitNote(result))
		case len(candidates) == 0 && (v.fn.spelling().valueOf != nil || v.fn.spelling().methodOf != nil):
			v.report(pos, "%s, which %s may not modify; the contract of %s does not list it, so code that writes it cannot be used there%s",
				what, v.fn.obj.Name(), v.fn.obj.Name(), limitNote(result))
		case len(candidates) == 0 && unlisted != "":
			v.report(pos, "%s, which %s may not modify; %s%s", what, v.fn.obj.Name(), unlisted, limitNote(result))
		case len(candidates) == 0:
			v.report(pos, "%s, which %s may not modify; list it in a // @Modifies clause%s", what, v.fn.obj.Name(), limitNote(result))
		default:
			v.report(pos, "%s, which %s may not modify: no footprint its // @Modifies clauses list is known to hold it; "+
				"a clause covers what its path referred to when %s was called%s", what, v.fn.obj.Name(), v.fn.obj.Name(), limitNote(result))
		}
		return
	}
	defer v.asking(modifiesCheck)()
	for _, i := range candidates {
		if !v.quickly(probe, guard, allowed(i)) {
			v.used[i] = true
		}
	}
}

// checkFootprintRanged requires that a call that writes a footprint while
// a loop ranges over a map does not write that map.
func (v *fnVerifier) checkFootprintRanged(st *state, guard []*logic.Term, t target, pos token.Pos, name string) {
	for _, r := range v.ranges {
		cell, facts := v.rowAt(t.rows, t.ref, r.walk.ref, logic.IntLit(0))
		for _, fact := range facts {
			st.assume(fact)
		}
		v.check(st, guard, logic.Not(cell), pos,
			"%s may modify %s while the loop at %s ranges over it, since the map may lie in the footprint of what it is called on; "+
				"change the map in the loop's body, or after the loop", name, r.text, v.placeOf(r.at))
	}
}

// reachedBy states that what a value of a type refers to directly, not
// through an interface value, is reached: the struct a pointer points to,
// the array of a slice from its start to its capacity, a map, and the same
// of the fields of a struct.
func (v *fnVerifier) reachedBy(rel *logic.Term, val value, t types.Type) *logic.Term {
	zero := logic.RefLit(0)
	inRange := func(ref, lo, hi *logic.Term) *logic.Term {
		j := v.bound("k")
		cellOf := logic.Select(logic.Select(rel, ref), j)
		return logic.Implies(logic.Ne(ref, zero), logic.Forall(j, logic.Implies(logic.And(logic.Le(lo, j), logic.Lt(j, hi)), cellOf)))
	}
	if object, isPointer := pointee(t); isPointer {
		return inRange(val[0], val[1], logic.Add(val[1], logic.IntLit(v.span(object))))
	}
	switch u := t.Underlying().(type) {
	case *types.Slice:
		return inRange(val[0], val[1], logic.Add(val[1], logic.Mul(val[3], logic.IntLit(v.span(u.Elem())))))
	case *types.Map:
		return logic.Implies(logic.Ne(val[0], zero), logic.Select(logic.Select(rel, val[0]), logic.IntLit(0)))
	case *types.Struct:
		var facts []*logic.Term
		for i := range u.NumFields() {
			if lo, hi, ok := fieldLeaves(t, i); ok {
				facts = append(facts, v.reachedBy(rel, val[lo:hi], u.Field(i).Type()))
			}
		}
		return logic.And(facts...)
	}
	return logic.True()
}

// holdsMemory reports whether a value of a type refers to memory directly,
// not through an interface value or a function value.
func holdsMemory(t types.Type) bool {
	if _, isPointer := pointee(t); isPointer {
		return true
	}
	switch u := t.Underlying().(type) {
	case *types.Slice, *types.Map:
		return true
	case *types.Struct:
		for field := range u.Fields() {
			if holdsMemory(field.Type()) {
				return true
			}
		}
	}
	return false
}

// enterReaches assumes, for every parameter that a Modifies clause lists
// as a footprint, that its footprint on entry holds nothing the other
// parameters reach without going through an interface value. Only a
// declared function assumes it: a contract of a type is met by code that
// the callers of a value cannot be asked about.
func (v *fnVerifier) enterReaches(st *state) {
	fn := v.fn
	if fn.decl == nil || fn.trust != nil || fn.valueOf != nil || fn.methodOf != nil {
		return
	}
	for _, t := range v.frame {
		if !t.fp || t.param == nil || v.entry[t.param] == nil {
			continue
		}
		r := separation{param: t.param, rel: logic.Const("reach $"+t.param.Name(), reachSort), home: home(v.entry[t.param][0])}
		v.inputs[r.rel.Name] = true
		for _, other := range fn.params {
			if other != t.param && v.entry[other] != nil && holdsMemory(other.Type()) {
				st.assume(v.reachedBy(r.rel, v.entry[other], other.Type()))
			}
		}
		v.reaches = append(v.reaches, r)
	}
}

// noteReached states, for a value read from memory, that what the value
// held on entry is reached when the cell that held it is: the parameters'
// reach is closed under what memory referred to on entry. The fact is
// about the entry contents of the cells, which the read gives when nothing
// wrote them since.
func (v *fnVerifier) noteReached(sink *state, cells []cell, ref, at *logic.Term, t types.Type) {
	if sink == nil || len(v.reaches) == 0 || len(cells) == 0 || !holdsMemory(t) {
		return
	}
	entry := make(value, len(cells))
	for i, c := range cells {
		region := logic.Const(entryRegion+c.key, logic.SeqOf(logic.SeqOf(c.sort)))
		entry[i] = logic.Select(logic.Select(region, ref), logic.Add(at, logic.IntLit(c.off)))
	}
	holder := logic.Add(at, logic.IntLit(cells[0].off))
	for _, r := range v.reaches {
		fact := logic.Implies(logic.Select(logic.Select(r.rel, ref), holder), v.reachedBy(r.rel, entry, t))
		if note := "reached " + fact.String(); !sink.noted[note] {
			sink.noted[note] = true
			sink.assume(fact)
		}
	}
}

// noteReachedValue is noteReached for a value of a map, whose cells are
// keyed by the map and the number of its key.
func (v *fnVerifier) noteReachedValue(sink *state, t types.Type, ref, key *logic.Term) {
	_, elem := mapParts(t)
	if sink == nil || len(v.reaches) == 0 || !holdsMemory(elem) {
		return
	}
	leaves, _ := layoutOf(elem)
	entry := make(value, len(leaves))
	for i, lf := range leaves {
		region := logic.Const(entryRegion+mapOwner(t)+"#val"+lf.path, logic.SeqOf(logic.SeqOf(lf.sort)))
		entry[i] = logic.Select(logic.Select(region, ref), mapKey(key))
	}
	for _, r := range v.reaches {
		fact := logic.Implies(logic.Select(logic.Select(r.rel, ref), logic.IntLit(0)), v.reachedBy(r.rel, entry, elem))
		if note := "reached " + fact.String(); !sink.noted[note] {
			sink.noted[note] = true
			sink.assume(fact)
		}
	}
}

// checkReachedApart refuses a call of a verified function that relies on
// what one argument reaches lying outside the footprint of another, which
// showing at a call is not built yet.
func (v *fnVerifier) checkReachedApart(call *ast.CallExpr, fn *funcInfo, args map[*types.Var]value, written []target, passed map[*types.Var]string, name string) {
	if fn.trust != nil || fn.valueOf != nil || fn.methodOf != nil {
		return
	}
	for _, t := range written {
		if !t.fp || t.param == nil {
			continue
		}
		for _, other := range fn.params {
			if other != t.param && args[other] != nil && holdsMemory(other.Type()) {
				v.unsupported(call.Pos(), fmt.Sprintf("%s relies on what is passed to it as %s lying outside the footprint of what is passed as %s, "+
					"and showing that at a call is not supported yet", name, passed[other], passed[t.param]))
			}
		}
	}
}

// refuseStatesBehind refuses a call through a value whose type has states
// of a method that writes behind its receiver, as a Write that an
// interface embedding io.Closer takes from another: what such a write does
// to the states of the value is not modelled yet.
func (v *fnVerifier) refuseStatesBehind(call *ast.CallExpr, fn *funcInfo, sel *ast.SelectorExpr, callee *types.Func) {
	if writesBehind(fn) && v.hasFootprint(fn.receiver.Type()) && v.hasStates(v.info.TypeOf(sel.X)) {
		v.unsupported(call.Pos(), fmt.Sprintf("%s writes behind its receiver, and %s has states; a call that writes behind the receiver of a value with states "+
			"is not supported yet", methodTitle(callee), types.ExprString(sel.X)))
	}
}
