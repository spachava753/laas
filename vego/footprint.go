package vego

import (
	"fmt"
	"go/token"
	"go/types"
	"slices"
	"strings"

	"gopkg.in/yaml.v3"

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
// A value has a footprint when its interface type has a method declared on
// an interface without states whose contract lists its receiver, in source
// or in a trust file. Modifies of such a value covers its footprint, and
// its states when its type has states. A method declared on an interface
// with states that lists its receiver changes the states and nothing else,
// as before; and a call writes the states of its receiver only through
// such a method (F7 (a) of the design review): Write of an io.WriteCloser,
// declared on io.Writer, keeps closed.

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
	// No row holds a cell of the storage of an assigned package-level
	// variable (V1), so an epoch keeps it.
	if key == footprintRegion || isVarRegion(key) {
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
		if v.frameNames != nil {
			// A frame reads it before the function does: it is made again,
			// the same, when the function first reads it, so that
			// everything after the frame is what it was without it.
			v.frameNames.materialized = append(v.frameNames.materialized, name)
			return
		}
		v.forwards[joined.forward].produced = append(v.forwards[joined.forward].produced, name)
		return
	}
	flat := !sort.Elem().IsSeq()
	v.layers[name] = &layer{prev: e.before.region(key, sort), bound: e.bound, targets: e.targets, key: key, flat: flat}
	if v.frameNames != nil {
		v.frameNames.materialized = append(v.frameNames.materialized, name)
	}
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
	for key, region := range st.mem {
		if isVarRegion(key) {
			mem[key] = region
		}
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
		// What a callee promised of a stretch of memory, at this cell: it
		// lies in the row of one of the values it named.
		for _, claim := range v.stretchClaims[at.Name] {
			held := logic.And(claim.holds, logic.Eq(alloc, claim.ref), logic.Le(claim.lo, pos), logic.Lt(pos, claim.hi))
			var options []*logic.Term
			for _, y := range claim.ys {
				options = append(options, logic.And(logic.Not(isNilRef(y.val)), logic.Select(logic.Select(logic.Select(at, logic.Select(homes, y.val[0])), alloc), pos)))
			}
			facts = append(facts, logic.Implies(held, logic.Or(options...)))
		}
		// What a callee promised of a row in this region, at this cell.
		for _, claim := range v.rowClaims[at.Name] {
			held := logic.And(claim.holds, logic.Eq(home, claim.home), cellOf(at))
			options, known := v.newOrInParts(alloc, pos, claim.before, claim.ys, claim.yRows)
			facts = append(facts, logic.Implies(held, options))
			facts = append(facts, known...)
		}
		switch {
		case at.Name == entryRegion+footprintRegion:
			// What existed on entry held only what existed on entry; a home
			// made since has a footprint this row does not describe.
			facts = append(facts, logic.Implies(logic.And(logic.Lt(home, v.entryBrk), cellOf(at)), logic.And(logic.Lt(logic.IntLit(0), alloc), logic.Lt(alloc, v.entryBrk))))
			// No row holds a cell of a struct variable whose address is
			// closed (K1).
			if apart := v.apartFromClosed(alloc); apart != nil {
				facts = append(facts, logic.Implies(cellOf(at), apart))
			}
		case v.layers[at.Name] != nil && v.layers[at.Name].follows != nil:
			// A row that holds the owned field's cell follows what is
			// stored there: the row of a converted owner grows with it.
			known := v.layers[at.Name]
			holds, more := v.rowAt(known.prev, home, known.follows.ref, known.follows.pos)
			stored, more2 := known.follows.stored(alloc, pos)
			facts = append(facts, more...)
			facts = append(facts, more2...)
			facts = append(facts, logic.Iff(cellOf(at), logic.Or(cellOf(known.prev), logic.And(holds, stored))))
			pending = append(pending, known.prev)
		case v.layers[at.Name] != nil && v.layers[at.Name].emptied != nil:
			known := v.layers[at.Name]
			defined := logic.False()
			if known.defines != nil {
				var more []*logic.Term
				defined, more = known.defines(alloc, pos)
				facts = append(facts, more...)
			}
			facts = append(facts, logic.Implies(logic.Eq(home, known.emptied), logic.Iff(cellOf(at), defined)),
				logic.Implies(logic.Ne(home, known.emptied), logic.Iff(cellOf(at), cellOf(known.prev))))
			pending = append(pending, known.prev)
		case v.layers[at.Name] != nil:
			known := v.layers[at.Name]
			if !known.growth {
				panic("vego: internal error: the footprint region has a layer that is not a growth layer")
			}
			// A home made since the bound described no value before it,
			// so only the rows of homes that existed keep their cells.
			kept := logic.And(logic.Lt(alloc, known.bound), logic.Lt(home, known.bound))
			if known.apart != nil {
				untouched, more := v.untouchedRow(known, home)
				facts = append(facts, more...)
				kept = logic.Or(kept, logic.And(logic.Lt(home, known.bound), untouched))
			}
			if known.skipped != nil {
				kept = logic.Or(kept, known.skipped)
			}
			facts = append(facts, logic.Implies(kept, logic.Iff(cellOf(at), cellOf(known.prev))))
			if known.after != nil {
				facts = append(facts, logic.Implies(cellOf(at), logic.And(logic.Lt(logic.IntLit(0), alloc), logic.Lt(alloc, known.after))))
			}
			// Nor does the row of a value the call made (K1).
			if apart := v.apartFromClosed(alloc); apart != nil {
				facts = append(facts, logic.Implies(logic.And(logic.Le(known.bound, home), cellOf(at)), apart))
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
// interface type that has a method that writes behind its receiver; see
// the comment at the top.
func (pv *pkgVerifier) hasFootprint(t types.Type) bool {
	if !isIface(t) {
		return false
	}
	// A method writes behind its receiver when its contract lists the
	// receiver and the interface that declares it has no states. One
	// declared on an interface with states that lists its receiver changes
	// the states of the value and nothing else, as it did before
	// footprints (D2, decided by the orchestrator: no contract that is
	// legal changes its meaning).
	for method := range t.Underlying().(*types.Interface).Methods() {
		if pv.footprintMethod(method) {
			return true
		}
	}
	return false
}

// footprintMethod reports whether a method of an interface writes behind
// its receiver: its contract lists the receiver and its interface has no
// states, or it lists behind(r) of its receiver r (F28), on an interface
// with states, where r alone names the states.
func (pv *pkgVerifier) footprintMethod(method *types.Func) bool {
	fn := pv.methodContract(method)
	if owner := declaringInterface(method); owner != nil && !pv.hasStates(owner.Type()) && writesBehind(fn) {
		return true
	}
	return listsBehind(fn)
}

// listsBehind reports whether a contract lists behind(r) of its receiver.
func listsBehind(fn *funcInfo) bool {
	if fn == nil || fn.receiver == nil {
		return false
	}
	return slices.ContainsFunc(fn.modifies, func(m *modTarget) bool { return m.behind && m.name == fn.receiver.Name() })
}

// writesBehind reports whether the contract of a method of an interface
// lists its receiver in Modifies.
func writesBehind(fn *funcInfo) bool {
	if fn == nil || fn.receiver == nil {
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
	// A nil interface value has no footprint: none of its methods can run.
	if t.ref.Op == logic.OpSelect && t.ref.Args[0] == homes {
		conditions = append(conditions, isNilRef(value{t.ref.Args[1]}))
	}
	if key == stateRegion {
		conditions = append(conditions, logic.Eq(ref, t.ref))
	}
	if t.skipped != nil {
		conditions = append(conditions, t.skipped)
	}
	return logic.Or(conditions...), facts
}

// separation is what a function assumes of a parameter whose footprint
// its Modifies lists: on entry, the footprint holds no cell that the other
// parameters reach without going through an interface value. A cell is so
// reached when one of the other parameters refers to it directly (direct,
// decided by directlyAt at the cell, with no quantifier), or when rel holds
// of it, which the facts of noteReached give for what memory held on entry
// at a reached cell. home is the home of the parameter on entry.
type separation struct {
	// param is the parameter whose footprint it is, or variable the
	// interface variable whose value on entry has it.
	param    *types.Var
	variable *types.Var
	// field is set for the footprint of p.field, a field that a
	// notWrittenBy declaration covers: what p reaches is among the roots
	// (F28).
	field  string
	rel    *logic.Term
	home   *logic.Term
	direct []passedValue
	// For a part that an owned field of a declaration in source gives
	// (C3 of ownership in source): contains tells the part's cells on
	// entry, in place of a row; parts tells the other parts' cells, which
	// are reached as the other parameters are; and cuts are the owned
	// cells of the owner's struct and of the structs it owns, whose
	// contents the reach does not follow, since they are the parts.
	contains func(ref, position *logic.Term) *logic.Term
	parts    []func(ref, position *logic.Term) *logic.Term
	cuts     [][2]*logic.Term
	// reachable holds the types, by typeKey, that the other parameters
	// reach; see reachesType.
	reachable map[string]bool
}

// reachesType reports whether a value of type t can lie in memory that the
// other parameters reach without going through an interface value: t is,
// or is held by value in, a type reached from theirs through pointers,
// slices, maps, and fields.
func (r *separation) reachesType(t types.Type) bool {
	if r.reachable == nil {
		r.reachable = map[string]bool{}
		var walk func(t types.Type)
		walk = func(t types.Type) {
			key := typeKey(t)
			if r.reachable[key] {
				return
			}
			r.reachable[key] = true
			switch u := t.Underlying().(type) {
			case *types.Pointer:
				walk(u.Elem())
			case *types.Slice:
				walk(u.Elem())
			case *types.Array:
				walk(u.Elem())
			case *types.Map:
				walk(u.Key())
				walk(u.Elem())
			case *types.Struct:
				for field := range u.Fields() {
					walk(field.Type())
				}
			}
		}
		for _, d := range r.direct {
			walk(d.t)
		}
	}
	return r.reachable[typeKey(t)]
}

// passedValue is a parameter's value on entry with its type.
type passedValue struct {
	val value
	t   types.Type
}

// reachedAt states that a cell is reached: a parameter refers to it
// directly, or rel holds of it.
func (r separation) reachedAt(v *fnVerifier, ref, position *logic.Term) *logic.Term {
	cases := []*logic.Term{logic.Select(logic.Select(r.rel, ref), position)}
	for _, d := range r.direct {
		cases = append(cases, v.directlyAt(d.val, d.t, ref, position))
	}
	for _, part := range r.parts {
		cases = append(cases, part(ref, position))
	}
	return logic.Or(cases...)
}

// directlyAt states that a value of a type refers directly to a cell: the
// cell lies in the struct a pointer points to, in the array of a slice from
// its start to its capacity, or is the cell of a map, or a field of a
// struct does.
func (v *fnVerifier) directlyAt(val value, t types.Type, ref, position *logic.Term) *logic.Term {
	zero := logic.RefLit(0)
	inRange := func(at, lo, hi *logic.Term) *logic.Term {
		return logic.And(logic.Ne(at, zero), logic.Eq(ref, at), logic.Le(lo, position), logic.Lt(position, hi))
	}
	if object, isPointer := pointee(t); isPointer {
		// A hidden field is not reached through the struct that holds it
		// (scoped.go): code that is not verified writes it.
		in := inRange(val[0], val[1], logic.Add(val[1], logic.IntLit(v.span(object))))
		for _, off := range v.hiddenOffsets(object) {
			in = logic.And(in, logic.Ne(position, logic.Add(val[1], logic.IntLit(off))))
		}
		return in
	}
	switch u := t.Underlying().(type) {
	case *types.Slice:
		return inRange(val[0], val[1], logic.Add(val[1], logic.Mul(val[3], logic.IntLit(v.span(u.Elem())))))
	case *types.Map:
		return logic.And(logic.Ne(val[0], zero), logic.Eq(ref, val[0]), logic.Eq(position, logic.IntLit(0)))
	case *types.Struct:
		var cases []*logic.Term
		for i := range u.NumFields() {
			if hiddenOf(t, i) != nil {
				continue
			}
			if lo, hi, ok := fieldLeaves(t, i); ok && holdsMemory(u.Field(i).Type()) {
				cases = append(cases, v.directlyAt(val[lo:hi], u.Field(i).Type(), ref, position))
			}
		}
		return logic.Or(cases...)
	}
	return logic.False()
}

// reachApart states, at one cell, what the separation of every listed
// footprint parameter says there.
func (v *fnVerifier) reachApart(ref, position *logic.Term) *logic.Term {
	var facts []*logic.Term
	for _, r := range v.reaches {
		reached := r.reachedAt(v, ref, position)
		var inRow *logic.Term
		if r.contains != nil {
			inRow = r.contains(ref, position)
		} else {
			var rowFacts []*logic.Term
			inRow, rowFacts = v.rowAt(logic.Const(entryRegion+footprintRegion, footprintSort), r.home, ref, position)
			facts = append(facts, rowFacts...)
		}
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
	// A footprint the frame lists covers the cells in its row, and a
	// stretch it lists the cells in the stretch: every position of an
	// object is one of its leaves, so a stretch covers what a footprint
	// holds there, as the footprint of a converted *Counter is the struct
	// that Modifies c lists. A map it lists whole covers the map.
	var candidates []int
	for i, f := range v.frame {
		if f.fp || (!f.row && f.ref != nil && (f.mapType != nil && f.key == nil || f.mapType == nil && f.lo != nil && f.hi != nil)) {
			candidates = append(candidates, i)
		}
	}
	alloc, position := v.fresh("cell", logic.Ref), v.fresh("at", logic.Int)
	probe := st.clone()
	cell, facts := v.rowAt(t.rows, t.ref, alloc, position)
	framed := make([]*logic.Term, len(v.frame))
	for _, i := range candidates {
		f := v.frame[i]
		switch {
		case f.fp:
			var more []*logic.Term
			framed[i], more = v.rowAt(f.rows, f.ref, alloc, position)
			facts = append(facts, more...)
		case f.mapType != nil:
			framed[i] = logic.And(logic.Eq(alloc, f.ref), logic.Eq(position, logic.IntLit(0)))
		default:
			framed[i] = logic.And(logic.Eq(alloc, f.ref), logic.Le(f.lo, position), logic.Lt(position, f.hi))
		}
	}
	for _, fact := range facts {
		probe.assume(fact)
	}
	// A nil interface value has no footprint: none of its methods can run,
	// since a call through it panics first.
	held := cell
	if t.ref.Op == logic.OpSelect && t.ref.Args[0] == homes {
		held = logic.And(logic.Not(isNilRef(value{t.ref.Args[1]})), cell)
	}
	allowed := func(without int) *logic.Term {
		covered := []*logic.Term{logic.Le(v.entryBrk, alloc)}
		for _, i := range candidates {
			if v.frame[i].mod != without {
				covered = append(covered, framed[i])
			}
		}
		return logic.Implies(held, logic.Or(covered...))
	}
	if result := v.attempt(probe, guard, allowed(-1)); result != solver.Proved {
		for _, i := range candidates {
			v.used[i] = true
		}
		// The message speaks of footprints the frame lists.
		listed := 0
		for _, i := range candidates {
			if v.frame[i].fp {
				listed++
			}
		}
		switch {
		case remedy != "":
			v.report(pos, "%s, which %s may not modify; %s%s", what, v.fn.obj.Name(), remedy, limitNote(result))
		case listed == 0 && v.fn.spelling().receiver != nil && v.hasStates(v.fn.spelling().receiver.Type()) && !listsBehind(v.fn.spelling()) &&
			slices.ContainsFunc(v.fn.spelling().modifies, func(m *modTarget) bool { return m.name == v.fn.spelling().receiver.Name() }):
			// A method of an interface with states that lists its receiver
			// changes its states only (D2; F18 of the review of step 5).
			r := v.fn.spelling().receiver.Name()
			v.report(pos, "%s, which %s may not modify; the contract of %s lists %s, which on an interface with states covers its states only; "+
				"list behind(%s) too to let the method write behind its receiver%s", what, v.fn.obj.Name(), v.fn.obj.Name(), r, r, limitNote(result))
		case listed == 0 && (v.fn.spelling().valueOf != nil || v.fn.spelling().methodOf != nil):
			v.report(pos, "%s, which %s may not modify; the contract of %s does not list it, so code that writes it cannot be used there%s",
				what, v.fn.obj.Name(), v.fn.obj.Name(), limitNote(result))
		case listed == 0 && unlisted != "":
			v.report(pos, "%s, which %s may not modify; %s%s", what, v.fn.obj.Name(), unlisted, limitNote(result))
		case listed == 0:
			v.report(pos, "%s, which %s may not modify; list it in a // @Modifies clause%s", what, v.fn.obj.Name(), limitNote(result))
		default:
			v.report(pos, "%s, which %s may not modify: no footprint its // @Modifies clauses list is known to hold it; "+
				"a clause covers what its path referred to when %s was called%s", what, v.fn.obj.Name(), v.fn.obj.Name(), limitNote(result))
		}
		return
	}
	defer v.asking(modifiesCheck)()
	v.markNeeded(candidates, func(mod int) bool { return v.quickly(probe, guard, allowed(mod)) })
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
	inRange := func(ref, lo, hi *logic.Term, skip ...int64) *logic.Term {
		j := v.bound("k")
		cellOf := logic.Select(logic.Select(rel, ref), j)
		in := logic.And(logic.Le(lo, j), logic.Lt(j, hi))
		for _, off := range skip {
			in = logic.And(in, logic.Ne(j, logic.Add(lo, logic.IntLit(off))))
		}
		return logic.Implies(logic.Ne(ref, zero), logic.Forall(j, logic.Implies(in, cellOf)))
	}
	if object, isPointer := pointee(t); isPointer {
		// A hidden field is not reached through its struct (scoped.go).
		return inRange(val[0], val[1], logic.Add(val[1], logic.IntLit(v.span(object))), v.hiddenOffsets(object)...)
	}
	switch u := t.Underlying().(type) {
	case *types.Slice:
		return inRange(val[0], val[1], logic.Add(val[1], logic.Mul(val[3], logic.IntLit(v.span(u.Elem())))))
	case *types.Map:
		return logic.Implies(logic.Ne(val[0], zero), logic.Select(logic.Select(rel, val[0]), logic.IntLit(0)))
	case *types.Struct:
		var facts []*logic.Term
		for i := range u.NumFields() {
			if hiddenOf(t, i) != nil {
				continue
			}
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
	v.reaches = nil
	if fn.decl == nil || fn.trust != nil || fn.valueOf != nil || fn.methodOf != nil {
		return
	}
	for i, t := range v.frame {
		// The footprint of what an interface variable the function lists
		// by itself holds on entry: what the parameters reach lies outside
		// it, which every verified caller proves (checkReachedApart) and
		// "What a proof assumes" states of the others. A write through the
		// variable after it was assigned is a write through another value,
		// which this says nothing of.
		if t.fp && t.fromVar != nil {
			key := t.fromVar.Name()
			if t.fromVar.Pkg() != nil {
				key = t.fromVar.Pkg().Path() + "." + key
			}
			r := separation{variable: t.fromVar, rel: logic.Const("reach var "+key, reachSort), home: t.ref}
			for _, param := range fn.params {
				if v.entry[param] != nil && holdsMemory(param.Type()) {
					r.direct = append(r.direct, passedValue{val: v.entry[param], t: param.Type()})
				}
			}
			r.direct = append(r.direct, v.groupRoots(st)...)
			if len(r.direct) > 0 {
				v.inputs[r.rel.Name] = true
				v.reaches = append(v.reaches, r)
			}
			continue
		}
		// The footprint of a parameter, or of an interface value that a
		// parameter that owns memory owns, as the writer a *bufio.Writer
		// keeps: what the other parameters reach lies outside it.
		param, at := t.param, t.ref
		field := ""
		if t.part {
			param = t.ownerParam
		} else if param != nil && v.entry[param] != nil {
			at = home(v.entry[param][0])
		} else if t.fp && t.mod < len(fn.modifies) {
			// The footprint of p.Body, of a field that notWrittenBy
			// covers: what p reaches lies outside it too, as the shipped
			// declaration claims (F28).
			if root := v.notWrittenRoot(fn, fn.modifies[t.mod]); root != nil {
				param, field = root, fn.modifies[t.mod].steps[0].field
			}
		}
		if !t.fp && !t.sourcePart || param == nil || v.entry[param] == nil {
			continue
		}
		name := "reach $" + param.Name()
		if t.part {
			name = fmt.Sprintf("reach $%s owned %d", param.Name(), i)
		}
		if field != "" {
			name += "." + field
		}
		r := separation{param: param, field: field, rel: logic.Const(name, reachSort), home: at}
		v.inputs[r.rel.Name] = true
		for _, other := range fn.params {
			if (other != param || field != "") && v.entry[other] != nil && holdsMemory(other.Type()) {
				r.direct = append(r.direct, passedValue{val: v.entry[other], t: other.Type()})
			}
		}
		// What a variable of a group refers to is reached only through the
		// variable, so it lies outside every footprint too (F35 of the review
		// of step 2 of part 2).
		r.direct = append(r.direct, v.groupRoots(st)...)
		if t.sourcePart {
			v.separatePart(&r, i, param)
			v.partApartFromParams(st, t, param)
		}
		v.reaches = append(v.reaches, r)
	}
}

// noteReached states, for a value read from memory, that what the value
// held on entry is reached when the cell that held it is: the parameters'
// reach is closed under what memory referred to on entry. The fact is
// about the entry contents of the cells, which the read gives when nothing
// wrote them since.
func (v *fnVerifier) noteReached(sink *state, cells []cell, ref, at *logic.Term, t, container types.Type) {
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
		// A cell holding a t, in a value of the container's type, is
		// reached only if both can be reached from the other parameters
		// by their types; otherwise the fact is about no state of Go, and
		// is left out.
		if !r.reachesType(t) || !r.reachesType(container) {
			continue
		}
		reached := r.reachedAt(v, ref, holder)
		// The reach does not follow an owned cell of the owner's struct
		// or of a struct it owns: those cells hold the parts.
		if len(r.cuts) > 0 {
			var cut []*logic.Term
			for _, c := range r.cuts {
				cut = append(cut, logic.And(logic.Eq(ref, c[0]), logic.Eq(holder, c[1])))
			}
			reached = logic.And(reached, logic.Not(logic.Or(cut...)))
		}
		fact := logic.Implies(reached, v.reachedBy(r.rel, entry, t))
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
		if !r.reachesType(elem) {
			continue
		}
		fact := logic.Implies(r.reachedAt(v, ref, logic.IntLit(0)), v.reachedBy(r.rel, entry, elem))
		if note := "reached " + fact.String(); !sink.noted[note] {
			sink.noted[note] = true
			sink.assume(fact)
		}
	}
}

// growsNothing reports whether a call can make nothing it creates part of
// a footprint: it is not written to, it modifies no footprint, and it
// returns nothing and writes nothing that can hold an interface value. A
// call that does no such thing needs no growth layer, which keeps the chain
// of layers short in a function that never meets a footprint. A target
// that a trusted entry lists under stores receives only memory the call
// made, which joins no row (F28; see callPollutes): a row grows only by
// what its value's methods create or, for a converted value, by its
// definition and follow layers, and the methods of a value from code that
// is not verified do not write through what another call stored into
// memory the value handed out, by the clause F33 of part 1 added.
func (v *fnVerifier) growsNothing(fn *funcInfo) bool {
	if writesFootprint(v, fn) {
		return false
	}
	sig := fn.obj.Type().(*types.Signature)
	for result := range sig.Results().Variables() {
		if reachesCode(result.Type(), map[types.Type]bool{}) {
			return false
		}
	}
	// What an entry lists under stores receives only memory the call made,
	// which joins no row (see the case of stores in callPollutes).
	return !v.targetsHold(fn, true)
}

// ownsDecl is what a shipped file declares a struct type of another module
// to own: the fields whose memory is part of the footprint of a value of
// the type, with why that is true of every method of the type.
type ownsDecl struct {
	// pkg and typ name the type.
	pkg, typ string
	fields   []string
	reason   string
	line     int
	// length, when set, is what |x| of a value of the type is: a formula
	// over the type's own fields, read in the package of the type as an
	// invariant is, as |buf| for a strings.Builder. holds are formulas over
	// the same fields that every value of the type satisfies, claims of
	// the declaration that are stated wherever the length is read. The
	// texts are kept for messages and the tests.
	length     *logic.Node
	lengthText string
	holds      []*logic.Node
	holdsText  []string
}

// addOwns reads the owns section of a file: a mapping from a struct type,
// as in bytes.Buffer, to the fields it owns and a reason. Only the shipped
// files may have one: the layout a declaration names is that of the
// standard library, the same in every module.
func (f *trustFile) addOwns(node *yaml.Node) {
	if !f.shipped {
		f.problem(node.Line, "owns can be declared only in the shipped files: what a type of the project owns is declared on the type, and what a type of another module owns depends on fields its module may change")
		return
	}
	if node.Kind != yaml.MappingNode {
		f.problem(node.Line, "owns must map types to the fields they own")
		return
	}
	for i := 0; i+1 < len(node.Content); i += 2 {
		typeName, body := node.Content[i], node.Content[i+1]
		pkg, typ, ok := splitTypeName(typeName.Value)
		if !ok || body.Kind != yaml.MappingNode {
			f.problem(typeName.Line, "owns: %q must be a type named by its package, mapped to its fields and a reason", typeName.Value)
			continue
		}
		decl := ownsDecl{pkg: pkg, typ: typ, line: typeName.Line}
		for k := 0; k+1 < len(body.Content); k += 2 {
			switch field, value := body.Content[k], body.Content[k+1]; field.Value {
			case "fields":
				for _, name := range value.Content {
					decl.fields = append(decl.fields, name.Value)
				}
			case "reason":
				decl.reason = strings.TrimSpace(value.Value)
			case "length":
				node, err := logic.ParseFormula(value.Value)
				if err != nil {
					f.problem(value.Line, "owns of %s: length %q: %v", typeName.Value, value.Value, err)
					continue
				}
				decl.length, decl.lengthText = node, value.Value
			case "holds":
				for _, item := range value.Content {
					node, err := logic.ParseFormula(item.Value)
					if err != nil {
						f.problem(item.Line, "owns of %s: holds %q: %v", typeName.Value, item.Value, err)
						continue
					}
					decl.holds, decl.holdsText = append(decl.holds, node), append(decl.holdsText, item.Value)
				}
			default:
				f.problem(field.Line, "unknown field %q in owns of %s; expected fields, length, holds, and reason", field.Value, typeName.Value)
			}
		}
		if len(decl.fields) == 0 || decl.reason == "" {
			f.problem(typeName.Line, "owns of %s needs the fields it owns and a reason", typeName.Value)
			continue
		}
		if len(decl.holds) > 0 && decl.length == nil {
			f.problem(typeName.Line, "owns of %s: holds is stated where the length is read, so it needs a length", typeName.Value)
			continue
		}
		f.owns[stateKey(pkg, typ)] = decl
	}
}

// ownedFields returns the indices of the fields of a struct type whose
// memory a value of the type owns, by the shipped declarations. A field
// that the declaration names and the type does not have, or that holds
// nothing a footprint can hold, panics: TestOwnsDeclarations holds every
// declaration against the types of the toolchain.
func (pv *pkgVerifier) ownedFields(t types.Type) []int {
	return ownedFieldsOf(t)
}

// ownedFieldsOf is ownedFields, which needs nothing of a package.
func ownedFieldsOf(t types.Type) []int {
	decl, u := ownsDeclOf(t)
	if decl == nil {
		// Or by a declaration in source (owns.go).
		return sourceOwnedFields(t)
	}
	var indices []int
	for _, name := range decl.fields {
		index := -1
		for i := range u.NumFields() {
			if u.Field(i).Name() == name {
				index = i
			}
		}
		if index < 0 {
			panic(fmt.Sprintf("vego: internal error: the shipped declaration that %s owns %s names no field of it", t, name))
		}
		// A field can be owned when it holds a pointer to a struct, a
		// slice, a map, or an interface value.
		ft := u.Field(index).Type()
		if _, isPointer := pointee(ft); !isPointer && !isSlice(ft) && !isMap(ft) && !isIface(ft) {
			panic(fmt.Sprintf("vego: internal error: the shipped declaration that %s owns %s names no field that can be owned", t, name))
		}
		indices = append(indices, index)
	}
	return indices
}

// ownsDeclOf returns the shipped declaration of what a value of a struct
// type owns, and the struct. Like a state (statesOf), a declaration is
// found through the package of the struct's fields and matched by the
// underlying struct, tags ignored, so that a type defined over an owner,
// as type B strings.Builder, owns what the owner owns: it shares its
// memory and its methods' panics, and only the name differs (F1 of the
// design review).
func ownsDeclOf(t types.Type) (*ownsDecl, *types.Struct) {
	decl, u, _ := ownsDeclared(t)
	return decl, u
}

// ownsDeclared is ownsDeclOf, which also returns the type the declaration
// names, whose fields a formula of the declaration reads in its package.
func ownsDeclared(t types.Type) (*ownsDecl, *types.Struct, types.Type) {
	u, isStruct := types.Unalias(t).Underlying().(*types.Struct)
	if !isStruct {
		return nil, nil, nil
	}
	var home *types.Package
	for field := range u.Fields() {
		if field.Pkg() != nil {
			home = field.Pkg()
			break
		}
	}
	if home == nil {
		return nil, nil, nil
	}
	plain := untagged(u)
	for _, file := range shippedContracts() {
		for _, decl := range file.owns {
			if decl.pkg != home.Path() {
				continue
			}
			obj, ok := home.Scope().Lookup(decl.typ).(*types.TypeName)
			if ok && types.Identical(plain, untagged(obj.Type().Underlying())) {
				return &decl, u, obj.Type()
			}
		}
	}
	return nil, nil, nil
}

// ownedParts returns, for a pointer to a struct whose type owns some of
// its fields, a target for what each owned field refers to, read in memory:
// the array of a slice from its start to its capacity, a map, the struct a
// pointer points to with what it owns in turn, and the footprint and the
// states of an interface value. seen keeps a type that owns itself through
// its fields from unfolding for ever; the shipped declarations have none.
func (v *fnVerifier) ownedParts(sink *state, mem memory, ptr value, t types.Type, seen map[types.Type]bool) []target {
	object, isPointer := pointee(t)
	if !isPointer || seen[object] {
		return nil
	}
	fields := v.ownedFields(object)
	inline := v.inlineOwners(object)
	if len(fields) == 0 && len(inline) == 0 {
		return nil
	}
	seen[object] = true
	defer delete(seen, object)
	var parts []target
	// What an owner held by value owns, as a strings.Builder in a field
	// of a struct of the project, the struct owns through it (D7).
	for _, field := range inline {
		parts = append(parts, v.ownedParts(sink, mem, field.at(ptr), field.ptr, seen)...)
	}
	source := len(sourceOwnedFields(object)) > 0
	for _, index := range fields {
		val, ft, ok := v.member(sink, mem, ptr, t, index)
		if !ok {
			continue
		}
		first := len(parts)
		switch {
		case isSlice(ft):
			lo, hi := v.extent(val, ft)
			parts = append(parts, target{cells: v.cellsOf(elemType(ft)), elem: elemType(ft), ref: val[0], lo: lo, hi: hi})
		case isMap(ft):
			parts = append(parts, target{mapType: ft, ref: val[0]})
		case isIface(ft):
			if v.hasFootprint(ft) {
				parts = append(parts, target{fp: true, ref: home(val[0]), rows: mem.region(footprintRegion, footprintSort)})
			}
			// An owner of the project owns the states of what its owned
			// interface value holds, whatever its interface declares, as
			// Modifies of an interface value covers them.
			if v.hasStates(ft) || source {
				parts = append(parts, target{row: true, cells: []cell{stateCell}, ref: home(val[0])})
			}
		default:
			inner, _ := pointee(ft)
			size := v.pass.TypesSizes.Sizeof(inner)
			parts = append(parts, target{cells: v.cellsOf(inner), ref: val[0], lo: val[1], hi: logic.Add(val[1], logic.IntLit(size)), single: true,
				base: &structValue{t: inner, ref: val[0], at: val[1]}})
		}
		for i := first; i < len(parts); i++ {
			parts[i].sourcePart = source
		}
		if _, isPointer := pointee(ft); isPointer && !isIface(ft) {
			parts = append(parts, v.ownedParts(sink, mem, val, ft, seen)...)
		}
	}
	return parts
}

// ownedSites returns the sites a loop may write through what the owned
// fields of a pointer's struct refer to, with no root: the loop forgets
// them by region.
func (v *fnVerifier) ownedSites(t types.Type, seen map[types.Type]bool) []site {
	object, isPointer := pointee(t)
	if !isPointer || seen[object] {
		return nil
	}
	seen[object] = true
	defer delete(seen, object)
	u, _ := object.Underlying().(*types.Struct)
	var sites []site
	for _, field := range v.inlineOwners(object) {
		sites = append(sites, v.ownedSites(field.ptr, seen)...)
	}
	for _, index := range v.ownedFields(object) {
		ft := u.Field(index).Type()
		switch {
		case isSlice(ft):
			sites = append(sites, site{cells: v.cellsOf(elemType(ft)), elem: elemType(ft)})
		case isMap(ft):
			sites = append(sites, site{mapType: ft})
		case isIface(ft):
			if v.hasFootprint(ft) {
				sites = append(sites, site{fp: true})
			}
			if v.hasStates(ft) || len(sourceOwnedFields(object)) > 0 {
				sites = append(sites, site{row: true, cells: []cell{stateCell}})
			}
		default:
			inner, _ := pointee(ft)
			lo, hi := bounds(v.cellsOf(inner))
			sites = append(sites, site{cells: v.cellsOf(inner), lo: lo, hi: hi})
			sites = append(sites, v.ownedSites(ft, seen)...)
		}
	}
	return sites
}

// ownedFreshSeen states that what the owned fields of a pointer's struct
// refer to was allocated at or past a bound, read in memory: the footprint
// of an owner is new when all of it is. A nil pointer, a nil map, and a
// slice without capacity refer to nothing, which is new. seen holds the
// types entered, so that a type that holds itself through its owned
// pointers is entered once. Each
// owned field gives one fact, by its kind: a slice is new or has no
// capacity, a map is new or nil, and a pointer is new or nil and what it
// owns is new too. An interface value is what the owner was given, so
// only its footprint must be new.
func (v *fnVerifier) ownedFreshSeen(sink *state, mem memory, ptr value, t types.Type, before *logic.Term, seen map[types.Type]bool) *logic.Term {
	object, isPointer := pointee(t)
	if !isPointer || seen[object] || !v.ownsMemory(object) {
		return logic.True()
	}
	seen[object] = true
	defer delete(seen, object)
	zero := logic.RefLit(0)
	var facts []*logic.Term
	for _, field := range v.inlineOwners(object) {
		facts = append(facts, v.ownedFreshSeen(sink, mem, field.at(ptr), field.ptr, before, seen))
	}
	for _, index := range v.ownedFields(object) {
		val, ft, ok := v.member(sink, mem, ptr, t, index)
		if !ok {
			continue
		}
		switch {
		case isSlice(ft):
			facts = append(facts, logic.Or(logic.Le(val[3], logic.IntLit(0)), logic.Le(before, val[0])))
		case isMap(ft):
			facts = append(facts, logic.Or(logic.Eq(val[0], zero), logic.Le(before, val[0])))
		case isIface(ft):
			// The value itself is what the owner was given, such as the
			// reader of a Scanner, which is not new; its footprint is what
			// the owner owns, and must be new (F2). An owner that keeps a
			// writer it was given says fresh(result, w) instead.
			if v.hasFootprint(ft) {
				facts = append(facts, logic.Or(isNilRef(val), v.rowNewOrIn(mem, home(val[0]), before, nil, nil)))
			}
			// An owner of the project owns the states of what its interface
			// value holds, which are new when its home is (F40 of the review
			// of step 5): G lets in only a new value.
			if len(sourceOwnedFields(object)) > 0 {
				facts = append(facts, logic.Or(isNilRef(val), logic.Le(before, home(val[0]))))
			}
		default:
			facts = append(facts, logic.Or(logic.Eq(val[0], zero), logic.And(logic.Le(before, val[0]), v.ownedFreshSeen(sink, mem, val, ft, before, seen))))
		}
	}
	return logic.And(facts...)
}

// ownerGrowth states that what the owned fields of an owner hold after a
// change lies within what they held before, or was created at or past a
// bound: a slice in the same array and inside its old stretch, or new, or
// without capacity; a map or a pointer the same, new, or nil, with what it
// owns in turn; an interface value the same. That is what every shipped
// declaration claims of its type's methods, and verified code cannot write
// those fields, which are unexported, but through them.
func (v *fnVerifier) ownerGrowth(sink *state, before, after memory, ptr value, t types.Type, bound *logic.Term) *logic.Term {
	return v.ownerGrowthSeen(sink, before, after, ptr, t, bound, map[types.Type]bool{})
}

// ownerGrowthSeen is ownerGrowth with the types entered: for each owner
// held by value it recurses at its offset, and for each owned field it
// states, by the field's kind, that the field holds nothing, what it held,
// within the same stretch for a slice, or memory made at or past the bound;
// for a pointer the same pointer brings the growth of what it owns, and a
// new one that what it owns is new; an owned interface value of a shipped
// owner stays the same, and one of the project may be nil or a new value
// with a new footprint.
func (v *fnVerifier) ownerGrowthSeen(sink *state, before, after memory, ptr value, t types.Type, bound *logic.Term, seen map[types.Type]bool) *logic.Term {
	object, isPointer := pointee(t)
	if !isPointer || seen[object] {
		return logic.True()
	}
	seen[object] = true
	defer delete(seen, object)
	zero := logic.RefLit(0)
	var facts []*logic.Term
	for _, field := range v.inlineOwners(object) {
		facts = append(facts, v.ownerGrowthSeen(sink, before, after, field.at(ptr), field.ptr, bound, seen))
	}
	for _, index := range v.ownedFields(object) {
		old, ft, ok := v.member(sink, before, ptr, t, index)
		now, _, _ := v.member(sink, after, ptr, t, index)
		if !ok {
			continue
		}
		switch {
		case isSlice(ft):
			oldLo, oldHi := v.extent(old, ft)
			nowLo, nowHi := v.extent(now, ft)
			within := logic.And(logic.Eq(now[0], old[0]), logic.Le(oldLo, nowLo), logic.Le(nowHi, oldHi))
			facts = append(facts, logic.Or(logic.Le(now[3], logic.IntLit(0)), logic.Le(bound, now[0]), within))
		case isMap(ft):
			facts = append(facts, logic.Or(logic.Eq(now[0], zero), logic.Eq(now[0], old[0]), logic.Le(bound, now[0])))
		case isIface(ft) && len(sourceOwnedFields(object)) > 0:
			// The same value, nil, or a new one whose footprint is new, as
			// a store into an owned field of the project may leave it.
			facts = append(facts, logic.Or(logic.Eq(now[0], old[0]), isNilRef(now),
				logic.And(logic.Le(bound, home(now[0])), v.rowNewOrIn(after, home(now[0]), bound, nil, nil))))
		case isIface(ft):
			// What a shipped owner keeps does not change (its owns claim).
			facts = append(facts, logic.Eq(now[0], old[0]))
		default:
			same := logic.And(logic.Eq(now[0], old[0]), logic.Eq(now[1], old[1]), v.ownerGrowthSeen(sink, before, after, now, ft, bound, seen))
			facts = append(facts, logic.Or(logic.Eq(now[0], zero), same, logic.And(logic.Le(bound, now[0]), v.ownedFreshSeen(sink, after, now, ft, bound, seen))))
		}
	}
	return logic.And(facts...)
}

// freshOf states fresh(x, ys...): what x refers to, read in mem, was made
// at or past before, cell by cell, or lies in the footprint of one of the
// interface values ys, read in yMem, the memory on entry of the call or of
// the function. Without ys it is fresh(x) as it always was, except for an
// interface value with a footprint, whose footprint must then be new too
// (F2 of the design review): its home is new, and every cell in its row
// was made at or past before. With ys, a pointer is not nil and every cell
// of its struct is new or in a footprint of ys, and so is every cell of
// what it owns; a slice, a map, and an interface value likewise, cell by
// cell, with a slice without capacity and a nil interface value counting
// as new. A footprint can hold an old cell, so a value that writes into
// what the writer it was given writes says fresh(result, w), as
// bufio.NewWriter does.
func (v *fnVerifier) freshOf(sink *state, x reached, mem memory, before *logic.Term, ys []reached, yMem memory) *logic.Term {
	if len(ys) == 0 {
		claim := logic.And(freshSince(before, x), v.ownedFreshSeen(sink, mem, x.val, x.typ, before, map[types.Type]bool{}))
		if isIface(x.typ) && v.hasFootprint(x.typ) {
			claim = logic.And(claim, logic.Or(isNilRef(x.val), v.rowNewOrIn(mem, home(x.val[0]), before, nil, nil)))
		}
		return claim
	}
	yRows := yMem.region(footprintRegion, footprintSort)
	newOrIn := func(alloc, pos *logic.Term) *logic.Term {
		return v.newOrIn(alloc, pos, before, ys, yRows)
	}
	inFootprints := func(alloc, pos *logic.Term) *logic.Term {
		return v.newOrIn(alloc, pos, nil, ys, yRows)
	}
	// Assumed, a stretch's claim is stated where the rows of ys are read
	// at a cell of it, as a row's claim is (rowNewOrIn).
	if v.lazyRows && yRows.Op == logic.OpConst {
		saved := v.lazyStretch
		v.lazyStretch = func(ref, lo, hi *logic.Term) *logic.Term {
			holds := v.fresh("stretchclaim", logic.Bool)
			k := v.bound("k")
			v.claimDefs = append(v.claimDefs, logic.Iff(holds, logic.Forall(k, logic.Implies(logic.And(logic.Le(lo, k), logic.Lt(k, hi)), inFootprints(ref, k)))))
			v.stretchClaims[yRows.Name] = append(v.stretchClaims[yRows.Name], stretchClaim{holds: holds, ref: ref, lo: lo, hi: hi, ys: ys})
			// The claim at the first cell of the stretch, so that an old
			// allocation is refuted where the rows of ys are known to be
			// empty, as those of a converted file are; what rowAt says of
			// that cell is true, and is assumed.
			first, known := v.newOrInParts(ref, lo, nil, ys, yRows)
			if sink != nil {
				for _, fact := range known {
					sink.assume(fact)
				}
			}
			return logic.And(holds, logic.Implies(logic.Lt(lo, hi), first))
		}
		defer func() { v.lazyStretch = saved }()
	}
	switch {
	case isIface(x.typ):
		return logic.Or(isNilRef(x.val), logic.And(logic.Le(before, home(x.val[0])), v.rowNewOrIn(mem, home(x.val[0]), before, ys, yRows)))
	case isMap(x.typ):
		return logic.And(logic.Not(isNilRef(x.val)), newOrIn(x.val[0], logic.IntLit(0)))
	case isSlice(x.typ):
		lo, hi := v.extent(x.val, x.typ)
		return logic.Or(logic.Le(x.val[3], logic.IntLit(0)), v.stretchNewOrIn(x.val[0], lo, hi, before, inFootprints))
	}
	lo, hi := v.extent(x.val, x.typ)
	claims := []*logic.Term{logic.Not(isNilRef(x.val)), v.stretchNewOrIn(x.val[0], lo, hi, before, inFootprints)}
	for _, part := range v.ownedParts(sink, mem, x.val, x.typ, map[types.Type]bool{}) {
		switch {
		case part.fp:
			claims = append(claims, v.rowNewOrIn(mem, part.ref, before, ys, yRows))
		case part.row:
			// The states of an owned interface value are its own, which
			// its contract governs; they are no memory x refers to.
		case part.mapType != nil:
			claims = append(claims, logic.Or(isNilRef(value{part.ref}), newOrIn(part.ref, logic.IntLit(0))))
		default:
			claims = append(claims, v.stretchNewOrIn(part.ref, part.lo, part.hi, before, inFootprints))
		}
	}
	return logic.And(claims...)
}

// newOrIn states that a cell was made at or past before, or lies in the
// footprint of one of the interface values ys in the rows given, with
// what rowAt says of the cell in those rows as its premises. With before
// nil it states only the second.
func (v *fnVerifier) newOrIn(alloc, pos, before *logic.Term, ys []reached, rows *logic.Term) *logic.Term {
	options, facts := v.newOrInParts(alloc, pos, before, ys, rows)
	return logic.Implies(logic.And(facts...), options)
}

// newOrInParts is newOrIn apart: the disjunction, and what rowAt says of
// the cells it reads, which are facts.
func (v *fnVerifier) newOrInParts(alloc, pos, before *logic.Term, ys []reached, rows *logic.Term) (*logic.Term, []*logic.Term) {
	var options, facts []*logic.Term
	if before != nil {
		options = append(options, logic.Le(before, alloc))
	}
	for _, y := range ys {
		cell, known := v.rowAt(rows, home(y.val[0]), alloc, pos)
		facts = append(facts, known...)
		options = append(options, logic.And(logic.Not(isNilRef(y.val)), cell))
	}
	return logic.Or(options...), facts
}

// stretchNewOrIn states newOrIn of every position of an allocation from lo
// up to hi. Whether the allocation is new does not depend on the position,
// so it stands outside the quantifier, which then speaks only of the
// footprints: Z3 can settle the first without the second.
func (v *fnVerifier) stretchNewOrIn(ref, lo, hi, before *logic.Term, inFootprints func(alloc, pos *logic.Term) *logic.Term) *logic.Term {
	if v.lazyStretch != nil {
		return logic.Or(logic.Le(before, ref), v.lazyStretch(ref, lo, hi))
	}
	k := v.bound("k")
	return logic.Or(logic.Le(before, ref), logic.Forall(k, logic.Implies(logic.And(logic.Le(lo, k), logic.Lt(k, hi)), inFootprints(ref, k))))
}

// stretchClaim is what a callee promised of a stretch of an allocation that
// existed: every cell of it lies in the footprint of one of ys, in the
// region the claim is kept for, when holds does.
type stretchClaim struct {
	holds, ref, lo, hi *logic.Term
	ys                 []reached
}

// rowClaim is what a callee promised of the row at a home in one footprint
// region, which holds when holds does: every cell in it was made at or past
// before, or lies in the footprint of one of ys, read in yRows.
type rowClaim struct {
	holds, home, before *logic.Term
	ys                  []reached
	yRows               *logic.Term
}

// rowNewOrIn states that every cell in the row at a home, read in mem, was
// made at or past before or lies in the footprint of one of ys.
func (v *fnVerifier) rowNewOrIn(mem memory, at, before *logic.Term, ys []reached, yRows *logic.Term) *logic.Term {
	rows := mem.region(footprintRegion, footprintSort)
	if v.lazyRows && rows.Op == logic.OpConst {
		// Assumed, as what a callee promises is: a boolean stands for the
		// claim, which rowAt states at each cell of the row it reads.
		v.lazyRows = false
		claim := v.rowNewOrIn(mem, at, before, ys, yRows)
		v.lazyRows = true
		holds := v.fresh("rowclaim", logic.Bool)
		v.claimDefs = append(v.claimDefs, logic.Iff(holds, claim))
		v.rowClaims[rows.Name] = append(v.rowClaims[rows.Name], rowClaim{holds: holds, home: at, before: before, ys: ys, yRows: yRows})
		return holds
	}
	a, k := v.bound("a"), v.bound("k")
	cell, facts := v.rowAt(mem.region(footprintRegion, footprintSort), at, a, k)
	return logic.Forall(a, logic.Forall(k, logic.Implies(logic.And(append(facts, cell)...), v.newOrIn(a, k, before, ys, yRows))))
}

// withinRow states that every cell of what x refers to is in the row at a
// home, read in mem: a map whole, every position of a slice's array up to
// its capacity (a slice without capacity lies within anything), and every
// position of the struct a pointer points to, which is not nil.
func (v *fnVerifier) withinRow(x reached, at *logic.Term, mem memory) *logic.Term {
	rows := mem.region(footprintRegion, footprintSort)
	in := func(alloc, pos *logic.Term) *logic.Term {
		cell, facts := v.rowAt(rows, at, alloc, pos)
		return logic.Implies(logic.And(facts...), cell)
	}
	if isMap(x.typ) {
		return logic.And(logic.Not(isNilRef(x.val)), in(x.val[0], logic.IntLit(0)))
	}
	lo, hi := v.extent(x.val, x.typ)
	k := v.bound("k")
	every := logic.Forall(k, logic.Implies(logic.And(logic.Le(lo, k), logic.Lt(k, hi)), in(x.val[0], k)))
	if isSlice(x.typ) {
		return logic.Or(logic.Le(x.val[3], logic.IntLit(0)), every)
	}
	return logic.And(logic.Not(isNilRef(x.val)), every)
}

// withinOwned states that what x refers to lies within what an owner y
// owns, read where y was read: inside the stretch of an owned slice's
// array, or in the footprint of an owned interface value. It is False for
// a y that owns nothing, and where nothing can be noted (sink is nil, as
// under a quantifier), which errs towards less.
func (v *fnVerifier) withinOwned(sink *state, x, y reached) *logic.Term {
	if sink == nil {
		return logic.False()
	}
	lo, hi := v.extent(x.val, x.typ)
	var options []*logic.Term
	for _, part := range v.ownedParts(sink, y.mem, y.val, y.typ, map[types.Type]bool{}) {
		switch {
		case part.fp:
			options = append(options, v.withinRow(x, part.ref, y.mem))
		case part.row, part.mapType != nil:
		default:
			options = append(options, logic.And(logic.Not(isNilRef(x.val)), logic.Eq(x.val[0], part.ref), logic.Le(part.lo, lo), logic.Le(hi, part.hi)))
		}
	}
	return logic.Or(options...)
}

// structuralFootprint returns what the methods of a value converted to an
// interface with a footprint may write behind their receiver, read in
// memory at the conversion, as a test of a cell with the facts that reading
// other rows needs. For a pointer it is the struct it points to, and a nil
// pointer has none. For a slice held by value it is its array up to its
// capacity, and for a map the map. Any other value held by value has none,
// since a method is handed a copy of it. A value of a type that owns memory
// is not converted in part 1: the bufio types call through what they keep,
// which stratification refuses, bytes.Buffer and strings.Builder grow
// without a bound that can be stated, and types of the project own nothing
// until ownership in source.
func (v *fnVerifier) structuralFootprint(sink *state, mem memory, val value, t types.Type) func(alloc, pos *logic.Term) (*logic.Term, []*logic.Term) {
	switch {
	case isSlice(t):
		lo, hi := v.extent(val, t)
		return func(alloc, pos *logic.Term) (*logic.Term, []*logic.Term) {
			return logic.And(logic.Lt(logic.IntLit(0), val[3]), logic.Eq(alloc, val[0]), logic.Le(lo, pos), logic.Lt(pos, hi)), nil
		}
	case isMap(t):
		return func(alloc, pos *logic.Term) (*logic.Term, []*logic.Term) {
			return logic.And(logic.Not(isNilRef(val)), logic.Eq(alloc, val[0]), logic.Eq(pos, logic.IntLit(0))), nil
		}
	}
	if _, isPointer := pointee(t); !isPointer {
		return nil
	}
	lo, hi := v.extent(val, t)
	if v.ownsMemory(t) {
		// An owner's footprint is its struct and what it owns, as it is
		// then (step 4 of ownership in source).
		return func(alloc, pos *logic.Term) (*logic.Term, []*logic.Term) {
			owned, facts := v.ownerFootprintAt(sink, mem, val, t, alloc, pos, map[types.Type]bool{})
			inStruct := logic.And(logic.Eq(alloc, val[0]), logic.Le(lo, pos), logic.Lt(pos, hi))
			return logic.And(logic.Not(isNilRef(val)), logic.Or(inStruct, owned)), facts
		}
	}
	return func(alloc, pos *logic.Term) (*logic.Term, []*logic.Term) {
		return logic.And(logic.Not(isNilRef(val)), logic.Eq(alloc, val[0]), logic.Le(lo, pos), logic.Lt(pos, hi)), nil
	}
}

// ownsMemory reports whether a value of the type, or what a pointer of it
// points to, owns memory by the shipped declarations.
func (pv *pkgVerifier) ownsMemory(t types.Type) bool {
	if object, isPointer := pointee(t); isPointer {
		t = object
	}
	if len(pv.ownedFields(t)) > 0 {
		return true
	}
	return len(pv.inlineOwners(t)) > 0
}

// inlineField is a field of a struct held by value whose type owns memory,
// or holds such a field in turn: its offset, and the type of a pointer to
// it, through which what it owns is read.
type inlineField struct {
	off int64
	ptr types.Type
}

// at returns a pointer to the field, for a pointer to the struct.
func (f inlineField) at(ptr value) value {
	return value{ptr[0], logic.Add(ptr[1], logic.IntLit(f.off))}
}

// inlineOwners returns the fields of a struct type held by value, not
// behind a pointer, a slice, or a map, whose type owns memory or holds such
// a field: a strings.Builder or a bytes.Buffer in a struct of the project,
// or a named type over one. What such a field owns, the struct owns (D7 of
// the design review): a write of it through the struct writes memory that
// the struct reaches, and only the methods of the field may write it.
func (pv *pkgVerifier) inlineOwners(t types.Type) []inlineField {
	u, isStruct := t.Underlying().(*types.Struct)
	if !isStruct {
		return nil
	}
	fields := slices.Collect(u.Fields())
	offsets := pv.pass.TypesSizes.Offsetsof(fields)
	var found []inlineField
	for i, field := range fields {
		if _, inner := field.Type().Underlying().(*types.Struct); inner && pv.ownsMemory(field.Type()) {
			found = append(found, inlineField{off: offsets[i], ptr: types.NewPointer(field.Type())})
		}
	}
	return found
}

// notWrittenRoot returns the parameter p of a Modifies entry p.f, where f is
// a field of the struct p points to that a notWrittenBy declaration covers,
// as resp.Body of an *http.Response, or nil.
func (v *fnVerifier) notWrittenRoot(fn *funcInfo, m *modTarget) *types.Var {
	if m.behind || len(m.steps) != 1 || m.steps[0].field == "" {
		return nil
	}
	param := fn.paramNames[m.name]
	if param == nil {
		return nil
	}
	object, isPointer := pointee(param.Type())
	if !isPointer {
		return nil
	}
	u, isStruct := object.Underlying().(*types.Struct)
	if !isStruct {
		return nil
	}
	for i := range u.NumFields() {
		if u.Field(i).Name() == m.steps[0].field && notWrittenOf(object, i) != nil {
			return param
		}
	}
	return nil
}
