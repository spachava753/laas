package vego

import (
	"fmt"
	"go/token"
	"go/types"
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
			// What existed on entry held only what existed on entry; a home
			// made since has a footprint this row does not describe.
			facts = append(facts, logic.Implies(logic.And(logic.Lt(home, v.entryBrk), cellOf(at)), logic.And(logic.Lt(logic.IntLit(0), alloc), logic.Lt(alloc, v.entryBrk))))
		case v.layers[at.Name] != nil:
			known := v.layers[at.Name]
			if !known.growth {
				panic("vego: internal error: the footprint region has a layer that is not a growth layer")
			}
			// A home made since the bound described no value before it,
			// so only the rows of homes that existed keep their cells.
			kept := logic.And(logic.Lt(alloc, known.bound), logic.Lt(home, known.bound))
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
		owner := declaringInterface(method)
		if owner != nil && !pv.hasStates(owner.Type()) && writesBehind(pv.methodContract(method)) {
			return true
		}
	}
	return false
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
	param  *types.Var
	rel    *logic.Term
	home   *logic.Term
	direct []passedValue
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
		return inRange(val[0], val[1], logic.Add(val[1], logic.IntLit(v.span(object))))
	}
	switch u := t.Underlying().(type) {
	case *types.Slice:
		return inRange(val[0], val[1], logic.Add(val[1], logic.Mul(val[3], logic.IntLit(v.span(u.Elem())))))
	case *types.Map:
		return logic.And(logic.Ne(val[0], zero), logic.Eq(ref, val[0]), logic.Eq(position, logic.IntLit(0)))
	case *types.Struct:
		var cases []*logic.Term
		for i := range u.NumFields() {
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
	v.reaches = nil
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
				r.direct = append(r.direct, passedValue{val: v.entry[other], t: other.Type()})
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
		fact := logic.Implies(r.reachedAt(v, ref, holder), v.reachedBy(r.rel, entry, t))
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
// of layers short in a function that never meets a footprint.
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
	return !v.targetsHoldReferences(fn)
}

// ownsDecl is what a shipped file declares a struct type of another module
// to own: the fields whose memory is part of the footprint of a value of
// the type, with why that is true of every method of the type.
type ownsDecl struct {
	// pkg and typ name the type.
	pkg, typ string
	fields   []string
	reason string
	line   int
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
			default:
				f.problem(field.Line, "unknown field %q in owns of %s; expected fields and reason", field.Value, typeName.Value)
			}
		}
		if len(decl.fields) == 0 || decl.reason == "" {
			f.problem(typeName.Line, "owns of %s needs the fields it owns and a reason", typeName.Value)
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
	named, ok := types.Unalias(t).(*types.Named)
	if !ok || named.Obj().Pkg() == nil {
		return nil
	}
	u, isStruct := named.Underlying().(*types.Struct)
	if !isStruct {
		return nil
	}
	var decl ownsDecl
	found := false
	for _, file := range shippedContracts() {
		if d, has := file.owns[stateKey(named.Obj().Pkg().Path(), named.Obj().Name())]; has {
			decl, found = d, true
		}
	}
	if !found {
		return nil
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
			panic(fmt.Sprintf("vego: internal error: the shipped declaration that %s owns %s names no field of it", named, name))
		}
		// A field can be owned when it holds a pointer to a struct, a
		// slice, a map, or an interface value.
		ft := u.Field(index).Type()
		if _, isPointer := pointee(ft); !isPointer && !isSlice(ft) && !isMap(ft) && !isIface(ft) {
			panic(fmt.Sprintf("vego: internal error: the shipped declaration that %s owns %s names no field that can be owned", named, name))
		}
		indices = append(indices, index)
	}
	return indices
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
	if len(fields) == 0 {
		return nil
	}
	seen[object] = true
	defer delete(seen, object)
	var parts []target
	for _, index := range fields {
		val, ft, ok := v.member(sink, mem, ptr, t, index)
		if !ok {
			continue
		}
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
			if v.hasStates(ft) {
				parts = append(parts, target{row: true, cells: []cell{stateCell}, ref: home(val[0])})
			}
		default:
			inner, _ := pointee(ft)
			size := v.pass.TypesSizes.Sizeof(inner)
			parts = append(parts, target{cells: v.cellsOf(inner), ref: val[0], lo: val[1], hi: logic.Add(val[1], logic.IntLit(size)), single: true})
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
			if v.hasStates(ft) {
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
	if !isPointer || seen[object] || len(v.ownedFields(object)) == 0 {
		return logic.True()
	}
	seen[object] = true
	defer delete(seen, object)
	zero := logic.RefLit(0)
	var facts []*logic.Term
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

func (v *fnVerifier) ownerGrowthSeen(sink *state, before, after memory, ptr value, t types.Type, bound *logic.Term, seen map[types.Type]bool) *logic.Term {
	object, isPointer := pointee(t)
	if !isPointer || seen[object] {
		return logic.True()
	}
	seen[object] = true
	defer delete(seen, object)
	zero := logic.RefLit(0)
	var facts []*logic.Term
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
		case isIface(ft):
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
	switch {
	case isIface(x.typ):
		return logic.Or(isNilRef(x.val), logic.And(logic.Le(before, home(x.val[0])), v.rowNewOrIn(mem, home(x.val[0]), before, ys, yRows)))
	case isMap(x.typ):
		return logic.And(logic.Not(isNilRef(x.val)), newOrIn(x.val[0], logic.IntLit(0)))
	case isSlice(x.typ):
		lo, hi := v.extent(x.val, x.typ)
		return logic.Or(logic.Le(x.val[3], logic.IntLit(0)), v.stretchNewOrIn(x.val[0], lo, hi, newOrIn))
	}
	lo, hi := v.extent(x.val, x.typ)
	claims := []*logic.Term{logic.Not(isNilRef(x.val)), v.stretchNewOrIn(x.val[0], lo, hi, newOrIn)}
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
			claims = append(claims, v.stretchNewOrIn(part.ref, part.lo, part.hi, newOrIn))
		}
	}
	return logic.And(claims...)
}

// newOrIn states that a cell was made at or past before, or lies in the
// footprint of one of the interface values ys in the rows given, with
// what rowAt says of the cell in those rows as its premises.
func (v *fnVerifier) newOrIn(alloc, pos, before *logic.Term, ys []reached, rows *logic.Term) *logic.Term {
	options := []*logic.Term{logic.Le(before, alloc)}
	var facts []*logic.Term
	for _, y := range ys {
		cell, known := v.rowAt(rows, home(y.val[0]), alloc, pos)
		facts = append(facts, known...)
		options = append(options, logic.And(logic.Not(isNilRef(y.val)), cell))
	}
	return logic.Implies(logic.And(facts...), logic.Or(options...))
}

// stretchNewOrIn states newOrIn of every position of an allocation from lo
// up to hi.
func (v *fnVerifier) stretchNewOrIn(ref, lo, hi *logic.Term, newOrIn func(alloc, pos *logic.Term) *logic.Term) *logic.Term {
	k := v.bound("k")
	return logic.Forall(k, logic.Implies(logic.And(logic.Le(lo, k), logic.Lt(k, hi)), newOrIn(ref, k)))
}

// rowNewOrIn states that every cell in the row at a home, read in mem, was
// made at or past before or lies in the footprint of one of ys.
func (v *fnVerifier) rowNewOrIn(mem memory, at, before *logic.Term, ys []reached, yRows *logic.Term) *logic.Term {
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
