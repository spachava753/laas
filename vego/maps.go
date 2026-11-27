package vego

import (
	"fmt"
	"math/big"
	"go/ast"
	"go/token"
	"go/types"

	"github.com/spachava753/laas/vego/internal/logic"
)

// A map is a reference, like a pointer: nil, or one of the maps that exist.
// What a map holds lives in memory, in regions of their own for each map
// type: whether each key is present, the value of each key, leaf by leaf,
// and the number of keys. A key is a number; a string key is turned into
// one that identifies the string by its contents. A key that is absent has
// the zero value, as reading it in Go gives.

func isMap(t types.Type) bool {
	if t == nil {
		return false
	}
	_, ok := t.Underlying().(*types.Map)
	return ok
}

// mapParts returns the key and value types of a map type.
func mapParts(t types.Type) (key, elem types.Type) {
	m := t.Underlying().(*types.Map)
	return m.Key(), m.Elem()
}

// mapKeyed reports whether the keys of a map type are modelled: integers,
// strings, or booleans. A map with such keys is a value the verifier can
// hold, whatever its values are.
func mapKeyed(t types.Type) bool {
	key, _ := mapParts(t)
	basic, ok := key.Underlying().(*types.Basic)
	return ok && basic.Info()&(types.IsInteger|types.IsString|types.IsBoolean) != 0 && basic.Kind() != types.Uintptr
}

// keyPlaceholder returns a term of the sort that keys of a map type have
// in the logic: a sequence for strings, a boolean for booleans, and a
// number otherwise.
func keyPlaceholder(t types.Type) *logic.Term {
	key, _ := mapParts(t)
	switch {
	case isString(key):
		return logic.Fill(logic.IntLit(0), logic.IntLit(0))
	case isBool(key):
		return logic.False()
	}
	return logic.IntLit(0)
}

// mapModelled reports whether the contents of maps of the type are
// modelled, which also takes values of a modelled type. It is asked where a
// map is used, not where its type is laid out, since a map type may have
// itself as its value type.
func mapModelled(t types.Type) bool {
	_, elem := mapParts(t)
	_, ok := elemLayout(elem)
	return ok && mapKeyed(t)
}

// The leaves of the regions that say which keys a map has and how many.
var (
	hasLeaf   = leaf{path: "#has", sort: logic.Bool}
	countLeaf = leaf{path: "#len", sort: logic.Int}
)

// mapOwner names the regions of a map type. A named map type shares them
// with the map type it is made of, since a map converts between the two and
// stays the same map.
func mapOwner(t types.Type) string { return "map " + typeKey(t.Underlying()) }

// mapKey turns a key into the number a map is indexed by.
func mapKey(key *logic.Term) *logic.Term {
	switch {
	case key.Sort.IsSeq():
		return logic.Key(key)
	case key.Sort == logic.Bool:
		// false is 0 and true 1, as no two booleans share a number.
		return logic.Ite(key, logic.IntLit(1), logic.IntLit(0))
	}
	return key
}

// mapHas reads whether a map has a key.
func (v *fnVerifier) mapHas(sink *state, mem memory, t types.Type, ref, key *logic.Term) *logic.Term {
	return logic.Select(v.row(sink, mem, mapOwner(t)+hasLeaf.path, hasLeaf.sort, ref), mapKey(key))
}

// mapLen reads the number of keys of a map.
func (v *fnVerifier) mapLen(sink *state, mem memory, t types.Type, ref *logic.Term) *logic.Term {
	count := v.cell(sink, mem, mapOwner(t)+countLeaf.path, countLeaf, ref)
	v.noteMap(sink, mem, t, ref, nil)
	return count
}

// mapValue reads the value a map has for a key, which is the zero value if
// the key is absent.
func (v *fnVerifier) mapValue(sink *state, mem memory, t types.Type, ref, key *logic.Term) value {
	_, elem := mapParts(t)
	leaves, _ := layoutOf(elem)
	val := make(value, len(leaves))
	for i, lf := range leaves {
		val[i] = logic.Select(v.row(sink, mem, mapOwner(t)+"#val"+lf.path, lf.sort, ref), mapKey(key))
	}
	v.noteMap(sink, mem, t, ref, key)
	cells := make([]entryCell, len(leaves))
	for i, lf := range leaves {
		cells[i] = entryCell{key: mapOwner(t) + "#val" + lf.path, sort: lf.sort, pos: mapKey(key)}
	}
	v.noteEntryRefs(mem, cells, ref, elem)
	switch {
	case !hasBound(key) && (sink == nil || !sink.collecting):
		v.noteTyped(sink, val, elem)
		v.noteReachedValue(sink, t, ref, key)
	case holdsMemory(elem):
		// Under a quantifier over the keys, what a value that refers to
		// memory is, and what the other parameters reach from it, go to
		// what gathers the quantifier's facts, as for an element.
		notes := v.boundSink
		if sink != nil && sink.collecting {
			notes = sink
		}
		v.noteMap(notes, mem, t, ref, key)
		v.noteTyped(notes, val, elem)
		v.noteReachedValue(notes, t, ref, key)
	}
	return val
}

// noteMap records what holds of every map, for the map and key that are
// read: the number of keys is not negative, a key that is present makes it
// positive, a key that is absent has the zero value, and the nil map has no
// keys. Like the typing of what is read from memory, this is true of every
// map whether or not the read was a sensible one.
//
// The number of keys is also bounded by memory. len gives it as an int, and
// the runtime keeps the key and the value of every entry in memory of their
// own in the heap, whose addresses lie in a range of 2^heapAddrBits bytes,
// which maxAlloc is (one less on 32-bit targets, where the map's header
// takes a byte too). That is an assumption about the runtime, stated in the
// guide's "What a proof assumes".
func (v *fnVerifier) noteMap(sink *state, mem memory, t types.Type, ref, key *logic.Term) {
	if sink == nil || !sink.collecting && (hasBound(ref) || (key != nil && hasBound(key))) {
		return
	}
	count := v.cell(nil, mem, mapOwner(t)+countLeaf.path, countLeaf, ref)
	isNil := logic.Eq(ref, logic.RefLit(0))
	keyType, elemType := mapParts(t)
	entry := v.pass.TypesSizes.Sizeof(keyType) + v.pass.TypesSizes.Sizeof(elemType)
	_, most, _ := v.intRange(types.Typ[types.Int])
	// A map has no more keys than its key type has values.
	if lo, hi, ok := v.intRange(keyType); ok {
		if values := new(big.Int).Add(new(big.Int).Sub(hi, lo), big.NewInt(1)); values.Cmp(most) < 0 {
			most = values
		}
	}
	if isBool(keyType) {
		most = big.NewInt(2)
	}
	// The bound by MaxInt and the bound by memory are marked: they rest on
	// memory alone, and a Variant may not use them (checkVariant). The
	// bound by the key type does not.
	countLimit := logic.BigLit(most)
	if _, maxInt, _ := v.intRange(types.Typ[types.Int]); most.Cmp(maxInt) == 0 {
		countLimit = v.marks().mapCount
	}
	facts := []*logic.Term{logic.Le(logic.IntLit(0), count), logic.Implies(isNil, logic.Eq(count, logic.IntLit(0))),
		logic.Le(count, countLimit), logic.Le(logic.Mul(count, logic.IntLit(max(entry, 1))), v.marks().mapBytes)}
	if key != nil {
		present := logic.Select(v.row(nil, mem, mapOwner(t)+hasLeaf.path, hasLeaf.sort, ref), mapKey(key))
		facts = append(facts, logic.Implies(present, logic.Le(logic.IntLit(1), count)), logic.Implies(isNil, logic.Not(present)))
		_, elem := mapParts(t)
		leaves, _ := layoutOf(elem)
		for _, lf := range leaves {
			held := logic.Select(v.row(nil, mem, mapOwner(t)+"#val"+lf.path, lf.sort, ref), mapKey(key))
			facts = append(facts, logic.Implies(logic.Not(present), isZero(held, lf)))
		}
	}
	fact := logic.And(facts...)
	if note := "map " + fact.String(); !sink.noted[note] {
		sink.noted[note] = true
		sink.assume(fact)
	}
}

// isZero states that a leaf holds its zero value.
func isZero(held *logic.Term, lf leaf) *logic.Term {
	switch {
	case lf.sort.IsSeq():
		return logic.Eq(logic.Len(held), logic.IntLit(0))
	case lf.sort == logic.Bool:
		return logic.Not(held)
	case lf.sort == logic.Err:
		return logic.IsNil(held)
	}
	return logic.Eq(held, zeroLeaf(lf))
}

// newMap creates an empty map and returns it.
func (v *fnVerifier) newMap(st *state, t types.Type) value {
	ref := v.alloc(st, true)
	_, elem := mapParts(t)
	leaves, _ := layoutOf(elem)
	st.storeCell(mapOwner(t)+countLeaf.path, countLeaf, ref, logic.IntLit(0))
	st.storeRow(mapOwner(t)+hasLeaf.path, hasLeaf.sort, ref, logic.Fill(logic.IntLit(0), logic.False()))
	for _, lf := range leaves {
		st.storeRow(mapOwner(t)+"#val"+lf.path, lf.sort, ref, logic.Fill(logic.IntLit(0), zeroLeaf(lf)))
	}
	v.noteBorn(st, ref, mapRegions(t))
	return value{ref}
}

// mapRegions returns the regions that hold the maps of a type, with the
// sort of each.
func mapRegions(t types.Type) map[string]logic.Sort {
	_, elem := mapParts(t)
	leaves, _ := layoutOf(elem)
	keys := map[string]logic.Sort{
		mapOwner(t) + countLeaf.path: logic.SeqOf(countLeaf.sort),
		mapOwner(t) + hasLeaf.path:   logic.SeqOf(logic.SeqOf(hasLeaf.sort)),
	}
	for _, lf := range leaves {
		keys[mapOwner(t)+"#val"+lf.path] = logic.SeqOf(logic.SeqOf(lf.sort))
	}
	return keys
}

// mapStore sets the value of a key, or with present false removes the key.
// The map must be one the function may modify. Setting a key needs a map
// that is not nil. Removing one from the nil map does nothing, in Go and
// here: the nil map has no keys, every key it lacks has the zero value, and
// that is all the removal writes.
//
// What it reads of the map is part of the write, which comes after the
// operands of the statement, so it is not recorded as a read.
func (v *fnVerifier) mapStore(st *state, t types.Type, ref, key *logic.Term, val value, present bool, pos token.Pos, what string) {
	v.quietly(func() { v.storeKey(st, t, ref, key, val, present, pos, what) })
}

// storeKey does the work of mapStore.
func (v *fnVerifier) storeKey(st *state, t types.Type, ref, key *logic.Term, val value, present bool, pos token.Pos, what string) {
	if present {
		v.check(st, nil, logic.Lt(logic.IntLit(0), ref), pos, "map may be nil")
	}
	// An entry of a map of references is covered only by the whole map,
	// since a path to it names what the value refers to.
	unlisted := ""
	_, elem := mapParts(t)
	if _, isPointer := pointee(elem); isPointer || isSlice(elem) || isMap(elem) || isIface(elem) {
		unlisted = "list the whole map in a // @Modifies clause: an entry of a map whose values are pointers, slices, maps, or interface values " +
			"is covered only by the map, since a path such as m[k] in a Modifies clause names what the value refers to"
	}
	v.checkWriteOr(st, nil, target{mapType: t, ref: ref, key: mapKey(key)}.reach(), pos, what, "", unlisted)
	v.checkRangedStore(st, t, ref, key, present, pos)
	// What holds of every map is put on record for this key before the
	// write, so that the write to the nil map is known to change nothing.
	v.noteMap(st, st.mem, t, ref, key)
	had := v.mapHas(st, st.mem, t, ref, key)
	// The count is named, so that the new count does not hold the region
	// of counts a second time.
	count := v.named(st, "count", v.mapLen(st, st.mem, t, ref))
	leaves, _ := layoutOf(elem)
	one, none := logic.IntLit(1), logic.IntLit(0)
	change := logic.Ite(had, none, one)
	if !present {
		change = logic.Ite(had, logic.IntLit(-1), none)
	}
	st.storeCell(mapOwner(t)+countLeaf.path, countLeaf, ref, logic.Add(count, change))
	v.writeAt(st, mapOwner(t)+hasLeaf.path, hasLeaf.sort, ref, mapKey(key), logic.BoolLit(present))
	for i, lf := range leaves {
		v.writeAt(st, mapOwner(t)+"#val"+lf.path, lf.sort, ref, mapKey(key), val[i])
	}
}

// havocEntry forgets one entry of a map: a call that may write it has run.
// Every other key is as it was, and the number of keys follows from
// whether the key was there and is: the call can change no other key. The
// new value of a key that is absent is the zero value, and the nil map
// gets no key, as for every map. Where skipped holds, the call did not
// run, and the entry is as it was.
func (v *fnVerifier) havocEntry(st *state, t target, skipped *logic.Term, guarded bool) {
	owner := mapOwner(t.mapType)
	_, elem := mapParts(t.mapType)
	leaves, _ := layoutOf(elem)
	key := v.named(st, "key", t.key)
	had := v.named(st, "had", logic.Select(v.row(nil, st.mem, owner+hasLeaf.path, hasLeaf.sort, t.ref), key))
	count := v.named(st, "count", v.cell(nil, st.mem, owner+countLeaf.path, countLeaf, t.ref))
	has := v.fresh("written", logic.Bool)
	held := make(value, len(leaves))
	for i, lf := range leaves {
		held[i] = v.fresh("written", lf.sort)
		st.assume(logic.Implies(logic.Not(has), isZero(held[i], lf)))
		if guarded {
			before := logic.Select(v.row(nil, st.mem, owner+"#val"+lf.path, lf.sort, t.ref), key)
			st.assume(logic.Implies(skipped, v.same(held[i], before)))
		}
	}
	st.assume(logic.Implies(logic.Eq(t.ref, logic.RefLit(0)), logic.Not(has)))
	if guarded {
		st.assume(logic.Implies(skipped, logic.Iff(has, had)))
	}
	one, none := logic.IntLit(1), logic.IntLit(0)
	st.storeCell(owner+countLeaf.path, countLeaf, t.ref, logic.Sub(logic.Add(count, logic.Ite(has, one, none)), logic.Ite(had, one, none)))
	v.writeAt(st, owner+hasLeaf.path, hasLeaf.sort, t.ref, key, has)
	for i, lf := range leaves {
		v.writeAt(st, owner+"#val"+lf.path, lf.sort, t.ref, key, held[i])
	}
}

// deleteKey executes delete(m, k), which does nothing when the key is absent
// or the map is nil.
func (v *fnVerifier) deleteKey(call *ast.CallExpr, st *state) {
	t := v.info.TypeOf(call.Args[0])
	if !isMap(t) || !mapModelled(t) {
		v.unsupported(call.Pos(), mapClass(t), fmt.Sprintf("delete on a %s is not supported", t))
	}
	var ref, key *logic.Term
	v.evaluate(st, func() {
		ref, key = v.expr(call.Args[0], st, nil), v.expr(call.Args[1], st, nil)
	})
	_, elem := mapParts(t)
	v.mapStore(st, t, ref, key, zeroValue(elem), false, call.Pos(), types.ExprString(call.Args[0])+" is modified")
}

// mapLiteral evaluates map[K]V{k: v, ...}: a new map that gets the entries
// one after the other. Go does not fix the order in which the entries are
// put into the map, so when two keys are equal it is not known which value
// the map keeps. Two constant keys cannot be equal, since Go rejects the
// literal; any other two must be proved to differ.
func (v *fnVerifier) mapLiteral(e *ast.CompositeLit, t types.Type, st *state, guard []*logic.Term) value {
	if !mapModelled(t) {
		v.unsupported(e.Pos(), mapClass(t), fmt.Sprintf("maps of type %s are not supported", t))
	}
	m := v.newMap(st, t)
	keyType, elem := mapParts(t)
	var keys []*logic.Term
	for _, element := range e.Elts {
		pair := element.(*ast.KeyValueExpr)
		key := v.settled(st, guard, v.evalAs(pair.Key, keyType, st, guard), keyType)[0]
		for j, earlier := range keys {
			other := e.Elts[j].(*ast.KeyValueExpr).Key
			if v.info.Types[pair.Key].Value != nil && v.info.Types[other].Value != nil {
				continue
			}
			v.check(st, guard, logic.Not(v.same(earlier, key)), pair.Key.Pos(),
				"the keys %s and %s of this map literal may be equal, and Go does not fix which of their entries the map keeps; "+
					"build the map with assignments instead", types.ExprString(other), types.ExprString(pair.Key))
		}
		keys = append(keys, key)
		held := v.settled(st, guard, v.evalAs(pair.Value, elem, st, guard), elem)
		v.mapStore(st, t, m[0], key, held, true, pair.Pos(), "a new map is filled")
	}
	v.noteBorn(st, m[0], mapRegions(t))
	return m
}
