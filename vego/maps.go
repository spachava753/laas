package vego

import (
	"fmt"
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

// mapKeyed reports whether the keys of a map type are modelled: integers or
// strings. A map with such keys is a value the verifier can hold, whatever
// its values are.
func mapKeyed(t types.Type) bool {
	key, _ := mapParts(t)
	basic, ok := key.Underlying().(*types.Basic)
	return ok && basic.Info()&(types.IsInteger|types.IsString) != 0 && basic.Kind() != types.Uintptr
}

// mapModelled reports whether the contents of maps of the type are
// modelled, which also takes values of a modelled type. It is asked where a
// map is used, not where its type is laid out, since a map type may have
// itself as its value type.
func mapModelled(t types.Type) bool {
	_, elem := mapParts(t)
	_, ok := layoutOf(elem)
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
	if key.Sort.IsSeq() {
		return logic.Key(key)
	}
	return key
}

// mapHas reads whether a map has a key.
func (v *fnVerifier) mapHas(sink *state, mem memory, t types.Type, ref, key *logic.Term) *logic.Term {
	return logic.Select(v.row(sink, mem, mapOwner(t)+hasLeaf.path, hasLeaf, ref), mapKey(key))
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
		val[i] = logic.Select(v.row(sink, mem, mapOwner(t)+"#val"+lf.path, lf, ref), mapKey(key))
	}
	v.noteMap(sink, mem, t, ref, key)
	if !hasBound(key) {
		v.noteTyped(sink, val, elem)
	}
	return val
}

// noteMap records what holds of every map, for the map and key that are
// read: the number of keys is not negative, a key that is present makes it
// positive, a key that is absent has the zero value, and the nil map has no
// keys. Like the typing of what is read from memory, this is true of every
// map whether or not the read was a sensible one.
func (v *fnVerifier) noteMap(sink *state, mem memory, t types.Type, ref, key *logic.Term) {
	if sink == nil || hasBound(ref) || (key != nil && hasBound(key)) {
		return
	}
	count := v.cell(nil, mem, mapOwner(t)+countLeaf.path, countLeaf, ref)
	isNil := logic.Eq(ref, logic.RefLit(0))
	facts := []*logic.Term{logic.Le(logic.IntLit(0), count), logic.Implies(isNil, logic.Eq(count, logic.IntLit(0)))}
	if key != nil {
		present := logic.Select(v.row(nil, mem, mapOwner(t)+hasLeaf.path, hasLeaf, ref), mapKey(key))
		facts = append(facts, logic.Implies(present, logic.Le(logic.IntLit(1), count)), logic.Implies(isNil, logic.Not(present)))
		_, elem := mapParts(t)
		leaves, _ := layoutOf(elem)
		for _, lf := range leaves {
			held := logic.Select(v.row(nil, mem, mapOwner(t)+"#val"+lf.path, lf, ref), mapKey(key))
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
	st.storeRow(mapOwner(t)+hasLeaf.path, hasLeaf, ref, logic.Fill(logic.IntLit(0), logic.False()))
	for _, lf := range leaves {
		st.storeRow(mapOwner(t)+"#val"+lf.path, lf, ref, logic.Fill(logic.IntLit(0), zeroLeaf(lf)))
	}
	return value{ref}
}

// mapStore sets the value of a key, or with present false removes the key.
// The map must not be nil and must be one the function may modify.
func (v *fnVerifier) mapStore(st *state, t types.Type, ref, key *logic.Term, val value, present bool, pos token.Pos, what string) {
	v.check(st, nil, logic.Lt(logic.IntLit(0), ref), pos, "map may be nil")
	v.checkWrite(st, nil, mapOwner(t), ref, nil, nil, pos, what)
	had := v.mapHas(st, st.mem, t, ref, key)
	count := v.mapLen(st, st.mem, t, ref)
	_, elem := mapParts(t)
	leaves, _ := layoutOf(elem)
	one, none := logic.IntLit(1), logic.IntLit(0)
	change := logic.Ite(had, none, one)
	if !present {
		change = logic.Ite(had, logic.IntLit(-1), none)
	}
	st.storeCell(mapOwner(t)+countLeaf.path, countLeaf, ref, logic.Add(count, change))
	rows := func(lf leaf) *logic.Term {
		return logic.Select(st.mem.region(mapOwner(t)+lf.path, logic.SeqOf(logic.SeqOf(lf.sort))), ref)
	}
	st.storeRow(mapOwner(t)+hasLeaf.path, hasLeaf, ref, logic.Store(rows(hasLeaf), mapKey(key), logic.BoolLit(present)))
	for i, lf := range leaves {
		inMap := lf
		inMap.path = "#val" + lf.path
		st.storeRow(mapOwner(t)+inMap.path, lf, ref, logic.Store(rows(inMap), mapKey(key), val[i]))
	}
}

// deleteKey executes delete(m, k). Go lets a nil map through as a no-op;
// here the map must be known not to be nil.
func (v *fnVerifier) deleteKey(call *ast.CallExpr, st *state) {
	t := v.info.TypeOf(call.Args[0])
	if !isMap(t) || !mapModelled(t) {
		v.unsupported(call.Pos(), fmt.Sprintf("delete on a %s is not supported", t))
	}
	ref, key := v.expr(call.Args[0], st, nil), v.expr(call.Args[1], st, nil)
	_, elem := mapParts(t)
	v.mapStore(st, t, ref, key, zeroValue(elem), false, call.Pos(), types.ExprString(call.Args[0])+" is modified")
}

// mapLiteral evaluates map[K]V{k: v, ...}: a new map that gets the entries
// one after the other.
func (v *fnVerifier) mapLiteral(e *ast.CompositeLit, t types.Type, st *state, guard []*logic.Term) value {
	if !mapModelled(t) {
		v.unsupported(e.Pos(), fmt.Sprintf("maps of type %s are not supported", t))
	}
	m := v.newMap(st, t)
	keyType, elem := mapParts(t)
	for _, element := range e.Elts {
		pair := element.(*ast.KeyValueExpr)
		key := v.settled(st, guard, v.evalAs(pair.Key, keyType, st, guard), keyType)[0]
		held := v.settled(st, guard, v.evalAs(pair.Value, elem, st, guard), elem)
		v.mapStore(st, t, m[0], key, held, true, pair.Pos(), "a new map is filled")
	}
	return m
}
