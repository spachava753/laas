package vego

import (
	"fmt"
	"go/types"
	"strings"

	"github.com/spachava753/laas/vego/internal/logic"
)

// The parts a leaf can be: an ordinary value, or one of the four numbers that
// make up a slice.
const (
	partValue = iota
	partRef   // which backing array the slice refers to; zero for a nil slice
	partOff   // where in that array the slice starts
	partLen
	partCap
)

// leaf is one indivisible component of a Go value. A number, a boolean, a
// string, an error, and a pointer are a single leaf; a slice is four; a
// struct is the leaves of its fields, one after the other.
type leaf struct {
	path string // how the leaf is reached from the value: ".pos.x", ".items#len"
	sort logic.Sort
	typ  types.Type // the type of the value or of the slice the leaf is part of
	part int
}

// value is a Go value in the logic: one term for each leaf of its type.
type value []*logic.Term

// typeKey names a type in the keys of memory regions. Identical types must
// get the same key however they are spelled, so aliases are replaced by what
// they stand for, at every depth.
func typeKey(t types.Type) string {
	switch t := types.Unalias(t).(type) {
	case *types.Basic:
		// byte is uint8 and rune is int32 under another name.
		return types.Typ[t.Kind()].Name()
	case *types.Pointer:
		return "*" + typeKey(t.Elem())
	case *types.Slice:
		return "[]" + typeKey(t.Elem())
	case *types.Struct:
		key := "struct{"
		for i := range t.NumFields() {
			field := t.Field(i)
			// Unexported names of different packages are different fields.
			name := field.Name()
			if !field.Exported() && field.Pkg() != nil {
				name = field.Pkg().Path() + "." + name
			}
			key += fmt.Sprintf("%s %s %t %q;", name, typeKey(field.Type()), field.Embedded(), t.Tag(i))
		}
		return key + "}"
	case *types.Named:
		// A named type is its own type, whatever it is made of; an
		// instantiated one is told apart by its arguments.
		key := types.TypeString(t.Origin(), nil)
		for i := range t.TypeArgs().Len() {
			key += "[" + typeKey(t.TypeArgs().At(i)) + "]"
		}
		return key
	}
	return types.TypeString(types.Unalias(t), nil)
}

func isError(t types.Type) bool {
	return types.Identical(t, types.Universe.Lookup("error").Type())
}

// pointee returns the struct type a pointer refers to. Pointers to anything
// else are not modelled.
func pointee(t types.Type) (types.Type, bool) {
	pointer, ok := t.Underlying().(*types.Pointer)
	if !ok {
		return nil, false
	}
	_, ok = pointer.Elem().Underlying().(*types.Struct)
	return pointer.Elem(), ok
}

// elemType returns the element type of a slice type.
func elemType(t types.Type) types.Type {
	return t.Underlying().(*types.Slice).Elem()
}

// layoutOf lists the leaves of a type, and reports whether the type is
// modelled at all. A struct field of a type that is not modelled is left
// out, so the rest of the struct can still be used; reading or writing that
// field is rejected where it happens.
func layoutOf(t types.Type) ([]leaf, bool) {
	if t == nil {
		return nil, false
	}
	one := func(sort logic.Sort) ([]leaf, bool) { return []leaf{{sort: sort, typ: t}}, true }
	switch u := t.Underlying().(type) {
	case *types.Basic:
		switch info := u.Info(); {
		case info&types.IsInteger != 0 && u.Kind() != types.Uintptr:
			return one(logic.Int)
		case info&types.IsBoolean != 0:
			return one(logic.Bool)
		case info&types.IsFloat != 0:
			return one(logic.Float)
		case info&types.IsString != 0:
			return one(logic.IntSeq)
		}
	case *types.Interface:
		if isError(t) {
			return one(logic.Err)
		}
	case *types.Pointer:
		if _, ok := pointee(t); ok {
			return one(logic.Ref)
		}
	case *types.Slice:
		return []leaf{
			{"#ref", logic.Ref, t, partRef}, {"#off", logic.Int, t, partOff},
			{"#len", logic.Int, t, partLen}, {"#cap", logic.Int, t, partCap},
		}, true
	case *types.Struct:
		var leaves []leaf
		for i := range u.NumFields() {
			field := u.Field(i)
			inner, ok := layoutOf(field.Type())
			if !ok || field.Name() == "_" {
				continue
			}
			for _, part := range inner {
				part.path = "." + field.Name() + part.path
				leaves = append(leaves, part)
			}
		}
		return leaves, true
	}
	return nil, false
}

// sortOf maps a Go type whose values are a single leaf to the sort of that
// leaf: numbers, booleans, strings, errors, and pointers.
func sortOf(t types.Type) (logic.Sort, bool) {
	// A struct is never a single leaf, even when only one of its fields is
	// modelled: the fields left out are part of its value too.
	if _, isStruct := t.Underlying().(*types.Struct); isStruct {
		return 0, false
	}
	leaves, ok := layoutOf(t)
	if !ok || len(leaves) != 1 || leaves[0].part != partValue {
		return 0, false
	}
	return leaves[0].sort, true
}

// fieldLeaves returns the range of leaves that field index of a struct type
// occupies in the layout of the struct, and reports whether the field is
// modelled.
func fieldLeaves(t types.Type, index int) (lo, hi int, ok bool) {
	u := t.Underlying().(*types.Struct)
	for i := range u.NumFields() {
		inner, modelled := layoutOf(u.Field(i).Type())
		if !modelled || u.Field(i).Name() == "_" {
			if i == index {
				return 0, 0, false
			}
			continue
		}
		if i == index {
			return lo, lo + len(inner), true
		}
		lo += len(inner)
	}
	return 0, 0, false
}

// under reports whether a leaf path lies at or below a prefix: ".pos.x" lies
// under ".pos" and under "", but ".position" does not lie under ".pos".
func under(path, prefix string) bool {
	rest, ok := strings.CutPrefix(path, prefix)
	return ok && (rest == "" || rest[0] == '.' || rest[0] == '#')
}

// zeroLeaf returns the zero value of one leaf.
func zeroLeaf(lf leaf) *logic.Term {
	switch {
	case lf.sort == logic.Ref:
		return logic.RefLit(0)
	case lf.sort == logic.Int:
		return logic.IntLit(0)
	case lf.sort == logic.Bool:
		return logic.False()
	case lf.sort == logic.Float:
		return logic.Const("float 0", logic.Float)
	case lf.sort == logic.Err:
		return logic.NilErr()
	}
	return logic.Fill(logic.IntLit(0), logic.IntLit(0))
}

// zeroValue returns the zero value of a type.
func zeroValue(t types.Type) value {
	leaves, _ := layoutOf(t)
	zero := make(value, len(leaves))
	for i, lf := range leaves {
		zero[i] = zeroLeaf(lf)
	}
	return zero
}

// wellFormed states what the type of a value guarantees about its leaves: an
// integer lies in the range of its type, a string is no longer than the
// largest int, a pointer is nil or an object that exists, and the numbers of
// a slice describe a stretch of an array that exists. brk is the number below
// which every existing object lies; it may be nil when that is not known.
func (pv *pkgVerifier) wellFormed(val value, t types.Type, brk *logic.Term) *logic.Term {
	leaves, _ := layoutOf(t)
	_, most, _ := pv.intRange(types.Typ[types.Int])
	zero := logic.IntLit(0)
	exists := func(ref *logic.Term) *logic.Term {
		if brk == nil {
			return logic.Le(zero, ref)
		}
		return logic.And(logic.Le(zero, ref), logic.Lt(ref, brk))
	}
	var facts []*logic.Term
	for i, lf := range leaves {
		switch {
		case lf.part == partRef:
			ref, off, length, capacity := val[i], val[i+1], val[i+2], val[i+3]
			facts = append(facts, exists(ref), logic.Le(zero, off), logic.Le(zero, length), logic.Le(length, capacity),
				logic.Le(logic.Add(off, capacity), logic.BigLit(most)))
		case lf.part != partValue:
		case lf.sort == logic.Ref:
			facts = append(facts, exists(val[i]))
		default:
			facts = append(facts, pv.typeFact(val[i], lf.typ))
		}
	}
	return logic.And(facts...)
}
