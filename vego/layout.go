package vego

import (
	"fmt"
	"strings"
	"go/token"
	"go/types"
	"slices"
	"sync"

	"github.com/spachava753/laas/vego/internal/logic"
	"golang.org/x/tools/go/types/typeutil"
)

// The parts a leaf can be: an ordinary value, one of the four numbers that
// make up a slice, or one of the two that make up a pointer.
const (
	partValue = iota
	partRef   // which backing array the slice refers to; zero for a nil slice
	partOff   // where in that array the slice starts
	partLen
	partCap
	partPtr // which allocation the pointer points into; zero for nil
	partAt  // where in that allocation the struct it points to starts
	// partHidden is a struct field of a type that is not modelled. Nothing
	// is known of its value and nothing can be done with it alone, but it
	// is copied, overwritten, and forgotten with the struct it is part of.
	partHidden
	// partState is a state that a type of another module owns, such as
	// whether the calling goroutine holds a sync.Mutex; see stateDecl. No Go
	// code can read or write it.
	partState
	// partArray is an array of single values that refer to nothing (see
	// plainElem): a sequence of its length, whose element k is element k
	// of the array. It is not a single value, so nothing that takes a
	// sequence leaf for a string takes it for one.
	partArray
	// partArr says of a pointer to a number, a boolean, or a string
	// whether it points to an element of an array, in the elem region of
	// its type, or not, in its place region (F42).
	partArr
)

// leaf is one indivisible component of a Go value. A number, a boolean, a
// string, an error, and a map are a single leaf; a pointer is two, a slice
// four; a struct is the leaves of its fields, one after the other.
//
// A pointer is an allocation and a position in it, because a pointer may
// point to a struct that is part of something larger: an element of a slice,
// or a field of another struct.
type leaf struct {
	path string // how the leaf is reached from the value: ".pos.x", ".items#len"
	sort logic.Sort
	typ  types.Type // the type of the value or of the slice the leaf is part of
	part int
}

// value is a Go value in the logic: one term for each leaf of its type.
type value []*logic.Term

// typeKeys gives every type a key of its own. It decides by Go's notion of
// identical types and not by how a type is spelled, which differs for an
// alias, for byte and uint8, and for the parameter names of a function type.
// Struct tags are ignored, as Go ignores them when it converts a pointer or
// a slice from one struct type to another and the memory stays the same.
var typeKeys = struct {
	sync.Mutex
	known typeutil.Map
}{}

// typeKeyBase is where the numbers of typeKey start. The numbers depend on
// the order in which packages and functions ask, so nothing sent to Z3 may
// depend on them; the tests start them elsewhere to check that.
var typeKeyBase = 0

// typeKey names a type in the keys of memory regions. Types that are
// identical apart from struct tags get the same key, so that a write through
// one of them is seen through every other.
func typeKey(t types.Type) string {
	t = untagged(t)
	typeKeys.Lock()
	defer typeKeys.Unlock()
	if key, ok := typeKeys.known.At(t).(string); ok {
		return key
	}
	key := fmt.Sprintf("%s#%d", types.TypeString(t, nil), typeKeyBase+typeKeys.known.Len())
	typeKeys.known.Set(t, key)
	return key
}

// untagged returns a type without the struct tags of the unnamed types it is
// made of. A named type is its own type whatever its definition says.
func untagged(t types.Type) types.Type {
	tuple := func(vars *types.Tuple) *types.Tuple {
		list := make([]*types.Var, vars.Len())
		for i := range list {
			list[i] = types.NewParam(vars.At(i).Pos(), vars.At(i).Pkg(), vars.At(i).Name(), untagged(vars.At(i).Type()))
		}
		return types.NewTuple(list...)
	}
	switch t := types.Unalias(t).(type) {
	case *types.Pointer:
		return types.NewPointer(untagged(t.Elem()))
	case *types.Slice:
		return types.NewSlice(untagged(t.Elem()))
	case *types.Array:
		return types.NewArray(untagged(t.Elem()), t.Len())
	case *types.Chan:
		return types.NewChan(t.Dir(), untagged(t.Elem()))
	case *types.Map:
		return types.NewMap(untagged(t.Key()), untagged(t.Elem()))
	case *types.Signature:
		if t.TypeParams() != nil || t.RecvTypeParams() != nil {
			return t
		}
		return types.NewSignatureType(nil, nil, nil, tuple(t.Params()), tuple(t.Results()), t.Variadic())
	case *types.Struct:
		fields := make([]*types.Var, t.NumFields())
		for i := range fields {
			field := t.Field(i)
			fields[i] = types.NewField(field.Pos(), field.Pkg(), field.Name(), untagged(field.Type()), field.Embedded())
		}
		return types.NewStruct(fields, nil)
	}
	return t
}

func isError(t types.Type) bool {
	return types.Identical(t, types.Universe.Lookup("error").Type())
}

// pointee returns the struct type a pointer refers to. A pointer to a
// number, a boolean, or a string points to the box of its type (see boxOf),
// which pointee returns. Pointers to anything else, and to a struct that is
// not modelled, are not modelled.
func pointee(t types.Type) (types.Type, bool) {
	return pointeeAt(t, 0)
}

// pointeeAt is pointee for a pointer reached through depth pointers, which
// ends a type such as type P *P, whose chain of pointers has no end.
func pointeeAt(t types.Type, depth int) (types.Type, bool) {
	pointer, ok := t.Underlying().(*types.Pointer)
	if !ok || depth > 8 {
		return nil, false
	}
	if boxableAt(pointer.Elem(), depth+1) {
		return boxOf(pointer.Elem()), true
	}
	_, ok = pointer.Elem().Underlying().(*types.Struct)
	return pointer.Elem(), ok && !holdsArray(pointer.Elem())
}

// boxable reports whether a pointer to a value of the type points to the
// box of its type (F37, step 2, and F42, step 2): a number, a boolean, or
// a string; a slice of anything but arrays; a map, a pointer, an interface
// value, an error, or a function value that is modelled. A struct is not:
// a pointer to one points to the struct itself.
func boxable(t types.Type) bool { return boxableAt(t, 0) }

func boxableAt(t types.Type, depth int) bool {
	if singleValue(t) {
		return true
	}
	switch u := t.Underlying().(type) {
	case *types.Slice:
		return !isArray(u.Elem())
	case *types.Map:
		return mapKeyed(t)
	case *types.Pointer:
		_, ok := pointeeAt(t, depth)
		return ok
	case *types.Interface:
		return isError(t) || isIface(t)
	case *types.Signature:
		return isFunc(t)
	}
	return false
}

// singleValue reports whether a type is a number, a boolean, or a string:
// a single value that a pointer may point to (F37, step 2).
func singleValue(t types.Type) bool {
	u, ok := t.Underlying().(*types.Basic)
	if !ok {
		return false
	}
	info := u.Info()
	return info&(types.IsInteger|types.IsFloat|types.IsBoolean|types.IsString) != 0 && info&types.IsUntyped == 0 &&
		u.Kind() != types.Uintptr && u.Kind() != types.UnsafePointer
}

// boxes holds the box of each type of single value, for the whole process:
// a struct of one field of that type, declared in a package of its own so
// that no type of a program is identical to it. A pointer to a single value
// points to its box, which is an allocation of one cell, as a struct a
// pointer points to is; so every rule of pointers to structs is the rule of
// these pointers (frames, nil checks, Modifies, fresh, havoc, origins,
// ownership). The box is keyed by the untagged underlying type, since Go
// converts *MyInt to *int and the memory is the same; one box for a type in
// every package and every verifier keeps one region for it (F1 of the
// design review of F37).
var boxes = struct {
	sync.Mutex
	known typeutil.Map
	pkg   *types.Package
}{pkg: types.NewPackage("vego/box", "box")}

// boxOf returns the box of a type of single value.
func boxOf(t types.Type) types.Type {
	u := untagged(t.Underlying())
	switch t.Underlying().(type) {
	case *types.Interface, *types.Signature:
		// An interface value and a function value are modelled by their
		// named types, whose contracts and states they carry, and the
		// underlying type of error is an interface that is no error. The
		// regions of the box are still those of the underlying type
		// (cellsOf), so a pointer converted between two such named types
		// sees one memory.
		u = types.Unalias(t)
	}
	boxes.Lock()
	defer boxes.Unlock()
	if box, ok := boxes.known.At(u).(types.Type); ok {
		return box
	}
	box := types.NewStruct([]*types.Var{types.NewField(token.NoPos, boxes.pkg, "v", u, false)}, nil)
	boxes.known.Set(u, box)
	return box
}

// isBox reports whether a type is the box of a single value, and returns
// the type of what it holds.
func isBox(t types.Type) (types.Type, bool) {
	s, ok := t.(*types.Struct)
	if !ok || s.NumFields() != 1 || s.Field(0).Pkg() != boxes.pkg {
		return nil, false
	}
	return s.Field(0).Type(), true
}

// isBoxType reports whether a type is the box of a single value.
func isBoxType(t types.Type) bool {
	_, box := isBox(t.Underlying())
	return box
}

// valueSize returns how many positions a value of the type that a pointer
// points to covers in the stretch of the pointer's target: a struct's size
// in bytes, and one for a box, whose one cell is counted in bytes at a
// place and in elements in an array (F13 of the review of step 1 of F42).
func (pv *pkgVerifier) valueSize(t types.Type) int64 {
	if isBoxType(t) {
		return 1
	}
	return pv.pass.TypesSizes.Sizeof(t)
}

// storedAs returns the type whose cells hold a variable of type t that
// lives in memory: the box of a single value, or the type itself.
func storedAs(t types.Type) types.Type {
	if boxable(t) {
		return boxOf(t)
	}
	return t
}

// elemType returns the element type of a slice type.
func elemType(t types.Type) types.Type {
	return t.Underlying().(*types.Slice).Elem()
}

// layoutOf lists the leaves of a type, and reports whether the type is
// modelled at all. A struct field of a type that is not modelled is one
// hidden leaf, so the rest of the struct can still be used; reading or
// writing that field alone is rejected where it happens. A blank field is
// left out, since no program can tell what it holds.
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
		if isIface(t) {
			return one(logic.Ref)
		}
	case *types.Pointer:
		if _, ok := pointee(t); ok && boxable(u.Elem()) {
			return []leaf{{"#ptr", logic.Ref, t, partPtr}, {"#at", logic.Int, t, partAt}, {"#arr", logic.Bool, t, partArr}}, true
		}
		if _, ok := pointee(t); ok {
			return []leaf{{"#ptr", logic.Ref, t, partPtr}, {"#at", logic.Int, t, partAt}}, true
		}
	case *types.Map:
		if mapKeyed(t) {
			return one(logic.Ref)
		}
	case *types.Signature:
		if isFunc(t) {
			return one(logic.Ref)
		}
	case *types.Array:
		if sort, ok := plainElem(u.Elem()); ok {
			return []leaf{{sort: logic.SeqOf(sort), typ: t, part: partArray}}, true
		}
	case *types.Slice:
		return []leaf{
			{"#ref", logic.Ref, t, partRef}, {"#off", logic.Int, t, partOff},
			{"#len", logic.Int, t, partLen}, {"#cap", logic.Int, t, partCap},
		}, true
	case *types.Struct:
		if holdsArray(t) {
			return nil, false
		}
		var leaves []leaf
		for i := range u.NumFields() {
			field := u.Field(i)
			inner, ok := fieldLayout(field.Type())
			if field.Name() == "_" {
				continue
			}
			if !ok {
				inner = []leaf{{sort: logic.Int, typ: field.Type(), part: partHidden}}
			}
			for _, part := range inner {
				part.path = "." + field.Name() + part.path
				leaves = append(leaves, part)
			}
		}
		// The states come after the fields, so that the leaves of every
		// field stay where fieldLeaves finds them.
		for _, decl := range statesOf(u) {
			leaves = append(leaves, leaf{path: "@" + decl.name, sort: logic.Bool, typ: types.Typ[types.Bool], part: partState})
		}
		return leaves, true
	}
	return nil, false
}

// plainElem reports whether values of a type can be the elements of an
// array that is modelled, and gives their sort: numbers and booleans, which
// are single values that refer to nothing and hold no state. An array of
// anything else is not modelled.
func plainElem(t types.Type) (logic.Sort, bool) {
	u, ok := t.Underlying().(*types.Basic)
	if !ok {
		return 0, false
	}
	switch info := u.Info(); {
	case info&types.IsInteger != 0 && u.Kind() != types.Uintptr:
		return logic.Int, true
	case info&types.IsBoolean != 0:
		return logic.Bool, true
	case info&types.IsFloat != 0:
		return logic.Float, true
	}
	return 0, false
}

// isArray reports whether a type is an array type.
func isArray(t types.Type) bool {
	if t == nil {
		return false
	}
	_, ok := t.Underlying().(*types.Array)
	return ok
}

// arrayLen returns the length of an array type.
func arrayLen(t types.Type) int64 { return t.Underlying().(*types.Array).Len() }

// elemLayout is layoutOf for the element of a slice or what a map holds:
// an array there is not modelled yet. An element of a slice of arrays
// would lie in a region of its own, while a slice of the element reaches
// the same bytes through the region of the array's elements.
func elemLayout(t types.Type) ([]leaf, bool) {
	if isArray(t) {
		return nil, false
	}
	return layoutOf(t)
}

// fieldLayout is layoutOf for the type of a struct field. An array there is
// modelled when its elements take one byte (byteArray), and not otherwise.
func fieldLayout(t types.Type) ([]leaf, bool) {
	if isArray(t) && !byteArray(t) {
		return nil, false
	}
	return layoutOf(t)
}

// byteArray reports whether a type is an array of numbers or booleans of
// one byte each: byte, uint8, int8, and bool, which take one byte on every
// target. Such an array may lie in a struct: in the region of its elements
// the position of a cell is then its byte address, as in the region of a
// field, so every test that compares positions with the bytes a struct
// covers holds of it. An array of larger elements lies at the floor of its
// address over the size of an element, and those tests would have to be
// made per region, the footprints of conversions among them (F1 of the
// design review of F36); it is not modelled inside a struct.
func byteArray(t types.Type) bool {
	array, ok := t.Underlying().(*types.Array)
	if !ok {
		return false
	}
	basic, ok := array.Elem().Underlying().(*types.Basic)
	if !ok {
		return false
	}
	switch basic.Kind() {
	case types.Uint8, types.Int8, types.Bool:
		return true
	}
	return false
}

// holdsArrayValue reports whether a value of the type is an array or holds
// one by value, in a field at any depth through structs.
func holdsArrayValue(t types.Type) bool {
	switch u := t.Underlying().(type) {
	case *types.Array:
		return true
	case *types.Struct:
		for field := range u.Fields() {
			if field.Name() != "_" && holdsArrayValue(field.Type()) {
				return true
			}
		}
	}
	return false
}

// pointsToArray reports whether a type is a pointer to a struct that holds
// an array by value.
func pointsToArray(t types.Type) bool {
	object, ok := pointee(t)
	return ok && holdsArrayValue(object)
}

// heldReason says why an interface value or an error cannot hold a value
// of a type, or returns "": its values are not modelled, or it holds an
// array, which no interface value is modelled to hold yet.
func heldReason(t types.Type) string {
	if _, ok := layoutOf(t); !ok {
		return "values of its type are not modelled"
	}
	if holdsArrayValue(t) {
		return "an interface value or an error cannot hold an array yet"
	}
	return ""
}

// holdsArray reports whether a value of the type has an array with elements
// inside it that a struct cannot hold as a run of cells: it is one, or a
// struct with such a field. A slice of the array is a second view of that
// memory, which a hidden leaf would not show, so such a struct is not
// modelled at all. An array of one-byte elements is modelled in a struct
// (byteArray). A blank field cannot be sliced.
func holdsArray(t types.Type) bool {
	switch u := t.Underlying().(type) {
	case *types.Array:
		return u.Len() != 0 && !byteArray(t)
	case *types.Struct:
		for field := range u.Fields() {
			if field.Name() != "_" && holdsArray(field.Type()) {
				return true
			}
		}
	}
	return false
}

// sortOf maps a Go type whose values are a single leaf to the sort of that
// leaf: numbers, booleans, strings, errors, maps, and functions.
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
		inner, modelled := fieldLayout(u.Field(i).Type())
		switch {
		case u.Field(i).Name() == "_" && i == index:
			return 0, 0, false
		case u.Field(i).Name() == "_":
			continue
		case !modelled && i == index:
			return lo, lo + 1, false
		case !modelled:
			lo++
			continue
		}
		if i == index {
			return lo, lo + len(inner), true
		}
		lo += len(inner)
	}
	return 0, 0, false
}

// cell says where one leaf of a value lies when the value is stored in
// memory: in which region, and how far from the start of the value.
//
// A leaf that is a field of a struct lies in the region of that struct type
// and field, at the field's byte offset; for a struct inside a struct that is
// the innermost one, so that a pointer to the inner struct finds the same
// cell. A leaf of anything else, which can only be stored as an element of a
// slice, lies in the region of its type at offset zero. Go's types guarantee
// that a piece of memory is only ever used at one type, so no two regions
// describe the same memory.
//
// An array lies in a run of cells, one for each element, in the region of
// its element type, the region the elements of a slice of that type use:
// run is its length. Element k of an array at byte A of its allocation is
// at position ⌊A/unit⌋ + k, where unit is the size of the element; see
// start. A cell that is not a run has run 0 and unit 0.
type cell struct {
	key  string
	sort logic.Sort
	off  int64
	run  int64
	unit int64
	// either is set for the cell of a box: the cell it is when the pointer
	// to the box points to an element of an array, in the elem region of
	// its type, at the same position. arr is that pointer's #arr once the
	// cell is resolved for it (resolveCells); a cell with either and no
	// arr is unresolved, which a read or a write of it must not meet. A
	// target may cover both, which is the cell of a place region and of
	// an elem region at one position, of which no allocation holds both.
	either *cell
	arr    *logic.Term
}

// resolveCells returns the cells of what a pointer points to for the
// pointer's value: for a box, the cell of its place region when the
// pointer's #arr is false, of its elem region when it is true, and the
// cell with both, to be chosen by #arr, when it is not known.
func resolveCells(cells []cell, ptr value) []cell {
	if !isBoxCells(cells) {
		return cells
	}
	if len(ptr) < 3 {
		// The place of a variable that lives in its box, which is no
		// element of an array. Every value of a pointer type has #arr, and
		// only &xs[i] and &a[i] make one that is true.
		return resolveBox(cells, logic.False())
	}
	return resolveBox(cells, ptr[2])
}

// isBoxCells reports whether cells are those of a box: each has the cell
// of the elem region beside it.
func isBoxCells(cells []cell) bool {
	return len(cells) > 0 && !slices.ContainsFunc(cells, func(c cell) bool { return c.either == nil })
}

// resolveBox resolves the cells of a box, one for each leaf of what it
// holds, for a pointer whose #arr is arr.
func resolveBox(cells []cell, arr *logic.Term) []cell {
	out := make([]cell, len(cells))
	for i, c := range cells {
		switch arr.Op {
		case logic.OpTrue:
			out[i] = *c.either
		case logic.OpFalse:
			c.either = nil
			out[i] = c
		default:
			c.arr = arr
			out[i] = c
		}
	}
	return out
}

// ownPlace is resolveCells for a box at a place of its own: a variable
// whose address is taken, or what new made.
func ownPlace(cells []cell) []cell {
	if !isBoxCells(cells) {
		return cells
	}
	return resolveBox(cells, logic.False())
}

// start returns the position of a cell of a value stored at position at:
// the cell itself, or the first element of a run.
func (c cell) start(at *logic.Term) *logic.Term {
	if !c.isRun() {
		return logic.Add(at, logic.IntLit(c.off))
	}
	// An array of its own starts at a known position.
	if at.Op == logic.OpIntLit && at.Big == nil {
		return logic.IntLit((at.Val + c.off) / max(c.unit, 1))
	}
	pos := logic.Add(at, logic.IntLit(c.off))
	if c.unit > 1 {
		pos = logic.Div(pos, logic.IntLit(c.unit))
	}
	return pos
}

// end returns the position after the last one a cell covers.
func (c cell) end(at *logic.Term) *logic.Term {
	if !c.isRun() {
		return logic.Add(at, logic.IntLit(c.off+1))
	}
	return logic.Add(c.start(at), logic.IntLit(c.run))
}

// isRun reports whether a cell is the run of an array.
func (c cell) isRun() bool { return c.unit > 0 }

// cellsOf returns the cells of the leaves of a type, in the order of
// layoutOf.
func (pv *pkgVerifier) cellsOf(t types.Type) []cell {
	u, isStruct := t.Underlying().(*types.Struct)
	leaves, _ := layoutOf(t)
	if array, ok := t.Underlying().(*types.Array); ok {
		elem := pv.cellsOf(array.Elem())[0]
		elem.run, elem.unit = array.Len(), pv.pass.TypesSizes.Sizeof(array.Elem())
		return []cell{elem}
	}
	if !isStruct {
		cells := make([]cell, len(leaves))
		for i, lf := range leaves {
			key := "elem " + typeKey(t) + lf.path
			if boxable(t) {
				// An element of a []MyInt is an int that &xs[i] can point
				// to as a *MyInt and convert to an *int.
				key = "elem " + typeKey(untagged(t.Underlying())) + lf.path
			}
			cells[i] = cell{key: key, sort: lf.sort}
		}
		return cells
	}
	fields := slices.Collect(u.Fields())
	offsets := pv.pass.TypesSizes.Offsetsof(fields)
	var cells []cell
	for i, field := range fields {
		inner, ok := fieldLayout(field.Type())
		if field.Name() == "_" {
			continue
		}
		if !ok {
			cells = append(cells, cell{key: typeKey(u) + "." + field.Name(), sort: logic.Int, off: offsets[i]})
			continue
		}
		if isArray(field.Type()) {
			// The run of the array, in the region of its elements, from
			// the field's offset.
			run := pv.cellsOf(field.Type())[0]
			run.off += offsets[i]
			cells = append(cells, run)
			continue
		}
		if _, nested := field.Type().Underlying().(*types.Struct); nested {
			for _, c := range pv.cellsOf(field.Type()) {
				c.off += offsets[i]
				cells = append(cells, c)
			}
			continue
		}
		key := typeKey(u) + "." + field.Name()
		// A single value that a pointer can point to lies in the region of
		// its type, with every box (addressed.go): an exported field, an
		// embedded one whose type has a pointer method, and one its
		// package's decision covers.
		_, box := isBox(u)
		addressable := box || field.Exported() || field.Pkg() == nil || field.Embedded() && hasPointerMethod(field.Type())
		if !addressable {
			// A package without a decision makes every field addressable.
			fact := pv.addressedFactOf(field.Pkg())
			addressable = fact == nil || fact.All || slices.Contains(fact.Names, field.Name())
		}
		if boxable(field.Type()) && addressable {
			key = "place " + typeKey(untagged(field.Type().Underlying()))
		}
		for _, lf := range inner {
			c := cell{key: key + lf.path, sort: lf.sort, off: offsets[i]}
			if box {
				c.either = &cell{key: "elem " + typeKey(untagged(field.Type().Underlying())) + lf.path, sort: lf.sort}
			}
			cells = append(cells, c)
		}
	}
	// A state lies at the start of its struct, in a region that only
	// states of this struct type with this name use. A type with a state
	// has a size, so two values of it never start at the same position.
	for _, decl := range statesOf(u) {
		cells = append(cells, cell{key: typeKey(u) + "@" + decl.name, sort: logic.Bool})
	}
	return cells
}

// A place region, "place " and the typeKey of an untagged underlying type,
// holds the single values of the type that are not elements of arrays and
// that a pointer can point to: the addressable fields (addressed.go) of
// every struct type, and every box, each at its byte address in its
// allocation. It is keyed as the box is, since Go converts *MyInt to *int.
// The elements of arrays of the type lie in "elem " and the same key, at
// the floor of their byte address over their size.

// isPlaceKey reports whether a region is a place region.
func isPlaceKey(key string) bool { return strings.HasPrefix(key, "place ") }

// span returns how many positions a stored value of the type takes: its
// size in bytes for a struct, whose fields have positions of their own, and
// one for anything else.
func (pv *pkgVerifier) span(t types.Type) int64 {
	// A box is one cell, named by its first position, whether the pointer
	// to it counts bytes, at a place, or elements, in an array (F42).
	if _, box := isBox(t); box {
		return 1
	}
	if _, isStruct := t.Underlying().(*types.Struct); isStruct {
		return pv.pass.TypesSizes.Sizeof(t)
	}
	return 1
}

// offsetsOf returns the byte offsets in a struct type at which a struct of
// another type can lie: the struct itself when the two have one underlying
// type, ignoring tags, and every field of such a type at any depth through
// struct fields.
func (pv *pkgVerifier) offsetsOf(outer, inner types.Type) []int64 {
	var offsets []int64
	var walk func(t types.Type, base int64)
	walk = func(t types.Type, base int64) {
		if types.IdenticalIgnoreTags(t.Underlying(), inner.Underlying()) {
			offsets = append(offsets, base)
		}
		st, ok := t.Underlying().(*types.Struct)
		if !ok {
			return
		}
		fields := slices.Collect(st.Fields())
		for i, offset := range pv.pass.TypesSizes.Offsetsof(fields) {
			walk(fields[i].Type(), base+offset)
		}
	}
	walk(outer, 0)
	return offsets
}

// fieldOffset returns the byte offset of a field in a struct type.
func (pv *pkgVerifier) fieldOffset(t types.Type, index int) int64 {
	fields := slices.Collect(t.Underlying().(*types.Struct).Fields())
	return pv.pass.TypesSizes.Offsetsof(fields)[index]
}

// zeroLeaf returns the zero value of one leaf.
func zeroLeaf(lf leaf) *logic.Term {
	switch {
	case lf.part == partArray:
		array := lf.typ.Underlying().(*types.Array)
		elem := mustLayout(array.Elem())[0]
		return logic.Fill(logic.IntLit(array.Len()), zeroLeaf(elem))
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
			// The array the slice lies in was allocated, so it is no larger
			// than an allocation can be. The offset counts positions, which
			// are bytes for structs and elements for anything else.
			// Elements of size zero take no room, so any number of them
			// that an int can count fits.
			elem := elemType(lf.typ)
			size, unit := pv.pass.TypesSizes.Sizeof(elem), int64(1)
			if pv.span(elem) == 1 {
				unit = size
			}
			end := logic.Add(logic.Mul(off, logic.IntLit(unit)), logic.Mul(capacity, logic.IntLit(size)))
			// A slice without an array is nil, and Go gives a nil slice no
			// length and no capacity: without unsafe nothing else makes one.
			nilEmpty := logic.Implies(logic.Eq(ref, logic.RefLit(0)), logic.Eq(capacity, zero))
			facts = append(facts, exists(ref), nilEmpty, logic.Le(zero, off), logic.Le(zero, length), logic.Le(length, capacity),
				logic.Le(end, pv.marks().arrayEnd), pv.typeFact(capacity, types.Typ[types.Int]))
		case lf.part == partPtr:
			facts = append(facts, exists(val[i]), logic.Le(zero, val[i+1]), logic.Le(val[i+1], logic.BigLit(pv.maxAlloc())))
		case lf.part == partArray:
			// An array has the length of its type. What the type of its
			// elements says of each is stated where an element is read,
			// as for the bytes of a string.
			facts = append(facts, logic.Eq(logic.Len(val[i]), logic.IntLit(arrayLen(lf.typ))))
		case lf.part != partValue:
		case lf.sort == logic.Ref && isIface(lf.typ):
			// The reference of an interface value is not the address of
			// what it holds; its home, where its states lie, exists, as
			// what it holds does. The nil interface holds nothing and has
			// no home. See ifacestate.go.
			known := []*logic.Term{exists(home(val[i])), logic.Lt(logic.IntLit(0), home(val[i]))}
			if pv.hasStates(lf.typ) || pv.inputsOf() != nil {
				// So does the row of its states (S0b of F34), and, under
				// the declaration that inputs end, of its unread (F39).
				known = append(known, exists(skey(val[i])), logic.Lt(logic.IntLit(0), skey(val[i])))
			}
			facts = append(facts, logic.Or(logic.Eq(val[i], logic.RefLit(0)), logic.And(known...)))
		case lf.sort == logic.Ref && holdsCodeRef(lf.typ):
			// A function value refers to no allocation, and the reference
			// of an interface value is not the address of what it holds.
		case lf.sort == logic.Ref:
			facts = append(facts, exists(val[i]))
		default:
			facts = append(facts, pv.typeFact(val[i], lf.typ))
		}
	}
	return logic.And(facts...)
}

// isPointerType reports whether a type is a pointer type.
func isPointerType(t types.Type) bool {
	_, ok := t.Underlying().(*types.Pointer)
	return ok
}
