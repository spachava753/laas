package vego

import (
	"errors"
	"fmt"
	"go/ast"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"reflect"
	"slices"
	"strings"
	"testing"

	"golang.org/x/tools/go/packages"
)

// TestCanonicalNames checks that two types share a canonical name exactly
// when types.Identical holds of them, over types that differ in the ways
// Go's identity tells apart and in ways it does not: aliases, byte and
// uint8, parameter names, struct tags, unexported names of two packages,
// type arguments, and channel directions. A type declared inside a
// function has no name.
func TestCanonicalNames(t *testing.T) {
	parallel(t)
	const src = `package p

type E int
type F int
type A = E
type S struct{ X int; y string }
type T struct{ X int; y string }
type G[V any] struct{ v V }
type I interface{ M(int) error }

var Types = []any{
	E(0), F(0), A(0), byte(0), uint8(0), rune(0), int32(0), int(0), "",
	(*E)(nil), (**E)(nil), []E(nil), map[E]string(nil), map[string]E(nil),
	S{}, T{}, &S{},
	struct{ X int }{}, struct{ X int ` + "`json:\"x\"`" + ` }{}, struct{ y int }{}, struct{ E }{}, struct{ E E }{},
	G[int]{}, G[uint8]{}, G[byte]{}, G[E]{}, G[A]{},
	(func(a int) error)(nil), (func(b int) error)(nil), (func(...int))(nil), (func([]int))(nil),
	(chan int)(nil), (<-chan int)(nil), (chan<- int)(nil),
	(I)(nil), (interface{ M(int) error })(nil), (interface{ m(int) error })(nil),
}

func Local() any {
	type L int
	return L(0)
}
`
	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "p.go", src, 0)
	if err != nil {
		t.Fatal(err)
	}
	info := &types.Info{Types: map[ast.Expr]types.TypeAndValue{}, Defs: map[*ast.Ident]types.Object{}}
	_, err = (&types.Config{Importer: importer.Default()}).Check("example.com/p", fset, []*ast.File{file}, info)
	if err != nil {
		t.Fatal(err)
	}
	var list []types.Type
	for _, decl := range file.Decls {
		gen, ok := decl.(*ast.GenDecl)
		if !ok || gen.Tok != token.VAR {
			continue
		}
		lit := gen.Specs[0].(*ast.ValueSpec).Values[0].(*ast.CompositeLit)
		for _, elt := range lit.Elts {
			list = append(list, info.TypeOf(elt))
		}
	}
	// The same struct with an unexported field of another package.
	other := types.NewPackage("example.com/q", "q")
	list = append(list, types.NewStruct([]*types.Var{types.NewField(token.NoPos, other, "y", types.Typ[types.Int], false)}, nil))
	for i, a := range list {
		an, ok := canonicalName(a)
		if !ok {
			t.Fatalf("%v has no canonical name", a)
		}
		for _, b := range list[i+1:] {
			bn, _ := canonicalName(b)
			if (an == bn) != types.Identical(a, b) {
				t.Errorf("%v and %v: names %q and %q, identical %v", a, b, an, bn, types.Identical(a, b))
			}
		}
	}
	var local types.Object
	for id, obj := range info.Defs {
		if id.Name == "L" {
			local = obj
		}
	}
	if name, ok := canonicalName(local.Type()); ok {
		t.Errorf("a type declared in a function has the name %q", name)
	}
	if name, ok := canonicalName(types.NewPointer(local.Type())); ok {
		t.Errorf("a pointer to a type declared in a function has the name %q", name)
	}
}

// TestMadeErrorTypes checks that the names noteMadeTag states of a made error
// are the canonical names of the types of package errors and fmt that
// errors.New and fmt.Errorf return, as go/types sees them.
func TestMadeErrorTypes(t *testing.T) {
	parallel(t)
	loaded, err := packages.Load(&packages.Config{Mode: packages.LoadSyntax}, "errors", "fmt")
	if err != nil {
		t.Fatal(err)
	}
	var names []string
	for _, pkg := range loaded {
		for _, name := range []string{"errorString", "wrapError", "wrapErrors"} {
			if obj := pkg.Types.Scope().Lookup(name); obj != nil {
				ptr := types.NewPointer(obj.Type())
				canon, ok := canonicalName(ptr)
				if !ok {
					t.Fatalf("%s.%s has no canonical name", pkg.PkgPath, name)
				}
				names = append(names, canon)
				// The methods madeImplements decides by (S2 of F34).
				methods := types.NewMethodSet(ptr)
				listed := madeErrorMethods[canon]
				if methods.Len() != len(listed) {
					t.Errorf("%s has %d methods, and madeErrorMethods lists %d", canon, methods.Len(), len(listed))
				}
				for _, m := range listed {
					sel := methods.Lookup(nil, m.name)
					want := types.NewSignatureType(nil, nil, nil, types.NewTuple(), types.NewTuple(types.NewVar(token.NoPos, nil, "", m.result)), false)
					if sel == nil || !types.Identical(sel.Type(), want) {
						t.Errorf("%s has no method %s of type %s", canon, m.name, want)
					}
				}
			}
		}
	}
	slices.Sort(names)
	want := slices.Sorted(slices.Values(madeErrorTypes))
	if !slices.Equal(names, want) {
		t.Fatalf("the types are %q, and madeErrorTypes lists %q", names, want)
	}
}

// TestErrorfTypes checks the type madeErrorType says each call
// of errors.New and fmt.Errorf gives, by the count of %w verbs that
// wrapVerbs reads, against the errors the running toolchain makes (F17 of
// the review of S2 of F34).
func TestErrorfTypes(t *testing.T) {
	inner := errors.New("inner")
	cases := []struct {
		format string
		args   []any
	}{
		{"plain", nil},
		{"%%w", nil},
		{"%d", []any{1}},
		{"%w", nil},
		{"w: %w", []any{inner}},
		{"w: %w", []any{3}},
		{"%v %w", []any{1, inner}},
		{"%v %w", []any{inner}},
		{"%5.2w", []any{inner}},
		{"%w %w", []any{inner, inner}},
		{"%w %d %w", []any{inner, 1}},
	}
	for _, c := range cases {
		err := fmt.Errorf(c.format, c.args...)
		count, ok := wrapVerbs(c.format, len(c.args))
		if !ok {
			t.Errorf("wrapVerbs(%q) does not read it", c.format)
			continue
		}
		want := madeErrorTypes[min(count, 2)]
		if got := strings.ReplaceAll(want, `"`, ""); fmt.Sprintf("%T", err) != got {
			t.Errorf("fmt.Errorf(%q) gives a %T, and %d %%w verbs say %s", c.format, err, count, got)
		}
	}
	if got := strings.ReplaceAll(madeErrorTypes[0], `"`, ""); fmt.Sprintf("%T", errors.New("x")) != got {
		t.Errorf("errors.New gives a %T, not %s", errors.New("x"), got)
	}
}

// TestNoPanicEq checks which types == on two interface values that hold
// them may panic on, against Go itself (S3 of F34).
func TestNoPanicEq(t *testing.T) {
	type blank struct {
		A int
		_ []int
	}
	type holder struct{ X any }
	type plain struct {
		A int
		B *int
		C [2]string
		D chan int
		E float64
	}
	cases := []struct {
		value  any
		panics bool
	}{
		{1, false}, {"s", false}, {1.5, false}, {new(int), false}, {make(chan int), false},
		{[2]int{}, false}, {plain{}, false},
		{[]int{}, true}, {map[int]int{}, true}, {func() {}, true}, {blank{}, true}, {holder{}, true},
	}
	for _, c := range cases {
		typ := reflect.TypeOf(c.value)
		goPanics := func() (p bool) {
			defer func() { p = recover() != nil }()
			_ = c.value == reflect.New(typ).Elem().Interface()
			return false
		}()
		// A holder of an int does not panic, so the check is of the type,
		// which holds an interface value that may hold anything.
		if typ.Name() == "holder" {
			goPanics = func() (p bool) {
				defer func() { p = recover() != nil }()
				_ = any(holder{X: []int{}}) == any(holder{X: []int{}})
				return false
			}()
		}
		got := noPanicWhy(goType(t, c.value), map[types.Type]bool{}) != ""
		if got != c.panics || goPanics != c.panics {
			t.Errorf("%T: noPanicWhy says %v, Go panics %v, want %v", c.value, got, goPanics, c.panics)
		}
	}
}

// goType returns the go/types type of a value of one of the shapes
// TestNoPanicEq uses.
func goType(t *testing.T, value any) types.Type {
	t.Helper()
	field := func(name string, typ types.Type) *types.Var {
		return types.NewField(token.NoPos, nil, name, typ, false)
	}
	anyType := types.Universe.Lookup("any").Type()
	intT, strT, floatT := types.Typ[types.Int], types.Typ[types.String], types.Typ[types.Float64]
	switch reflect.TypeOf(value).Name() {
	case "blank":
		return types.NewStruct([]*types.Var{field("A", intT), field("_", types.NewSlice(intT))}, nil)
	case "holder":
		return types.NewStruct([]*types.Var{field("X", anyType)}, nil)
	case "plain":
		return types.NewStruct([]*types.Var{field("A", intT), field("B", types.NewPointer(intT)), field("C", types.NewArray(strT, 2)),
			field("D", types.NewChan(types.SendRecv, intT)), field("E", floatT)}, nil)
	}
	switch value.(type) {
	case int:
		return intT
	case string:
		return strT
	case float64:
		return floatT
	case *int:
		return types.NewPointer(intT)
	case chan int:
		return types.NewChan(types.SendRecv, intT)
	case [2]int:
		return types.NewArray(intT, 2)
	case []int:
		return types.NewSlice(intT)
	case map[int]int:
		return types.NewMap(intT, intT)
	case func():
		return types.NewSignatureType(nil, nil, nil, nil, nil, false)
	}
	t.Fatalf("no type for %T", value)
	return nil
}
