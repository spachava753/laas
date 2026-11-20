package vego

import (
	"go/importer"
	"go/token"
	"go/types"
	"testing"

	"golang.org/x/tools/go/analysis"
)

// TestHeldAs checks the two types that the rules about code walk as what
// their package lets them hold: sync/atomic.Pointer[T] as a *T, so that it
// holds code exactly when T does, and runtime.Pinner as nothing, which with
// atomic.Pointer[os.dirInfo] is all that an *os.File holds of unsafe
// pointers. atomic.Value is walked as it is declared and holds code. Every
// rule that asks whether a value can hold code answers the same.
func TestHeldAs(t *testing.T) {
	imports := importer.ForCompiler(token.NewFileSet(), "source", nil)
	lookup := func(path, name string) types.Type {
		pkg, err := imports.Import(path)
		if err != nil {
			t.Fatalf("import %s: %v", path, err)
		}
		return pkg.Scope().Lookup(name).Type()
	}
	pointerOf := func(elem types.Type) types.Type {
		generic := lookup("sync/atomic", "Pointer")
		instance, err := types.Instantiate(nil, generic, []types.Type{elem}, true)
		if err != nil {
			t.Fatalf("instantiate atomic.Pointer: %v", err)
		}
		return instance
	}
	field := func(name string, typ types.Type) *types.Var {
		return types.NewField(token.NoPos, nil, name, typ, false)
	}
	plain := types.NewStruct([]*types.Var{field("n", types.Typ[types.Int]), field("s", types.Typ[types.String])}, nil)
	callback := types.NewStruct([]*types.Var{field("f", types.NewSignatureType(nil, nil, nil, nil, nil, false))}, nil)
	raw := types.NewStruct([]*types.Var{field("p", types.Typ[types.UnsafePointer])}, nil)
	pv := &pkgVerifier{pass: &analysis.Pass{Pkg: types.NewPackage("held", "held")}}
	for _, tc := range []struct {
		what  string
		typ   types.Type
		holds bool
	}{
		{"atomic.Pointer of a plain struct", pointerOf(plain), false},
		{"atomic.Pointer of a struct that holds a function", pointerOf(callback), true},
		{"atomic.Pointer of a struct that holds an unsafe.Pointer", pointerOf(raw), true},
		{"a struct holding atomic.Pointer of a struct that holds a function", types.NewStruct([]*types.Var{field("p", pointerOf(callback))}, nil), true},
		{"atomic.Value", lookup("sync/atomic", "Value"), true},
		{"runtime.Pinner", lookup("runtime", "Pinner"), false},
		{"*os.File", types.NewPointer(lookup("os", "File")), false},
		{"a struct with an unsafe.Pointer", raw, true},
	} {
		if got := holdsCode(tc.typ, map[types.Type]bool{}); got != tc.holds {
			t.Errorf("holdsCode(%s) = %v, want %v", tc.what, got, tc.holds)
		}
		if got := heldCode(tc.typ, map[types.Type]bool{}) != ""; got != tc.holds {
			t.Errorf("heldCode(%s) names something: %v, want %v", tc.what, got, tc.holds)
		}
		// holdsCallable counts only code that verified code can make, and
		// verified code makes no value that an any holds.
		if got, want := holdsCallable(pv, tc.typ, map[types.Type]bool{}), tc.holds && tc.what != "atomic.Value"; got != want {
			t.Errorf("holdsCallable(%s) = %v, want %v", tc.what, got, want)
		}
		if got := pv.foreignCode(tc.typ, map[types.Type]bool{}) != ""; got != tc.holds {
			t.Errorf("foreignCode(%s) names something: %v, want %v", tc.what, got, tc.holds)
		}
		if got := !pv.dataType(tc.typ, map[types.Type]bool{}); got != tc.holds {
			t.Errorf("dataType(%s) = %v, want %v", tc.what, !got, !tc.holds)
		}
		if got := !pv.codeless(tc.typ, map[types.Type]bool{}); got != tc.holds {
			t.Errorf("codeless(%s) = %v, want %v", tc.what, !got, !tc.holds)
		}
	}
}
