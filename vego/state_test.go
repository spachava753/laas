package vego

import (
	"go/importer"
	"go/token"
	"go/types"
	"slices"
	"strings"
	"testing"

	"github.com/spachava753/laas/vego/internal/logic"
	"golang.org/x/tools/go/analysis"
)

// TestStateDeclarations checks that a project trust file can declare a
// state, which is checked against the type where the type is seen, and
// every state the shipped files declare. The type exists. A struct has a
// size, so that two values of it never start at the same position, and its
// layout and cells carry the state once, after its fields; a type defined
// from it shares its memory and so its states. An interface is one that a
// state can be declared on: a defined interface type that declares a
// method of its own.
func TestStateDeclarations(t *testing.T) {
	parallel(t)
	t.Run("project", func(t *testing.T) {
		file := parseTrustFile("vego-trusted.yaml", []byte("version: 1\nstate:\n  example.com/x.T:\n    open:\n      reason: r\n"), false)
		if len(file.problems) != 0 {
			t.Fatalf("problems = %+v", file.problems)
		}
		if len(file.states[`"example.com/x".T`]) != 1 {
			t.Fatalf("states = %+v", file.states)
		}
		// A path in quotes is the same type.
		quoted := parseTrustFile("vego-trusted.yaml", []byte("version: 1\nstate:\n  '\"example.com/x\".T':\n    open:\n      reason: r\n"), false)
		if len(quoted.problems) != 0 || len(quoted.states[`"example.com/x".T`]) != 1 {
			t.Fatalf("problems = %+v, states = %+v", quoted.problems, quoted.states)
		}
	})
	fset := token.NewFileSet()
	imports := importer.ForCompiler(fset, "source", nil)
	pv := &pkgVerifier{pass: &analysis.Pass{Fset: fset, TypesSizes: types.SizesFor("gc", "amd64")}}
	declared := 0
	for path, byType := range shippedStates() {
		pkg, err := imports.Import(path)
		if err != nil {
			t.Fatalf("import %s: %v", path, err)
		}
		for name, decls := range byType {
			declared++
			obj, ok := pkg.Scope().Lookup(name).(*types.TypeName)
			if !ok {
				t.Errorf("%s.%s: no such type", path, name)
				continue
			}
			if types.IsInterface(obj.Type()) {
				if problem := pv.stateDeclProblem(obj); problem != "" {
					t.Errorf("%s.%s %s", path, name, problem)
				}
				continue
			}
			u, isStruct := obj.Type().Underlying().(*types.Struct)
			if !isStruct {
				t.Errorf("%s.%s is not a struct type", path, name)
				continue
			}
			// statesOf finds a declaration through the package of the
			// struct's fields. A struct with only exported fields is
			// identical to a struct written in any package, which would
			// share its regions without its states.
			if !slices.ContainsFunc(slices.Collect(u.Fields()), func(f *types.Var) bool { return !f.Exported() }) {
				t.Errorf("%s.%s has only exported fields, so a struct of another package can be identical to it and would have no states", path, name)
			}
			if size := pv.pass.TypesSizes.Sizeof(obj.Type()); size == 0 {
				t.Errorf("%s.%s has no size, so two of its values may share their states", path, name)
			}
			defined := types.NewNamed(types.NewTypeName(token.NoPos, types.NewPackage("other", "other"), "M", nil), u, nil)
			for _, typ := range []types.Type{obj.Type(), defined} {
				leaves, ok := layoutOf(typ)
				if !ok {
					t.Errorf("%s is not modelled", typ)
					continue
				}
				cells := pv.cellsOf(typ)
				if len(cells) != len(leaves) {
					t.Errorf("%s: %d cells for %d leaves", typ, len(cells), len(leaves))
				}
				tail := leaves[len(leaves)-len(decls):]
				for i, decl := range decls {
					if tail[i].path != "@"+decl.name || tail[i].part != partState {
						t.Errorf("%s: leaf %d is %q, want the state %s", typ, len(leaves)-len(decls)+i, tail[i].path, decl.name)
					}
					if c := cells[len(cells)-len(decls)+i]; !strings.HasSuffix(c.key, "@"+decl.name) || c.off != 0 {
						t.Errorf("%s: the cell of %s is %+v", typ, decl.name, c)
					}
				}
			}
		}
	}
	if declared == 0 {
		t.Fatal("no shipped file declares a state")
	}
}

// TestUnexportedFields checks which package may name an unexported field
// in a formula: only the one that declares it, and no shipped contract.
func TestUnexportedFields(t *testing.T) {
	parallel(t)
	imports := importer.ForCompiler(token.NewFileSet(), "source", nil)
	syncPkg, err := imports.Import("sync")
	if err != nil {
		t.Fatal(err)
	}
	mutex := types.NewPointer(syncPkg.Scope().Lookup("Mutex").Type())
	steps := []logic.Step{{Field: "mu"}}
	if _, _, err := plan(mutex, steps, syncPkg); err != nil {
		t.Errorf("package sync cannot name its own field: %v", err)
	}
	for _, from := range []*types.Package{nil, types.NewPackage("example.com/x", "x")} {
		if _, _, err := plan(mutex, steps, from); err == nil || !strings.Contains(err.Error(), "unexported field") {
			t.Errorf("from %v: err = %v", from, err)
		}
	}
}
