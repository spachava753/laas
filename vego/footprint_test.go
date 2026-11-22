package vego

import (
	"go/importer"
	"go/token"
	"go/types"
	"testing"
)

// TestOwnsDeclarations holds every owns declaration of the shipped files
// against the types of the toolchain: the type is a struct, each field it
// names exists and can be owned, and the type declares a state or has a
// field that is not exported, so that no struct of another package is
// identical to it. A project file cannot declare what a type owns.
func TestOwnsDeclarations(t *testing.T) {
	parallel(t)
	project := parseTrustFile("vego-trusted.yaml", []byte("version: 1\nowns:\n  example.com/x.T:\n    fields: [buf]\n    reason: r\n"), false)
	if len(project.problems) != 1 || len(project.owns) != 0 {
		t.Errorf("a project file that declares owns: problems = %+v, owns = %+v", project.problems, project.owns)
	}
	unreasoned := parseTrustFile("vego/trusted/std/x.yaml", []byte("version: 1\nowns:\n  bytes.Buffer:\n    fields: [buf]\n"), true)
	if len(unreasoned.problems) != 1 || len(unreasoned.owns) != 0 {
		t.Errorf("an owns declaration without a reason: problems = %+v, owns = %+v", unreasoned.problems, unreasoned.owns)
	}
	imports := importer.ForCompiler(token.NewFileSet(), "source", nil)
	declared := 0
	for _, file := range shippedContracts() {
		for _, decl := range file.owns {
			declared++
			pkg, err := imports.Import(decl.pkg)
			if err != nil {
				t.Fatalf("import %s: %v", decl.pkg, err)
			}
			obj, ok := pkg.Scope().Lookup(decl.typ).(*types.TypeName)
			if !ok {
				t.Errorf("%s.%s: no such type", decl.pkg, decl.typ)
				continue
			}
			u, isStruct := obj.Type().Underlying().(*types.Struct)
			if !isStruct {
				t.Errorf("%s.%s is not a struct type", decl.pkg, decl.typ)
				continue
			}
			for _, name := range decl.fields {
				found := false
				for field := range u.Fields() {
					if field.Name() == name {
						found = true
						_, isPointer := pointee(field.Type())
						if !isPointer && !isSlice(field.Type()) && !isMap(field.Type()) && !isIface(field.Type()) {
							t.Errorf("%s.%s owns %s, of type %s, which holds nothing that can be owned", decl.pkg, decl.typ, name, field.Type())
						}
						if field.Exported() {
							t.Errorf("%s.%s owns %s, which is exported, so code of other packages may write it", decl.pkg, decl.typ, name)
						}
					}
				}
				if !found {
					t.Errorf("%s.%s has no field %s", decl.pkg, decl.typ, name)
				}
			}
			if t.Failed() {
				continue
			}
			if got := ownedFieldsOf(obj.Type()); len(got) != len(decl.fields) {
				t.Errorf("%s.%s owns %d fields, and ownedFields finds %d", decl.pkg, decl.typ, len(decl.fields), len(got))
			}
		}
	}
	if declared != 6 {
		t.Errorf("the shipped files declare what %d types own; this test was written for 6, so read the new ones against the source of their package and change the count", declared)
	}
}
