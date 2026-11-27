package vego

import (
	"go/ast"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"path/filepath"
	"slices"
	"strings"
	"testing"
)

// classifiers are the functions whose result a place that refuses may hand
// unsupported as its class, besides a constant and withDetail of one.
var classifiers = map[string]bool{
	"typeClass": true, "elemClass": true, "mapClass": true, "stmtClass": true, "rangeClass": true,
	"addressClass": true, "callClass": true, "varClass": true, "funcValueClass": true,
}

// TestRefusalClasses holds every place in the verifier that refuses to a
// class: each call of unsupported and each unsupported value names a class
// of the table, withDetail of one, or the result of a classifier; every
// class of the table is used and described.
func TestRefusalClasses(t *testing.T) {
	parallel(t)
	fset := token.NewFileSet()
	files, err := filepath.Glob("*.go")
	if err != nil {
		t.Fatal(err)
	}
	declared := map[string]bool{}
	described := map[string]bool{}
	used := map[string]bool{}
	sites, reports := 0, 0
	var parsed []*ast.File
	for _, name := range files {
		if strings.HasSuffix(name, "_test.go") {
			continue
		}
		file, err := parser.ParseFile(fset, name, nil, 0)
		if err != nil {
			t.Fatal(err)
		}
		parsed = append(parsed, file)
		for _, decl := range file.Decls {
			gen, ok := decl.(*ast.GenDecl)
			if !ok {
				continue
			}
			for _, spec := range gen.Specs {
				value, ok := spec.(*ast.ValueSpec)
				if !ok {
					continue
				}
				if id, ok := value.Type.(*ast.Ident); ok && id.Name == "refusal" && gen.Tok == token.CONST {
					for _, n := range value.Names {
						declared[n.Name] = true
					}
				}
				if len(value.Names) == 1 && value.Names[0].Name == "refusalClasses" {
					for _, elt := range value.Values[0].(*ast.CompositeLit).Elts {
						kv := elt.(*ast.KeyValueExpr)
						text := kv.Value.(*ast.BasicLit).Value
						// A class says in parentheses where the roadmap
						// plans what lifts it.
						if len(text) < 12 || !strings.Contains(text, "not a cause") && !strings.Contains(text, "(") {
							t.Errorf("%s: the class %s has no description that names where the roadmap plans it", fset.Position(kv.Pos()), kv.Key.(*ast.Ident).Name)
						}
						described[kv.Key.(*ast.Ident).Name] = true
					}
				}
			}
		}
	}
	// check reports a class argument that is none of the accepted forms.
	var check func(e ast.Expr, at token.Pos)
	check = func(e ast.Expr, at token.Pos) {
		switch e := e.(type) {
		case *ast.Ident:
			if e.Name == "class" {
				// A function that refuses on behalf of its caller, which
				// names the class.
				return
			}
			if !declared[e.Name] {
				t.Errorf("%s: %s is not a class of the table", fset.Position(at), e.Name)
			}
			used[e.Name] = true
			return
		case *ast.SelectorExpr:
			if e.Sel.Name == "class" {
				// A refusal passed on from where it was made.
				return
			}
		case *ast.CallExpr:
			name := ""
			switch fun := e.Fun.(type) {
			case *ast.Ident:
				name = fun.Name
			case *ast.SelectorExpr:
				name = fun.Sel.Name
			}
			if name == "withDetail" {
				check(e.Args[0], at)
				return
			}
			if classifiers[name] {
				return
			}
		}
		t.Errorf("%s: the class of this refusal is %s, which is neither a class of the table nor a classifier's result",
			fset.Position(at), types.ExprString(e))
	}
	for _, file := range parsed {
		ast.Inspect(file, func(n ast.Node) bool {
			switch n := n.(type) {
			case *ast.CallExpr:
				if sel, ok := n.Fun.(*ast.SelectorExpr); ok && sel.Sel.Name == "unsupported" {
					sites++
					if len(n.Args) != 3 {
						t.Errorf("%s: unsupported takes a position, a class, and a message", fset.Position(n.Pos()))
						return true
					}
					check(n.Args[1], n.Pos())
				}
				// Every report says what it is: an obligation, a fault of an
				// annotation, or a refusal with its class.
				name := ""
				switch fun := n.Fun.(type) {
				case *ast.SelectorExpr:
					name = fun.Sel.Name
				case *ast.Ident:
					name = fun.Name
				}
				if name == "report" {
					reports++
					if len(n.Args) < 3 {
						t.Errorf("%s: report takes a position, a class, and a message", fset.Position(n.Pos()))
						return true
					}
					check(n.Args[1], n.Pos())
				}
			case *ast.CompositeLit:
				if id, ok := n.Type.(*ast.Ident); ok && id.Name == "unsupported" {
					found := false
					for i, elt := range n.Elts {
						if kv, ok := elt.(*ast.KeyValueExpr); ok && kv.Key.(*ast.Ident).Name == "class" {
							check(kv.Value, n.Pos())
							found = true
						} else if id, isID := elt.(*ast.Ident); !ok && i == 2 && isID && id.Name == "class" {
							// unsupported itself, which passes its class on.
							found = true
						} else if !ok && i == 2 {
							check(elt, n.Pos())
							found = true
						}
					}
					if !found {
						t.Errorf("%s: an unsupported value without a class", fset.Position(n.Pos()))
					}
				}
			case *ast.FuncDecl:
				// What the classifiers return counts as used.
				if (classifiers[n.Name.Name] || n.Name.Name == "typeClassOf") && n.Body != nil {
					ast.Inspect(n.Body, func(m ast.Node) bool {
						if id, ok := m.(*ast.Ident); ok && declared[id.Name] {
							used[id.Name] = true
						}
						return true
					})
				}
			}
			return true
		})
	}
	if sites < 250 || reports < 170 {
		t.Fatalf("only %d places that refuse and %d that report were found", sites, reports)
	}
	for name := range declared {
		if !described[name] {
			t.Errorf("the class %s is not in refusalClasses", name)
		}
		if !used[name] {
			t.Errorf("the class %s is used by no place that refuses", name)
		}
	}
	for class := range proofClasses {
		if !strings.HasSuffix(refusalClasses[class], "made only when a proof fails") {
			t.Errorf("the class %s is made only when a proof fails, and its description does not say so", class)
		}
	}
	for class, text := range refusalClasses {
		if strings.HasSuffix(text, "made only when a proof fails") && !proofClasses[class] {
			t.Errorf("the class %s says it is made only when a proof fails, and is not among proofClasses", class)
		}
	}
	if len(refusalClasses) != len(declared) {
		t.Errorf("refusalClasses has %d entries for %d classes", len(refusalClasses), len(declared))
	}
	seen := map[string]bool{}
	for class := range refusalClasses {
		if strings.Contains(string(class), "|") || !strings.Contains(string(class), ":") || seen[string(class)] {
			t.Errorf("the class %q is not of the form group:kind, or is there twice", class)
		}
		seen[string(class)] = true
	}
}

// TestLayoutClasses checks typeClass on a type of every kind layoutOf has no
// layout for, and that it never falls through to type:other for a type
// built of what Go source can name.
func TestLayoutClasses(t *testing.T) {
	parallel(t)
	const src = `package p

import "unsafe"

type S struct{ a [4]int32 }
type E interface{ error; M() }
type G[T any] struct{ x T }

var (
	pUintptr uintptr
	pComplex complex128
	pUnsafe unsafe.Pointer
	pChan chan int
	pPtrSlice *[]int
	pPtrMap *map[string]int
	pPtrPtr **S
	pPtrArray *[4]int
	pPtrIface *error
	pPtrFunc *func()
	pArrayStrings [3]string
	pArrayStruct S
	pPtrArrayStruct *S
	pMapKey map[*S]int
	pMapStruct map[struct{ x int }]bool
	pIface interface{ E }
	pErrorIface E
	pMapFloat map[float64]int
	pMapArray map[[2]int]int
	pMapIface map[any]int
	pArrayPointers [2]*S
	pArrayArrays [2][2]int
	pArrayStructs [2]struct{ x int }
	pArrayIfaces [2]any
	pBigStruct struct{ big [64]uint64 }
)

func Generic[T any](x T, p *T) {}
`
	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "p.go", src, 0)
	if err != nil {
		t.Fatal(err)
	}
	pkg, err := (&types.Config{Importer: importer.Default()}).Check("p", fset, []*ast.File{file}, nil)
	if err != nil {
		t.Fatal(err)
	}
	want := map[string]refusal{
		"pUintptr": rTypeUintptr, "pComplex": rTypeComplex, "pUnsafe": rTypeUnsafe, "pChan": rChannel,
		"pPtrSlice": rPointerTo, "pPtrMap": rPointerTo, "pPtrPtr": rPointerTo, "pPtrArray": rPointerTo, "pPtrIface": rPointerTo, "pPtrFunc": rPointerTo,
		"pArrayStrings": rTypeArray, "pArrayStruct": rTypeArrayStruct, "pPtrArrayStruct": rTypeArrayStruct,
		"pMapKey": rTypeMapKey, "pMapStruct": rTypeMapKey, "pIface": rTypeIface, "pErrorIface": rTypeIface,
		"pMapFloat": rTypeMapKey, "pMapArray": rTypeMapKey, "pMapIface": rTypeMapKey,
		"pArrayPointers": rTypeArray, "pArrayArrays": rTypeArray, "pArrayStructs": rTypeArray, "pArrayIfaces": rTypeArray,
		"pBigStruct": rTypeArrayStruct,
	}
	for name, class := range want {
		typ := pkg.Scope().Lookup(name).Type()
		if _, ok := layoutOf(typ); ok {
			t.Errorf("%s: %s has a layout", name, typ)
			continue
		}
		if got := typeClass(typ); got != withDetail(class, typ.String()) {
			t.Errorf("%s: typeClass(%s) = %q, want %s with the type as detail", name, typ, got, class)
		}
	}
	generic := pkg.Scope().Lookup("Generic").Type().(*types.Signature)
	for param := range generic.Params().Variables() {
		if got := typeClass(param.Type()).class(); got != string(rGenericTypeParam) {
			t.Errorf("typeClass(%s) = %s, want %s", param.Type(), got, rGenericTypeParam)
		}
	}
	if got := elemClass(pkg.Scope().Lookup("pArrayStrings").Type()).class(); got != string(rTypeArrayElem) {
		t.Errorf("elemClass of an array = %s, want %s", got, rTypeArrayElem)
	}
	// Every type of the standard library's unsafe-free packages that has no
	// layout gets a class other than type:other.
	checked := 0
	for _, path := range []string{"net/http", "os", "sync", "reflect", "go/types", "encoding/json", "time"} {
		lib, err := importer.Default().Import(path)
		if err != nil {
			t.Fatal(err)
		}
		for _, name := range lib.Scope().Names() {
			obj := lib.Scope().Lookup(name)
			var types_ []types.Type
			types_ = append(types_, obj.Type())
			if named, ok := obj.Type().(*types.Named); ok {
				if s, ok := named.Underlying().(*types.Struct); ok {
					for field := range s.Fields() {
						types_ = append(types_, field.Type())
					}
				}
			}
			for _, typ := range types_ {
				if _, ok := layoutOf(typ); ok {
					continue
				}
				checked++
				if typeClass(typ).class() == string(rTypeOther) {
					if _, isTuple := typ.(*types.Tuple); !isTuple && !slices.Contains([]string{"invalid type"}, typ.String()) {
						t.Errorf("%s.%s: typeClass(%s) is %s", path, name, typ, rTypeOther)
					}
				}
			}
		}
	}
	if checked < 50 {
		t.Errorf("only %d types without a layout were met", checked)
	}
}
