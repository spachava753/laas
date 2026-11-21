package vego

import (
	"go/ast"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"strings"
	"testing"

	"golang.org/x/tools/go/analysis"
)

// TestReachingPositions checks how a use is placed in the control-flow
// graph: a use in a body's own code gets the definitions that reach it, a
// use in code the graph finds unreachable falls back to every assignment,
// and a position that no node holds is a fault that panics instead of
// turning the analysis off without a word.
func TestReachingPositions(t *testing.T) {
	parallel(t)
	const src = `package p

import "errors"

func f(c bool) (err error) {
	err = errors.New("a")
	if c {
		err = errors.New("b")
	}
	_ = err
	return err
	_ = err
	return nil
}
`
	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "p.go", src, 0)
	if err != nil {
		t.Fatal(err)
	}
	info := &types.Info{Defs: map[*ast.Ident]types.Object{}, Uses: map[*ast.Ident]types.Object{}, Types: map[ast.Expr]types.TypeAndValue{}, Implicits: map[ast.Node]types.Object{}}
	if _, err := (&types.Config{Importer: importer.Default()}).Check("p", fset, []*ast.File{file}, info); err != nil {
		t.Fatal(err)
	}
	decl := file.Decls[1].(*ast.FuncDecl)
	pv := &pkgVerifier{info: info, pass: &analysis.Pass{Fset: fset}, origins: map[*ast.BlockStmt]*origins{}}
	o := pv.originsOf(decl.Body)
	result := info.Defs[decl.Type.Results.List[0].Names[0]].(*types.Var)
	if !o.tracked(result) {
		t.Fatal("err is not tracked")
	}
	// The uses of err in "_ = err": the live one and the dead one.
	var uses []token.Pos
	ast.Inspect(decl.Body, func(n ast.Node) bool {
		if assign, ok := n.(*ast.AssignStmt); ok {
			if id, ok := assign.Rhs[0].(*ast.Ident); ok && id.Name == "err" {
				uses = append(uses, id.Pos())
			}
		}
		return true
	})
	if len(uses) != 2 {
		t.Fatalf("found %d uses", len(uses))
	}
	if defs, ok := pv.reaching(o, result, uses[0]); !ok || len(defs) != 2 {
		t.Errorf("at the live use: %d definitions, ok %v; want both assignments", len(defs), ok)
	}
	if _, ok := pv.reaching(o, result, uses[1]); ok {
		t.Error("the use after the return is placed in a live block")
	}
	defer func() {
		r := recover()
		if msg, _ := r.(string); !strings.Contains(msg, "no node of the control-flow graph holds the use of err") {
			t.Errorf("a position outside every node gave %v", r)
		}
	}()
	pv.reaching(o, result, decl.Name.Pos())
}
