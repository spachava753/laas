package vego

import (
	"go/ast"
	"go/parser"
	"go/token"
	"path/filepath"
	"strings"
	"testing"

	"github.com/spachava753/laas/vego/internal/logic"
)

// TestFrameEnvComplete holds the keystone of F (frames.go): every
// interface the resolver asks of its environment by a type assertion or a
// type switch is one frameEnv implements, so that no read of a clause goes
// past the frame unpaired. A method added to one of them fails to build;
// an interface added to the resolver fails here until frameEnv takes a
// position on it.
func TestFrameEnvComplete(t *testing.T) {
	parallel(t)
	var env any = &frameEnv{}
	implemented := map[string]bool{}
	_, implemented["Env"] = env.(logic.Env)
	_, implemented["Applier"] = env.(logic.Applier)
	_, implemented["Gatherer"] = env.(logic.Gatherer)
	files, err := filepath.Glob(filepath.Join("internal", "logic", "*.go"))
	if err != nil {
		t.Fatal(err)
	}
	asked := map[string]bool{}
	fset := token.NewFileSet()
	for _, name := range files {
		if strings.HasSuffix(name, "_test.go") {
			continue
		}
		file, err := parser.ParseFile(fset, name, nil, 0)
		if err != nil {
			t.Fatal(err)
		}
		ast.Inspect(file, func(n ast.Node) bool {
			assert, ok := n.(*ast.TypeAssertExpr)
			if !ok || !mentionsEnv(assert.X) {
				return true
			}
			if assert.Type == nil {
				// A type switch: every case names a type asked of the env.
				return true
			}
			if ident, ok := assert.Type.(*ast.Ident); ok {
				asked[ident.Name] = true
			} else {
				t.Errorf("%s: the environment is asserted to %T, which the test cannot name", fset.Position(assert.Pos()), assert.Type)
			}
			return true
		})
		ast.Inspect(file, func(n ast.Node) bool {
			sw, ok := n.(*ast.TypeSwitchStmt)
			if !ok {
				return true
			}
			var x ast.Expr
			switch a := sw.Assign.(type) {
			case *ast.ExprStmt:
				x = a.X.(*ast.TypeAssertExpr).X
			case *ast.AssignStmt:
				x = a.Rhs[0].(*ast.TypeAssertExpr).X
			}
			if !mentionsEnv(x) {
				return true
			}
			for _, clause := range sw.Body.List {
				for _, typ := range clause.(*ast.CaseClause).List {
					if ident, ok := typ.(*ast.Ident); ok {
						asked[ident.Name] = true
					} else {
						t.Errorf("%s: a case of a switch on the environment names %T, which the test cannot name", fset.Position(typ.Pos()), typ)
					}
				}
			}
			return true
		})
	}
	if len(asked) == 0 {
		t.Fatal("found no assertion on the environment in package logic; the scan is broken")
	}
	for name := range asked {
		if !implemented[name] {
			t.Errorf("the resolver asks its environment for logic.%s, on which frameEnv takes no position: implement it in frames.go, pairing every result, and add it here", name)
		}
	}
}

// mentionsEnv reports whether an expression is the resolver's environment,
// as env or s.env.
func mentionsEnv(x ast.Expr) bool {
	switch x := x.(type) {
	case *ast.Ident:
		return x.Name == "env"
	case *ast.SelectorExpr:
		return x.Sel.Name == "env"
	}
	return false
}
