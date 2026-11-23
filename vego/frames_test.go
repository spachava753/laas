package vego

import (
	"go/ast"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"path/filepath"
	"strings"
	"testing"

	"github.com/spachava753/laas/vego/internal/logic"
)

// TestFrameEnvComplete holds the keystone of F (frames.go): every
// interface the resolver asks of its environment, by a type assertion or a
// type switch on any value whose static type is logic.Env or an interface
// that embeds it or that it embeds, whatever the value is named, is one
// frameEnv implements, so that no read of a clause goes past the frame
// unpaired. A method added to one of them fails to build; an interface
// asked anywhere in package logic fails here until frameEnv takes a
// position on it.
func TestFrameEnvComplete(t *testing.T) {
	parallel(t)
	var env any = &frameEnv{}
	implemented := map[string]bool{}
	_, implemented["Env"] = env.(logic.Env)
	_, implemented["Applier"] = env.(logic.Applier)
	_, implemented["Gatherer"] = env.(logic.Gatherer)

	names, err := filepath.Glob(filepath.Join("internal", "logic", "*.go"))
	if err != nil {
		t.Fatal(err)
	}
	fset := token.NewFileSet()
	var files []*ast.File
	for _, name := range names {
		if strings.HasSuffix(name, "_test.go") {
			continue
		}
		file, err := parser.ParseFile(fset, name, nil, 0)
		if err != nil {
			t.Fatal(err)
		}
		files = append(files, file)
	}
	info := &types.Info{Types: map[ast.Expr]types.TypeAndValue{}}
	conf := types.Config{Importer: importer.ForCompiler(fset, "source", nil)}
	pkg, err := conf.Check("github.com/spachava753/laas/vego/internal/logic", fset, files, info)
	if err != nil {
		t.Fatal(err)
	}
	envType := pkg.Scope().Lookup("Env").Type()
	envIface := envType.Underlying().(*types.Interface)
	// isEnv reports whether a static type is Env or an interface related
	// to it by embedding, in either direction.
	isEnv := func(x ast.Expr) bool {
		tv, ok := info.Types[x]
		if !ok {
			return false
		}
		iface, ok := tv.Type.Underlying().(*types.Interface)
		// Every type implements the empty interface, so a value of that
		// static type, as recover returns, is not the environment by its
		// type; package logic hands the environment on as Env only, which
		// the last check of the test holds.
		return ok && iface.NumMethods() > 0 && (types.Identical(tv.Type, envType) || types.Implements(iface, envIface) || types.Implements(envType, iface))
	}
	asked := map[string]bool{}
	name := func(x ast.Expr) {
		tv, ok := info.Types[x]
		named, isNamed := tv.Type.(*types.Named)
		if !ok || !isNamed || named.Obj().Pkg() != pkg {
			t.Errorf("%s: the environment is asked for %s, which is no interface of package logic the test can name", fset.Position(x.Pos()), types.ExprString(x))
			return
		}
		asked[named.Obj().Name()] = true
	}
	for _, file := range files {
		ast.Inspect(file, func(n ast.Node) bool {
			switch n := n.(type) {
			case *ast.TypeAssertExpr:
				if n.Type != nil && isEnv(n.X) {
					name(n.Type)
				}
			case *ast.TypeSwitchStmt:
				var x ast.Expr
				switch a := n.Assign.(type) {
				case *ast.ExprStmt:
					x = a.X.(*ast.TypeAssertExpr).X
				case *ast.AssignStmt:
					x = a.Rhs[0].(*ast.TypeAssertExpr).X
				}
				if !isEnv(x) {
					return true
				}
				for _, clause := range n.Body.List {
					for _, typ := range clause.(*ast.CaseClause).List {
						if ident, ok := typ.(*ast.Ident); ok && ident.Name == "nil" {
							continue
						}
						name(typ)
					}
				}
			}
			return true
		})
	}
	if len(asked) == 0 {
		t.Fatal("found no assertion on the environment in package logic; the scan is broken")
	}
	// The environment is never converted to the empty interface, where an
	// assertion on it would escape the scan.
	for x, tv := range info.Types {
		if iface, ok := tv.Type.Underlying().(*types.Interface); ok && iface.NumMethods() == 0 {
			if conv, ok := x.(*ast.CallExpr); ok && len(conv.Args) == 1 && isEnv(conv.Args[0]) {
				t.Errorf("%s: the environment is converted to an empty interface, which the scan cannot follow", fset.Position(x.Pos()))
			}
		}
	}
	for name := range asked {
		if !implemented[name] {
			t.Errorf("the resolver asks its environment for logic.%s, on which frameEnv takes no position: implement it in frames.go, pairing every result, and add it here", name)
		}
	}
}
