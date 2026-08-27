// Package inlinehelper finds small helpers with only one call site.
package inlinehelper

import (
	"go/ast"
	"go/types"

	"golang.org/x/tools/go/analysis"
)

const defaultMaxStatements = 4

// Analyzer reports small unexported functions and methods that have exactly one
// reference and are called directly at that reference.
var Analyzer = newAnalyzer()

type candidate struct {
	declaration *ast.FuncDecl
	statements  int
	references  int
	calls       int
	recursive   bool
}

func newAnalyzer() *analysis.Analyzer {
	maxStatements := defaultMaxStatements
	analyzer := &analysis.Analyzer{
		Name: "inlinehelper",
		Doc: `finds small helpers with only one call site

inlinehelper reports unexported functions and methods that contain at most the
configured number of statements and have exactly one direct call in the current
package. The diagnostic is advisory because a small helper may still provide a
useful abstraction.`,
		URL: "https://github.com/spachava753/laas#inlinehelper",
	}
	analyzer.Flags.IntVar(
		&maxStatements,
		"max-statements",
		defaultMaxStatements,
		"maximum number of statements in a helper considered small",
	)
	analyzer.Run = func(pass *analysis.Pass) (any, error) {
		return run(pass, maxStatements)
	}
	return analyzer
}

// run collects small declarations, counts their references and calls, then
// reports single-use helpers.
func run(pass *analysis.Pass, maxStatements int) (any, error) {
	candidatesByObject := make(map[types.Object]*candidate)
	var candidates []*candidate
	for _, file := range pass.Files {
		for _, declaration := range file.Decls {
			function, ok := declaration.(*ast.FuncDecl)
			if !ok || function.Body == nil || ast.IsExported(function.Name.Name) {
				continue
			}

			statements := statementCount(function.Body)
			if statements > maxStatements {
				continue
			}
			object, ok := pass.TypesInfo.Defs[function.Name].(*types.Func)
			if !ok {
				continue
			}

			item := &candidate{
				declaration: function,
				statements:  statements,
			}
			candidates = append(candidates, item)
			candidatesByObject[object] = item
		}
	}

	for _, object := range pass.TypesInfo.Uses {
		if item := candidatesByObject[object]; item != nil {
			item.references++
		}
	}

	for _, file := range pass.Files {
		ast.Inspect(file, func(node ast.Node) bool {
			call, ok := node.(*ast.CallExpr)
			if !ok {
				return true
			}
			item := candidatesByObject[calledObject(pass, call.Fun)]
			if item == nil {
				return true
			}
			item.calls++
			if item.declaration.Pos() <= call.Pos() && call.Pos() < item.declaration.End() {
				item.recursive = true
			}
			return true
		})
	}

	for _, item := range candidates {
		if item.references != 1 || item.calls != 1 || item.recursive {
			continue
		}
		kind := "function"
		if item.declaration.Recv != nil {
			kind = "method"
		}
		statementLabel := "statements"
		if item.statements == 1 {
			statementLabel = "statement"
		}
		pass.ReportRangef(
			item.declaration.Name,
			"%s %s has %d %s and is called once; consider inlining it at its call site",
			kind,
			item.declaration.Name.Name,
			item.statements,
			statementLabel,
		)
	}
	return nil, nil
}

func statementCount(body *ast.BlockStmt) int {
	count := 0
	ast.Inspect(body, func(node ast.Node) bool {
		statement, ok := node.(ast.Stmt)
		if !ok {
			return true
		}
		switch statement.(type) {
		case *ast.BlockStmt, *ast.EmptyStmt:
			return true
		default:
			count++
			return true
		}
	})
	return count
}

func calledObject(pass *analysis.Pass, expression ast.Expr) types.Object {
	switch expression := ast.Unparen(expression).(type) {
	case *ast.Ident:
		return pass.TypesInfo.Uses[expression]
	case *ast.SelectorExpr:
		if selection := pass.TypesInfo.Selections[expression]; selection != nil {
			return selection.Obj()
		}
		return pass.TypesInfo.Uses[expression.Sel]
	case *ast.IndexExpr:
		return calledObject(pass, expression.X)
	case *ast.IndexListExpr:
		return calledObject(pass, expression.X)
	default:
		return nil
	}
}
