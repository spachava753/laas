// Package teststructure requires Go tests to use subtests or table-driven structure.
package teststructure

import (
	"go/ast"
	"go/types"
	"strings"
	"unicode"
	"unicode/utf8"

	"golang.org/x/tools/go/analysis"
)

// Analyzer reports tests that use neither t.Run subtests nor a local table of
// test cases.
var Analyzer = &analysis.Analyzer{
	Name: "teststructure",
	Doc: `requires subtests or table-driven tests

teststructure reports Test functions that neither call Run on their own
*testing.T parameter nor range over a locally initialized slice, array, or map.
Only declarations in test files with the standard Go test signature are
checked.`,
	URL: "https://github.com/spachava753/laas#teststructure",
	Run: run,
}

func run(pass *analysis.Pass) (any, error) {
	for _, file := range pass.Files {
		if !strings.HasSuffix(pass.Fset.Position(file.Pos()).Filename, "_test.go") {
			continue
		}

		for _, declaration := range file.Decls {
			function, ok := declaration.(*ast.FuncDecl)
			if !ok || !isTestFunction(pass, function) {
				continue
			}
			if hasSubtest(pass, function) || hasTable(pass, function) {
				continue
			}

			pass.ReportRangef(
				function.Name,
				"test %s should use t.Run subtests or range over a local table of test cases",
				function.Name.Name,
			)
		}
	}
	return nil, nil
}

func isTestFunction(pass *analysis.Pass, function *ast.FuncDecl) bool {
	// isTestFunction matches Go's naming rule, then verifies the testing.T signature.
	if function.Recv != nil || function.Body == nil || !isTestName(function.Name.Name) {
		return false
	}

	object, ok := pass.TypesInfo.Defs[function.Name].(*types.Func)
	if !ok {
		return false
	}
	signature, ok := object.Type().(*types.Signature)
	if !ok || signature.Params().Len() != 1 || signature.Results().Len() != 0 {
		return false
	}

	parameterType := types.Unalias(signature.Params().At(0).Type())
	pointer, ok := parameterType.(*types.Pointer)
	if !ok {
		return false
	}
	named, ok := types.Unalias(pointer.Elem()).(*types.Named)
	if !ok {
		return false
	}

	packageObject := named.Obj().Pkg()
	return packageObject != nil && packageObject.Path() == "testing" && named.Obj().Name() == "T"
}

func isTestName(name string) bool {
	const prefix = "Test"
	if !strings.HasPrefix(name, prefix) {
		return false
	}
	if len(name) == len(prefix) {
		return true
	}
	firstRune, _ := utf8.DecodeRuneInString(name[len(prefix):])
	return !unicode.IsLower(firstRune)
}

func hasSubtest(pass *analysis.Pass, function *ast.FuncDecl) bool {
	parameterField := function.Type.Params.List[0]
	if len(parameterField.Names) != 1 {
		return false
	}
	parameter := pass.TypesInfo.Defs[parameterField.Names[0]]
	found := false

	ast.Inspect(function.Body, func(node ast.Node) bool {
		if found {
			return false
		}
		if _, ok := node.(*ast.FuncLit); ok {
			return false
		}
		call, ok := node.(*ast.CallExpr)
		if !ok {
			return true
		}
		selector, ok := call.Fun.(*ast.SelectorExpr)
		if !ok || selector.Sel.Name != "Run" {
			return true
		}
		identifier, ok := ast.Unparen(selector.X).(*ast.Ident)
		if !ok {
			return true
		}
		if pass.TypesInfo.Uses[identifier] == parameter {
			found = true
		}
		return !found
	})
	return found
}

func hasTable(pass *analysis.Pass, function *ast.FuncDecl) bool {
	// hasTable records local collection literals, then finds a range over one.
	tables := make(map[types.Object]struct{})
	ast.Inspect(function.Body, func(node ast.Node) bool {
		if _, ok := node.(*ast.FuncLit); ok {
			return false
		}

		switch node := node.(type) {
		case *ast.AssignStmt:
			if len(node.Lhs) != len(node.Rhs) {
				return true
			}
			for index, value := range node.Rhs {
				if !isTableLiteral(pass, value) {
					continue
				}
				identifier, ok := ast.Unparen(node.Lhs[index]).(*ast.Ident)
				if ok {
					recordLocalVariable(pass, tables, identifier)
				}
			}
		case *ast.ValueSpec:
			if len(node.Names) != len(node.Values) {
				return true
			}
			for index, value := range node.Values {
				if isTableLiteral(pass, value) {
					recordLocalVariable(pass, tables, node.Names[index])
				}
			}
		}
		return true
	})

	found := false
	ast.Inspect(function.Body, func(node ast.Node) bool {
		if found {
			return false
		}
		if _, ok := node.(*ast.FuncLit); ok {
			return false
		}
		rangeStatement, ok := node.(*ast.RangeStmt)
		if !ok {
			return true
		}
		if isTableLiteral(pass, rangeStatement.X) {
			found = true
			return false
		}
		identifier, ok := ast.Unparen(rangeStatement.X).(*ast.Ident)
		if !ok {
			return true
		}
		_, found = tables[pass.TypesInfo.Uses[identifier]]
		return !found
	})
	return found
}

func recordLocalVariable(pass *analysis.Pass, tables map[types.Object]struct{}, identifier *ast.Ident) {
	object := pass.TypesInfo.Defs[identifier]
	if object == nil {
		object = pass.TypesInfo.Uses[identifier]
	}
	variable, ok := object.(*types.Var)
	if !ok || variable.Parent() == pass.Pkg.Scope() {
		return
	}
	tables[variable] = struct{}{}
}

func isTableLiteral(pass *analysis.Pass, expression ast.Expr) bool {
	literal, ok := ast.Unparen(expression).(*ast.CompositeLit)
	if !ok {
		return false
	}
	typeOfLiteral := pass.TypesInfo.TypeOf(literal)
	if typeOfLiteral == nil {
		return false
	}

	switch typeOfLiteral.Underlying().(type) {
	case *types.Array, *types.Slice, *types.Map:
		return true
	default:
		return false
	}
}
