// Package funcdoc reports complex functions that lack an implementation overview.
package funcdoc

import (
	"go/ast"
	"strings"

	"github.com/fzipp/gocyclo"
	"golang.org/x/tools/go/analysis"
)

const defaultLimit = 10

// Analyzer reports functions and methods whose cyclomatic complexity exceeds
// the configured limit and whose body does not begin with a substantive
// comment.
var Analyzer = newAnalyzer()

func newAnalyzer() *analysis.Analyzer {
	limit := defaultLimit
	analyzer := &analysis.Analyzer{
		Name: "funcdoc",
		Doc: `reports complex functions without implementation overviews

funcdoc requires a leading comment in the body of each function or method whose
cyclomatic complexity exceeds the configured limit. The comment should give the
reader a mental model of the implementation before they read its logic.`,
		URL: "https://github.com/spachava753/laas#funcdoc",
	}
	analyzer.Flags.IntVar(
		&limit,
		"limit",
		defaultLimit,
		"maximum cyclomatic complexity allowed without an overview comment",
	)
	analyzer.Run = func(pass *analysis.Pass) (any, error) {
		return run(pass, limit)
	}
	return analyzer
}

func run(pass *analysis.Pass, limit int) (any, error) {
	for _, file := range pass.Files {
		for _, declaration := range file.Decls {
			function, ok := declaration.(*ast.FuncDecl)
			if !ok || function.Body == nil {
				continue
			}

			complexity := gocyclo.Complexity(function)
			if complexity <= limit || hasOverviewComment(file, function.Body) {
				continue
			}

			kind := "function"
			if function.Recv != nil {
				kind = "method"
			}
			pass.ReportRangef(
				function.Name,
				"%s %s has cyclomatic complexity %d (limit %d); add a leading comment explaining its logic",
				kind,
				function.Name.Name,
				complexity,
				limit,
			)
		}
	}
	return nil, nil
}

func hasOverviewComment(file *ast.File, body *ast.BlockStmt) bool {
	firstStatement := body.Rbrace
	if len(body.List) > 0 {
		firstStatement = body.List[0].Pos()
	}

	for _, group := range file.Comments {
		if group.Pos() <= body.Lbrace || group.End() > firstStatement {
			continue
		}
		if strings.TrimSpace(group.Text()) != "" {
			return true
		}
	}
	return false
}
