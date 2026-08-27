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
// the configured limit unless the declaration has a doc comment whose first
// word matches its name.
var Analyzer = newAnalyzer()

func newAnalyzer() *analysis.Analyzer {
	limit := defaultLimit
	includeTests := false
	analyzer := &analysis.Analyzer{
		Name: "funcdoc",
		Doc: `reports complex functions without implementation overviews

funcdoc requires a doc comment immediately above each function or method whose
cyclomatic complexity exceeds the configured limit. The comment must start with
the function or method name and give the reader a mental model of the
implementation before they read its logic. Test files are excluded unless
include-tests is enabled.`,
		URL: "https://github.com/spachava753/laas#funcdoc",
	}
	analyzer.Flags.BoolVar(
		&includeTests,
		"include-tests",
		false,
		"include functions and methods declared in test files",
	)
	analyzer.Flags.IntVar(
		&limit,
		"limit",
		defaultLimit,
		"maximum cyclomatic complexity allowed without a doc comment",
	)
	analyzer.Run = func(pass *analysis.Pass) (any, error) {
		return run(pass, limit, includeTests)
	}
	return analyzer
}

// run skips excluded test files, scores each function, then validates its doc
// comment.
func run(pass *analysis.Pass, limit int, includeTests bool) (any, error) {
	for _, file := range pass.Files {
		if !includeTests && strings.HasSuffix(pass.Fset.Position(file.Pos()).Filename, "_test.go") {
			continue
		}

		for _, declaration := range file.Decls {
			function, ok := declaration.(*ast.FuncDecl)
			if !ok || function.Body == nil {
				continue
			}

			complexity := gocyclo.Complexity(function)
			if complexity <= limit {
				continue
			}

			kind := "function"
			if function.Recv != nil {
				kind = "method"
			}

			var words []string
			if function.Doc != nil {
				words = strings.Fields(function.Doc.Text())
			}
			if len(words) == 0 {
				pass.ReportRangef(
					function.Name,
					"%s %s has cyclomatic complexity %d (limit %d); add a doc comment immediately above it starting with %q that explains its logic",
					kind,
					function.Name.Name,
					complexity,
					limit,
					function.Name.Name,
				)
				continue
			}

			if words[0] != function.Name.Name {
				pass.ReportRangef(
					function.Doc,
					"%s %s has cyclomatic complexity %d (limit %d); its doc comment should start with %q",
					kind,
					function.Name.Name,
					complexity,
					limit,
					function.Name.Name,
				)
			}
		}
	}
	return nil, nil
}
