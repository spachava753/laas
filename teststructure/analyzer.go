// Package teststructure enforces focused, locally readable Go test structure.
package teststructure

import (
	"go/ast"
	"go/types"
	"sort"
	"strings"
	"unicode"
	"unicode/utf8"

	"golang.org/x/tools/go/analysis"
)

// Analyzer reports groups of tests whose names share an identifier-word prefix
// and testing.T.Run calls whose callback is not an inline function literal.
var Analyzer = &analysis.Analyzer{
	Name: "teststructure",
	Doc: `enforces focused, locally readable Go tests

teststructure groups standard Test functions by shared name prefixes at Go
identifier-word boundaries. Multiple tests in a group should become one outer
test using either a table of cases or t.Run subtests. Calls to testing.T.Run
must define their callback as an inline function literal so each subtest's logic
remains next to its name.`,
	URL: "https://github.com/spachava753/laas#teststructure",
	Run: run,
}

type testDeclaration struct {
	function *ast.FuncDecl
	words    []string
}

// run checks subtest callbacks and groups test declarations by name prefix.
func run(pass *analysis.Pass) (any, error) {
	var tests []testDeclaration
	for _, file := range pass.Files {
		if !strings.HasSuffix(pass.Fset.Position(file.Pos()).Filename, "_test.go") {
			continue
		}
		reportDelegatedSubtests(pass, file)

		for _, declaration := range file.Decls {
			function, ok := declaration.(*ast.FuncDecl)
			if !ok || !isTestFunction(pass, function) {
				continue
			}
			tests = append(tests, testDeclaration{
				function: function,
				words:    identifierWords(function.Name.Name),
			})
		}
	}

	groups := prefixGroups(tests)
	prefixes := make([]string, 0, len(groups))
	for prefix, group := range groups {
		if len(group) >= 2 {
			prefixes = append(prefixes, prefix)
		}
	}
	sort.Strings(prefixes)

	for _, prefix := range prefixes {
		group := groups[prefix]
		pass.ReportRangef(
			group[0].function.Name,
			"tests %s share prefix %s; consolidate scenarios into one test using a table or t.Run subtests",
			testNames(group),
			prefix,
		)
	}
	return nil, nil
}

// reportDelegatedSubtests keeps each subtest's implementation next to its name.
func reportDelegatedSubtests(pass *analysis.Pass, file *ast.File) {
	ast.Inspect(file, func(node ast.Node) bool {
		call, ok := node.(*ast.CallExpr)
		if !ok || len(call.Args) == 0 {
			return true
		}
		selector, ok := ast.Unparen(call.Fun).(*ast.SelectorExpr)
		if !ok || !isTestingTRun(pass, selector) {
			return true
		}

		callback := call.Args[len(call.Args)-1]
		if _, ok := ast.Unparen(callback).(*ast.FuncLit); ok {
			return true
		}
		pass.ReportRangef(
			callback,
			"testing.T.Run callback must be an inline function literal; move the subtest body into the Run call",
		)
		return true
	})
}

func isTestingTRun(pass *analysis.Pass, selector *ast.SelectorExpr) bool {
	selection := pass.TypesInfo.Selections[selector]
	if selection == nil {
		return false
	}
	method, ok := selection.Obj().(*types.Func)
	if !ok || method.Name() != "Run" {
		return false
	}
	signature, ok := method.Type().(*types.Signature)
	if !ok || signature.Recv() == nil {
		return false
	}
	return isTestingT(signature.Recv().Type())
}

// isTestFunction matches Go's naming rule, then verifies the testing.T
// signature.
func isTestFunction(pass *analysis.Pass, function *ast.FuncDecl) bool {
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

	return isTestingT(signature.Params().At(0).Type())
}

func isTestingT(value types.Type) bool {
	pointer, ok := types.Unalias(value).(*types.Pointer)
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

func identifierWords(name string) []string {
	var words []string
	var word []rune
	runes := []rune(strings.TrimPrefix(name, "Test"))
	for index, current := range runes {
		if current == '_' {
			if len(word) > 0 {
				words = append(words, string(word))
				word = nil
			}
			continue
		}
		if startsNewWord(runes, index) {
			words = append(words, string(word))
			word = nil
		}
		word = append(word, current)
	}
	if len(word) > 0 {
		words = append(words, string(word))
	}
	return words
}

func startsNewWord(runes []rune, index int) bool {
	if index == 0 {
		return false
	}
	current := runes[index]
	previous := runes[index-1]
	if unicode.IsDigit(current) != unicode.IsDigit(previous) {
		return true
	}
	if unicode.IsUpper(current) && (unicode.IsLower(previous) || unicode.IsDigit(previous)) {
		return true
	}
	return unicode.IsUpper(current) &&
		unicode.IsUpper(previous) &&
		index+1 < len(runes) &&
		unicode.IsLower(runes[index+1])
}

func prefixGroups(tests []testDeclaration) map[string][]testDeclaration {
	bestPrefixLengths := make([]int, len(tests))
	for index := range tests {
		for otherIndex := range tests {
			if index == otherIndex {
				continue
			}
			length := commonPrefixLength(tests[index].words, tests[otherIndex].words)
			if length > bestPrefixLengths[index] {
				bestPrefixLengths[index] = length
			}
		}
	}

	groups := make(map[string][]testDeclaration)
	for index, length := range bestPrefixLengths {
		if length == 0 {
			continue
		}
		prefix := "Test" + strings.Join(tests[index].words[:length], "")
		groups[prefix] = append(groups[prefix], tests[index])
	}
	return groups
}

func commonPrefixLength(left, right []string) int {
	length := min(len(left), len(right))
	for index := range length {
		if left[index] != right[index] {
			return index
		}
	}
	return length
}

func testNames(tests []testDeclaration) string {
	names := make([]string, len(tests))
	for index, test := range tests {
		names[index] = test.function.Name.Name
	}
	if len(names) == 2 {
		return names[0] + " and " + names[1]
	}
	return strings.Join(names[:len(names)-1], ", ") + ", and " + names[len(names)-1]
}
