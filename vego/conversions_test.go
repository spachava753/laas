package vego

import (
	"go/ast"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"

	"golang.org/x/tools/go/packages"
)

// TestConversionLists checks the walk over the contexts of assignment,
// which lists the conversions to interface types, against what go/ssa
// records, on every package of the corpus. Every conversion go/ssa makes of
// a value that is not a constant must have an expression the walk lists
// among the expressions of its operand, or none at all, as for one result
// of a call with several, which the verifier refuses. And every expression
// the walk lists that is not a constant must be an expression of a value
// go/ssa converts; go/ssa gives constants no expression.
func TestConversionLists(t *testing.T) {
	testdata, err := filepath.Abs("testdata")
	if err != nil {
		t.Fatal(err)
	}
	config := &packages.Config{
		Mode: packages.LoadAllSyntax,
		Dir:  filepath.Join(testdata, "src"),
		Env:  append(os.Environ(), "GOPATH="+testdata, "GO111MODULE=off", "GOPROXY=off", "GOWORK=off"),
	}
	loaded, err := packages.Load(config, "./...")
	if err != nil {
		t.Fatalf("load packages: %v", err)
	}
	checked := 0
	for _, pkg := range loaded {
		if len(pkg.Errors) > 0 {
			continue
		}
		checked++
		walked := map[ast.Expr]bool{}
		for _, file := range pkg.Syntax {
			for e := range syntacticConversions(pkg.TypesInfo, file) {
				walked[e] = true
			}
		}
		candidate := map[ast.Expr]bool{}
		var problems []string
		for _, conversion := range ssaConversions(pkg.Fset, pkg.Types, pkg.Syntax, pkg.TypesInfo) {
			for _, e := range conversion.candidates {
				candidate[e] = true
			}
			switch {
			case conversion.constant:
			case len(conversion.candidates) == 0:
				// A conversion without an expression of its own is one
				// result of a call with several, a value that a comma-ok
				// form gives, or an element that a range assigns: what
				// go/ssa extracts, or loads from where the range keeps it.
				if !strings.HasPrefix(conversion.what, "extract ") && !strings.HasPrefix(conversion.what, "*") {
					problems = append(problems, pkg.Fset.Position(conversion.at).String()+": go/ssa converts "+conversion.what+
						" here, in the function at "+pkg.Fset.Position(conversion.fn.Pos()).String()+", and it has no expression")
				}
			case !slices.ContainsFunc(conversion.candidates, func(e ast.Expr) bool { return walked[e] }):
				problems = append(problems, pkg.Fset.Position(conversion.at).String()+": go/ssa converts "+conversion.what+
					", and the walk lists none of its expressions")
			}
		}
		for e := range walked {
			if pkg.TypesInfo.Types[e].Value == nil && !candidate[e] {
				problems = append(problems, pkg.Fset.Position(e.Pos()).String()+": the walk lists it, and go/ssa converts no value it is an expression of")
			}
		}
		slices.Sort(problems)
		for _, problem := range problems {
			t.Error(problem)
		}
	}
	if checked < 50 {
		t.Fatalf("only %d packages of the corpus were checked", checked)
	}
}
