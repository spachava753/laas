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

// TestConversionLists checks the two lists of conversions to interface
// types against each other on every package of the corpus: what go/ssa
// records and what the walk over the contexts of assignment finds. Every
// conversion go/ssa places must be found by the walk, and every one the
// walk finds of a value that is not a constant must be placed by go/ssa,
// which gives constants no expression. A conversion go/ssa cannot place
// must be of something the walk does not list either, such as one result
// of a call with several; the verifier refuses a function that has one.
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
		placed, unplaced := ssaConversions(pkg.Fset, pkg.Types, pkg.Syntax, pkg.TypesInfo)
		walked := map[ast.Expr]bool{}
		for _, file := range pkg.Syntax {
			for e := range syntacticConversions(pkg.TypesInfo, file) {
				walked[e] = true
			}
		}
		var problems []string
		for e := range placed {
			if !walked[e] {
				problems = append(problems, pkg.Fset.Position(e.Pos()).String()+": go/ssa converts it, and the walk does not list it")
			}
		}
		for e := range walked {
			if pkg.TypesInfo.Types[e].Value == nil && !placed[e] {
				problems = append(problems, pkg.Fset.Position(e.Pos()).String()+": the walk lists it, and go/ssa does not place a conversion of it")
			}
		}
		// A conversion without an expression of its own is one result of a
		// call with several, a value that a comma-ok form gives, or an
		// element that a range assigns: what go/ssa extracts, or loads
		// from where the range keeps it. Anything else would be a gap.
		for _, conversion := range unplaced {
			if !strings.HasPrefix(conversion.what, "extract ") && !strings.HasPrefix(conversion.what, "*") {
				problems = append(problems, pkg.Fset.Position(conversion.at).String()+": go/ssa converts "+conversion.what+
					" here, in the function at "+pkg.Fset.Position(conversion.fn.Pos()).String()+", and it has no expression of its own")
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
