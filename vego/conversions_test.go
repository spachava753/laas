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
// records. Every conversion go/ssa makes of a value that is not a constant
// must have an expression the walk lists among the expressions of its
// operand, or none at all, as for one result of a call with several, which
// the verifier refuses. And every expression the walk lists that is not a
// constant must be an expression of a value go/ssa converts; go/ssa gives
// constants no expression.
func TestConversionLists(t *testing.T) {
	parallel(t)
	t.Run("on the corpus", func(t *testing.T) {
		heavyFor(t)
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
		if checked := checkConversionLists(t, loaded, true); checked < 50 {
			t.Fatalf("only %d packages of the corpus were checked", checked)
		}
	})

	// Packages of the standard library use far more forms of Go than the
	// corpus. That a listed expression is converted is only logged there,
	// since go/ssa folds some expressions that are not constants into
	// constants, as msg in msg := "failed"; panic(msg), and does not build
	// generic bodies as written. They are loaded from source, so this runs
	// only when VEGO_STD_PACKAGES names them, in a scope of its own:
	//
	//	VEGO_STD_PACKAGES="encoding/json text/template go/types net/http" \
	//	systemd-run --user --scope --quiet -p MemoryMax=12G -p MemorySwapMax=4G -- \
	//	go test -count=1 -run TestConversionLists ./vego
	t.Run("on the standard library", func(t *testing.T) {
		patterns := strings.Fields(os.Getenv("VEGO_STD_PACKAGES"))
		if len(patterns) == 0 {
			t.Skip("VEGO_STD_PACKAGES names no packages")
		}
		heavyFor(t)
		// Export data of a newer Go than golang.org/x/tools knows cannot
		// be read, so everything is loaded from source.
		loaded, err := packages.Load(&packages.Config{Mode: packages.LoadAllSyntax}, patterns...)
		if err != nil {
			t.Fatalf("load packages: %v", err)
		}
		if checked := checkConversionLists(t, loaded, false); checked < len(patterns) {
			t.Fatalf("only %d of the %d packages named were checked", checked, len(patterns))
		}
	})
}

// checkConversionLists compares the walk with go/ssa on packages and
// returns how many it checked. With strict, a listed expression that is not
// a constant and that go/ssa converts no value of is an error; otherwise it
// is logged.
func checkConversionLists(t *testing.T, loaded []*packages.Package, strict bool) (checked int) {
	t.Helper()
	for _, pkg := range loaded {
		if len(pkg.Errors) > 0 {
			t.Logf("%s does not load: %v", pkg.PkgPath, pkg.Errors[0])
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
		for _, conversion := range conversionsIn(buildSSA(pkg.Fset, pkg.Types, pkg.Syntax, pkg.TypesInfo), pkg.Types, pkg.Syntax, pkg.TypesInfo) {
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
					in := "in the initialisers of the package"
					if conversion.fn != nil {
						in = "in the function at " + pkg.Fset.Position(conversion.fn.Pos()).String()
					}
					problems = append(problems, pkg.Fset.Position(conversion.at).String()+": go/ssa converts "+conversion.what+
						" here, "+in+", and it has no expression")
				}
			case !slices.ContainsFunc(conversion.candidates, func(e ast.Expr) bool { return walked[e] }):
				problems = append(problems, pkg.Fset.Position(conversion.at).String()+": go/ssa converts "+conversion.what+
					", and the walk lists none of its expressions")
			}
		}
		for e := range walked {
			// go/ssa folds a conversion of nil to a type, as (*T)(nil),
			// into a constant, and so gives it no expression.
			call, isCall := ast.Unparen(e).(*ast.CallExpr)
			nilConversion := isCall && len(call.Args) == 1 && pkg.TypesInfo.Types[call.Fun].IsType() && pkg.TypesInfo.Types[ast.Unparen(call.Args[0])].IsNil()
			if pkg.TypesInfo.Types[e].Value != nil || candidate[e] || nilConversion {
				continue
			}
			problem := pkg.Fset.Position(e.Pos()).String() + ": the walk lists it, and go/ssa converts no value it is an expression of"
			if !strict {
				t.Log(problem)
				continue
			}
			problems = append(problems, problem)
		}
		slices.Sort(problems)
		for _, problem := range problems {
			t.Error(problem)
		}
	}
	return checked
}

