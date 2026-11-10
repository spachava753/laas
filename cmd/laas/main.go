package main

import (
	"flag"
	"fmt"
	"os"
	"regexp"
	"slices"
	"strings"

	"github.com/spachava753/laas/funcdoc"
	"github.com/spachava753/laas/inlinehelper"
	"github.com/spachava753/laas/teststructure"
	"github.com/spachava753/laas/vego"
	"golang.org/x/tools/go/analysis"
	"golang.org/x/tools/go/analysis/checker"
	"golang.org/x/tools/go/analysis/multichecker"
	"golang.org/x/tools/go/packages"
)

var excludedPackages packageFilter

type packageFilter struct {
	pattern    string
	expression *regexp.Regexp
}

func (filter *packageFilter) Set(pattern string) error {
	expression, err := regexp.Compile(pattern)
	if err != nil {
		return err
	}
	filter.pattern = pattern
	filter.expression = expression
	return nil
}

func (filter *packageFilter) String() string {
	return filter.pattern
}

func (filter *packageFilter) Match(packagePath string) bool {
	return filter.expression != nil && filter.expression.MatchString(packagePath)
}

// trustReport prints what the proofs of the given packages take on trust,
// instead of running the linters. It is selected by -vego.trust; any other
// -vego. flags are passed on to the verifier.
func trustReport(args []string) int {
	var patterns []string
	for _, arg := range args {
		name, value, hasValue := strings.Cut(strings.TrimLeft(arg, "-"), "=")
		switch {
		case !strings.HasPrefix(arg, "-"):
			patterns = append(patterns, arg)
		case name == "vego.trust":
		case strings.HasPrefix(name, "vego.") && hasValue:
			if err := vego.Analyzer.Flags.Set(strings.TrimPrefix(name, "vego."), value); err != nil {
				fmt.Fprintf(os.Stderr, "laas: %s: %v\n", arg, err)
				return 2
			}
		default:
			fmt.Fprintf(os.Stderr, "laas: %s cannot be combined with -vego.trust\n", arg)
			return 2
		}
	}
	packagesLoaded, err := packages.Load(&packages.Config{Mode: packages.LoadAllSyntax}, patterns...)
	if err != nil || packages.PrintErrors(packagesLoaded) > 0 {
		fmt.Fprintf(os.Stderr, "laas: cannot load packages: %v\n", err)
		return 1
	}
	graph, err := checker.Analyze([]*analysis.Analyzer{vego.Analyzer}, packagesLoaded, nil)
	if err != nil {
		fmt.Fprintf(os.Stderr, "laas: %v\n", err)
		return 1
	}
	var usages []*vego.Usage
	failures := 0
	for _, action := range graph.Roots {
		if usage, ok := action.Result.(*vego.Usage); ok {
			usages = append(usages, usage)
		}
		failures += len(action.Diagnostics)
	}
	dir, _ := os.Getwd()
	fmt.Print(vego.TrustReport(usages, dir))
	if failures > 0 {
		fmt.Printf("\nNote: verification reported %d problems; run laas without -vego.trust to see them.\n", failures)
	}
	return 0
}

func main() {
	if slices.ContainsFunc(os.Args[1:], func(arg string) bool { return strings.TrimLeft(arg, "-") == "vego.trust" }) {
		os.Exit(trustReport(os.Args[1:]))
	}
	flag.Var(
		&excludedPackages,
		"exclude-packages",
		"exclude package import paths matching this Go regular expression",
	)

	analyzers := []*analysis.Analyzer{
		funcdoc.Analyzer,
		inlinehelper.Analyzer,
		teststructure.Analyzer,
		vego.Analyzer,
	}
	for _, analyzer := range analyzers {
		run := analyzer.Run
		analyzer.Run = func(pass *analysis.Pass) (any, error) {
			if excludedPackages.Match(pass.Pkg.Path()) {
				return nil, nil
			}
			return run(pass)
		}
	}

	multichecker.Main(analyzers...)
}
