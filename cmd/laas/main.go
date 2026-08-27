package main

import (
	"flag"
	"regexp"

	"github.com/spachava753/laas/funcdoc"
	"github.com/spachava753/laas/inlinehelper"
	"github.com/spachava753/laas/teststructure"
	"golang.org/x/tools/go/analysis"
	"golang.org/x/tools/go/analysis/multichecker"
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

func main() {
	flag.Var(
		&excludedPackages,
		"exclude-packages",
		"exclude package import paths matching this Go regular expression",
	)

	analyzers := []*analysis.Analyzer{
		funcdoc.Analyzer,
		inlinehelper.Analyzer,
		teststructure.Analyzer,
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
