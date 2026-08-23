package main

import (
	"github.com/spachava753/laas/funcdoc"
	"github.com/spachava753/laas/teststructure"
	"golang.org/x/tools/go/analysis/multichecker"
)

func main() {
	multichecker.Main(
		funcdoc.Analyzer,
		teststructure.Analyzer,
	)
}
