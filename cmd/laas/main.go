package main

import (
	"github.com/spachava753/laas/funcdoc"
	"golang.org/x/tools/go/analysis/multichecker"
)

func main() {
	multichecker.Main(funcdoc.Analyzer)
}
