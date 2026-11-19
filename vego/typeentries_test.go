package vego

import (
	"go/ast"
	"go/token"
	"go/types"
	"os"
	"path/filepath"
	"slices"
	"testing"

	"golang.org/x/tools/go/analysis"
	"golang.org/x/tools/go/analysis/checker"
	"golang.org/x/tools/go/packages"
)

// TestInAnalysedModule checks which packages count as packages of the
// analysed module, whose types cannot be given a contract in the trust
// file. The analysed package lies in w/app, under w/go.mod.
func TestInAnalysedModule(t *testing.T) {
	root := t.TempDir()
	for _, dir := range []string{"", "tools", "cache/golang.org/x/text@v0.1.0"} {
		if err := os.MkdirAll(filepath.Join(root, dir), 0o755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(filepath.Join(root, dir, "go.mod"), []byte("module m\n"), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	tests := []struct {
		name, module, path, file string
		want                     bool
	}{
		{name: "a package of the module", module: "example.com/app", path: "example.com/app/store", file: "store/store.go", want: true},
		{name: "the root package of the module", module: "example.com/app", path: "example.com/app", file: "app.go", want: true},
		{name: "a vendored package, under the go.mod of the module", module: "example.com/app", path: "gopkg.in/yaml.v3", file: "vendor/gopkg.in/yaml.v3/yaml.go"},
		{name: "a package whose path only starts like the module's", module: "example.com/app", path: "example.com/appendix", file: "vendor/example.com/appendix/a.go"},
		{name: "a nested module", module: "example.com/app", path: "example.com/app/tools", file: "tools/tools.go"},
		{name: "a package of the module cache", module: "example.com/app", path: "golang.org/x/text", file: "cache/golang.org/x/text@v0.1.0/text.go"},
		{name: "a package whose position is not known", module: "example.com/app", path: "example.com/app/gen"},
		{name: "GOPATH mode, under the same go.mod", path: "lib", file: "lib/lib.go", want: true},
		{name: "GOPATH mode, under another go.mod", path: "lib", file: "tools/lib/lib.go"},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			fset := token.NewFileSet()
			own := fset.AddFile(filepath.Join(root, "app", "main.go"), -1, 10)
			pass := &analysis.Pass{Fset: fset, Pkg: types.NewPackage("example.com/app/main", "main"), Files: []*ast.File{{Package: own.Pos(0)}}}
			if test.module != "" {
				pass.Module = &analysis.Module{Path: test.module}
			}
			declared := token.NoPos
			if test.file != "" {
				declared = fset.AddFile(filepath.Join(root, test.file), -1, 10).Pos(0)
			}
			pv := &pkgVerifier{pass: pass}
			if got := pv.inAnalysedModule(types.NewPackage(test.path, "p"), declared); got != test.want {
				t.Fatalf("got %v, want %v", got, test.want)
			}
		})
	}
}

// TestTypeEntriesInUse checks which entries for types the analysis of the
// corpus foreign reports as relied on: those that proofs use, and none
// that cannot be used, since every use of such an entry is an error.
func TestTypeEntriesInUse(t *testing.T) {
	analyzer := newAnalyzer()
	if err := analyzer.Flags.Set("trusted", filepath.Join("testdata", "trusted.yaml")); err != nil {
		t.Fatal(err)
	}
	testdata, err := filepath.Abs("testdata")
	if err != nil {
		t.Fatal(err)
	}
	config := &packages.Config{
		Mode: packages.LoadAllSyntax,
		Dir:  filepath.Join(testdata, "src"),
		Env:  append(os.Environ(), "GOPATH="+testdata, "GO111MODULE=off", "GOPROXY=off", "GOWORK=off"),
	}
	loaded, err := packages.Load(config, "foreign")
	if err != nil || packages.PrintErrors(loaded) > 0 {
		t.Fatalf("load: %v", err)
	}
	graph, err := checker.Analyze([]*analysis.Analyzer{analyzer}, loaded, nil)
	if err != nil {
		t.Fatal(err)
	}
	usage := graph.Roots[0].Result.(*Usage)
	var keys []string
	for _, use := range usage.Entries {
		if use.Every != "" {
			keys = append(keys, use.Key)
		}
	}
	slices.Sort(keys)
	for _, want := range []string{"(foreignlib.Filler).Fill", "(foreignlib.Sink).Put", "(foreignlib.Source).Next", "foreignlib.Hook", "foreignlib.Mapper"} {
		if !slices.Contains(keys, want) {
			t.Errorf("%s is not among the entries in use: %v", want, keys)
		}
	}
	for _, unusable := range []string{"(foreignlib.Opener).Open", "foreign.Local", "foreignlib.Half", "foreignlib.Runs"} {
		if slices.Contains(keys, unusable) {
			t.Errorf("%s cannot be used, and is among the entries in use: %v", unusable, keys)
		}
	}
}
