package vego

import (
	"go/ast"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"golang.org/x/tools/go/analysis"
	"golang.org/x/tools/go/analysis/checker"
	"golang.org/x/tools/go/packages"
)

// TestCopiesConfirmed runs the corpus of copies with the syntactic walk
// turned off: go/ssa alone must refuse every function whose name starts
// with Copy, and nothing in the functions that copy nothing. Overwrites and
// append are not copies of a value that go/ssa shows, and are left to the
// walk.
func TestCopiesConfirmed(t *testing.T) {
	skipCopyWalk = true
	defer func() { skipCopyWalk = false }()
	testdata, err := filepath.Abs("testdata")
	if err != nil {
		t.Fatal(err)
	}
	config := &packages.Config{
		Mode: packages.LoadAllSyntax,
		Dir:  filepath.Join(testdata, "src"),
		Env:  append(os.Environ(), "GOPATH="+testdata, "GO111MODULE=off", "GOPROXY=off", "GOWORK=off"),
	}
	loaded, err := packages.Load(config, "locks")
	if err != nil || packages.PrintErrors(loaded) > 0 {
		t.Fatalf("load: %v", err)
	}
	graph, err := checker.Analyze([]*analysis.Analyzer{newAnalyzer()}, loaded, nil)
	if err != nil {
		t.Fatal(err)
	}
	root := graph.Roots[0]
	if root.Err != nil {
		t.Fatal(root.Err)
	}
	refused := map[string]string{}
	for _, d := range root.Diagnostics {
		if _, rest, ok := strings.Cut(d.Message, "vego: cannot verify "); ok {
			name, _, _ := strings.Cut(rest, ":")
			refused[name] = d.Message
		}
	}
	checked := 0
	for _, file := range root.Package.Syntax {
		if !strings.Contains(filepath.Base(root.Package.Fset.File(file.Pos()).Name()), "copies") {
			continue
		}
		for _, decl := range file.Decls {
			fd, ok := decl.(*ast.FuncDecl)
			if !ok || fd.Doc == nil || !strings.Contains(fd.Doc.Text(), "@Ensures") {
				continue
			}
			name, msg := fd.Name.Name, refused[fd.Name.Name]
			switch {
			case strings.HasPrefix(name, "Copy"):
				checked++
				if !strings.Contains(msg, "Go copies a") {
					t.Errorf("%s is not refused by go/ssa: %q", name, msg)
				}
			case strings.Contains(msg, "Go copies a"):
				t.Errorf("%s copies nothing, but go/ssa refuses it: %q", name, msg)
			}
		}
	}
	if checked < 20 {
		t.Fatalf("only %d functions that copy were checked", checked)
	}
}
