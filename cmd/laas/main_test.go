package main

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

func TestPackageFilter(t *testing.T) {
	var filter packageFilter
	if filter.Match("github.com/spachava753/laas/generated") {
		t.Fatal("empty filter matched a package")
	}

	if err := filter.Set(`(^|/)(generated|mocks)($|/)`); err != nil {
		t.Fatalf("set filter: %v", err)
	}
	if got, want := filter.String(), `(^|/)(generated|mocks)($|/)`; got != want {
		t.Fatalf("filter.String() = %q, want %q", got, want)
	}

	tests := []struct {
		path string
		want bool
	}{
		{path: "github.com/acme/project/generated", want: true},
		{path: "github.com/acme/project/mocks/http", want: true},
		{path: "github.com/acme/project/generator", want: false},
		{path: "github.com/acme/project/service", want: false},
	}
	for _, test := range tests {
		t.Run(test.path, func(t *testing.T) {
			if got := filter.Match(test.path); got != test.want {
				t.Fatalf("filter.Match(%q) = %t, want %t", test.path, got, test.want)
			}
		})
	}

	if err := filter.Set("["); err == nil {
		t.Fatal("invalid regular expression was accepted")
	}
	if !filter.Match("github.com/acme/project/generated") {
		t.Fatal("invalid update replaced the previous filter")
	}
}

// TestTrustReportNeedsZ3 checks that the trust report is not printed, and
// the status is 1, when the verifier could not run, as without Z3.
func TestTrustReportNeedsZ3(t *testing.T) {
	dir := t.TempDir()
	for name, text := range map[string]string{
		"go.mod": "module example.com/needsz3\n\ngo 1.24\n",
		"a.go":   "// Package needsz3 has one verified function.\npackage needsz3\n\n// Double doubles a small number.\n//\n// @Requires 0 <= x And x < 100\n// @Ensures y = 2*x\nfunc Double(x int) (y int) { return 2 * x }\n",
	} {
		if err := os.WriteFile(filepath.Join(dir, name), []byte(text), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	t.Chdir(dir)
	// With Z3 the same module verifies and the report is printed, so the
	// status below comes from the missing Z3 and not from loading.
	z3, err := exec.LookPath("z3")
	if err != nil {
		t.Fatal(err)
	}
	if got := trustReport([]string{"-vego.trust", "-vego.z3=" + z3, "./..."}); got != 0 {
		t.Fatalf("trustReport with Z3 = %d, want 0", got)
	}
	if got := trustReport([]string{"-vego.trust", "-vego.z3=" + filepath.Join(dir, "no-z3"), "./..."}); got != 1 {
		t.Fatalf("trustReport without Z3 = %d, want 1", got)
	}
}

// TestChangedSentinelReportedAtRoot runs laas on one package that is built
// with a package whose proof relies on its error variable and with another
// that changes it. Only the package laas is run on reports, so the change
// has to be reported there although it is in neither.
func TestChangedSentinelReportedAtRoot(t *testing.T) {
	z3, err := exec.LookPath("z3")
	if err != nil {
		t.Fatal(err)
	}
	laas := filepath.Join(t.TempDir(), "laas")
	if out, err := exec.Command("go", "build", "-o", laas, ".").CombinedOutput(); err != nil {
		t.Fatalf("build laas: %v\n%s", err, out)
	}
	dir := t.TempDir()
	for name, text := range map[string]string{
		"go.mod": "module example.com/m2\n\ngo 1.24\n",
		"lib/lib.go": "package lib\n\nimport \"errors\"\n\nvar ErrGone = errors.New(\"gone\")\n\n" +
			"// Fail fails unless told otherwise.\n//\n// @Ensures err = nil <-> ok\nfunc Fail(ok bool) (err error) {\n\tif ok {\n\t\treturn nil\n\t}\n\treturn ErrGone\n}\n",
		"mid/mid.go":   "package mid\n\nimport \"example.com/m2/lib\"\n\nfunc init() { lib.ErrGone = nil }\n",
		"root/root.go": "package root\n\nimport (\n\t\"example.com/m2/lib\"\n\t_ \"example.com/m2/mid\"\n)\n\nfunc Use() error { return lib.Fail(false) }\n",
	} {
		path := filepath.Join(dir, name)
		if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(path, []byte(text), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	run := exec.Command(laas, "-vego.z3="+z3, "./root")
	run.Dir = dir
	out, err := run.CombinedOutput()
	want := "lib.ErrGone is changed at mid.go:5 in package example.com/m2/mid, which this package is built with, " +
		"but proofs in package example.com/m2/lib rely on it being the error it was declared with"
	if err == nil || !strings.Contains(string(out), want) {
		t.Fatalf("laas ./root: %v\n%s\nwant a report containing %q", err, out, want)
	}
}
