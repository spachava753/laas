package vego

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// TestCorpusClaims runs the tests that packages of the corpus hold beside
// their programs: each calls functions whose contracts vego proves and
// checks what the contracts claim against Go, as the real errors package
// and the real conversions do it (F33). The analysis never reads these
// files, since it loads the packages without their tests. The run covers
// the toolchain the test runs on; VEGO_GO126=1 adds Go 1.26.6.
func TestCorpusClaims(t *testing.T) {
	parallel(t)
	testdata, err := filepath.Abs("testdata")
	if err != nil {
		t.Fatal(err)
	}
	found, err := filepath.Glob(filepath.Join(testdata, "src", "*", "*_test.go"))
	if err != nil {
		t.Fatal(err)
	}
	packages := map[string]bool{}
	for _, file := range found {
		packages[filepath.Base(filepath.Dir(file))] = true
	}
	if !packages["typederrors"] || !packages["typederrorsclient"] {
		t.Fatalf("no package of the corpus holds claims: %v", found)
	}
	// GOPATH mode does not switch toolchains, so the go command of the
	// other toolchain is found in module mode and run itself.
	toolchains := map[string]string{"": "go"}
	if os.Getenv("VEGO_GO126") == "1" {
		root := exec.Command("go", "env", "GOROOT")
		root.Env = append(os.Environ(), "GOTOOLCHAIN=go1.26.6")
		out, err := root.Output()
		if err != nil {
			t.Fatalf("find Go 1.26.6: %v", err)
		}
		toolchains["go1.26.6"] = filepath.Join(strings.TrimSpace(string(out)), "bin", "go")
	}
	for toolchain, gocmd := range toolchains {
		for pkg := range packages {
			name := pkg
			if toolchain != "" {
				name += " " + toolchain
			}
			t.Run(name, func(t *testing.T) {
				parallel(t)
				env := append(os.Environ(), "GOPATH="+testdata, "GO111MODULE=off", "GOWORK=off", "GOFLAGS=", "GOTOOLCHAIN=local")
				if toolchain != "" {
					// The test binary runs with the GOROOT of its own toolchain.
					env = append(env, "GOROOT="+filepath.Dir(filepath.Dir(gocmd)))
				}
				version := exec.Command(gocmd, "env", "GOVERSION")
				version.Env = env
				out, err := version.Output()
				if err != nil || toolchain != "" && strings.TrimSpace(string(out)) != toolchain {
					t.Fatalf("the go command %s is %s, not %s: %v", gocmd, out, toolchain, err)
				}
				run := exec.Command(gocmd, "test", "-count=1", "-vet=off", "./src/"+pkg)
				run.Dir = testdata
				run.Env = env
				if out, err := run.CombinedOutput(); err != nil {
					t.Fatalf("go test %s: %v\n%s", pkg, err, out)
				}
			})
		}
	}
}
