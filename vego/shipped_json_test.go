package vego

import (
	"bytes"
	"encoding/json"
	"go/types"
	"os"
	"os/exec"
	"path/filepath"
	"reflect"
	"slices"
	"strings"
	"testing"

	"golang.org/x/tools/go/packages"
)

// The entries of encoding/json (F29) are held against every build of
// encoding/json a program can be built with: the test builds
// testdata/jsonharness once for each, hands it the bound vego generates
// for each of its types, and reads what it found. The ordinary run covers
// the toolchain it runs on, with and without GOEXPERIMENT=jsonv2;
// VEGO_GO126=1 adds Go 1.26.6 both ways.

// jsonBuild is one build of encoding/json: the environment its helper is
// built with.
type jsonBuild struct {
	name string
	env  []string
}

// jsonBuilds are the builds the run covers.
func jsonBuilds() []jsonBuild {
	builds := []jsonBuild{
		{"default", nil},
		{"nojsonv2", []string{"GOEXPERIMENT=nojsonv2"}},
	}
	if os.Getenv("VEGO_GO126") == "1" {
		builds = append(builds,
			jsonBuild{"go1.26.6", []string{"GOTOOLCHAIN=go1.26.6"}},
			jsonBuild{"go1.26.6 jsonv2", []string{"GOTOOLCHAIN=go1.26.6", "GOEXPERIMENT=jsonv2"}})
	}
	return builds
}

// jsonHelper builds the helper for a build and returns its path.
func jsonHelper(t *testing.T, b jsonBuild) string {
	t.Helper()
	helper := filepath.Join(t.TempDir(), "jsonharness")
	build := exec.Command("go", "build", "-o", helper, "./testdata/jsonharness")
	build.Env = append(os.Environ(), b.env...)
	if out, err := build.CombinedOutput(); err != nil {
		t.Fatalf("build the helper for %s: %v\n%s", b.name, err, out)
	}
	return helper
}

// jsonEntries are the shipped entries of encoding/json, each held by
// TestJSONEntries; an entry of the package not listed has no harness.
var jsonEntries = []string{"encoding/json.Marshal", "encoding/json.MarshalIndent", jsonEncodeKey}

// checkJSONEntry reads a shipped entry of encoding/json as a call would:
// it must be usable, encode its parameter v, and vouch for its error.
func checkJSONEntry(t *testing.T, pv *pkgVerifier, pkg *types.Package, key string) {
	_, name, _ := splitFuncName(key)
	callee, ok := pkg.Scope().Lookup(name).(*types.Func)
	if receiver, method, isMethod := strings.Cut(strings.TrimPrefix(strings.TrimPrefix(name, "("), "*"), ")."); isMethod {
		found, _, _ := types.LookupFieldOrMethod(types.NewPointer(pkg.Scope().Lookup(receiver).Type()), true, pkg, method)
		callee, ok = found.(*types.Func)
	}
	if !ok {
		t.Fatalf("package %s has no function %s", pkg.Path(), name)
	}
	fn := pv.trustedContract(callee)
	if fn == nil || len(fn.defects) > 0 {
		t.Fatalf("the entry of %s cannot be used: %v", key, fn.defects)
	}
	switch {
	case fn.encoded == nil || fn.encoded.Name() != "v":
		t.Errorf("the entry of %s does not encode v", key)
	case key != jsonEncodeKey && !fn.vouches[1]:
		t.Errorf("the entry of %s does not vouch for its error", key)
	case key == jsonEncodeKey && fn.vouches[0]:
		// What Write returned is not vouched for.
		t.Errorf("the entry of %s vouches for its error", key)
	}
}

// jsonHarnessInput is what the helper reads.
type jsonHarnessInput struct {
	Seed    uint64
	Samples int
	Cases   []jsonHarnessCase
}

type jsonHarnessCase struct {
	Type   string
	Groups []jsonHarnessGroup
	Depth  int
	Raw    bool
	Want   bool
}

type jsonHarnessGroup struct {
	Steps []struct{ Binder, Length, Guard string }
	Konst int64
	Terms []struct {
		Coef int64
		Path string
	}
}

// jsonHarnessOutput is what the helper writes.
type jsonHarnessOutput struct {
	Build    string
	Failures []string
	Above    map[string]int
	Called   []string
	Errors   []string
	Samples  int
}

// runJSONHelper runs a helper on an input.
func runJSONHelper(t *testing.T, helper string, in jsonHarnessInput) jsonHarnessOutput {
	t.Helper()
	data, err := json.Marshal(in)
	if err != nil {
		t.Fatal(err)
	}
	cmd := exec.Command(helper)
	cmd.Stdin = bytes.NewReader(data)
	var stderr bytes.Buffer
	cmd.Stderr = &stderr
	raw, err := cmd.Output()
	if err != nil {
		t.Fatalf("run %s: %v\n%s", helper, err, stderr.String())
	}
	var out jsonHarnessOutput
	if err := json.Unmarshal(raw, &out); err != nil {
		t.Fatalf("read what %s wrote: %v\n%s", helper, err, raw)
	}
	return out
}

// jsonHarnessTypes loads the helper's package and returns the type of each
// name its registry has.
func jsonHarnessTypes(t *testing.T) (*types.Package, types.Sizes, map[string]types.Type) {
	t.Helper()
	pkgs, err := packages.Load(&packages.Config{Mode: packages.NeedName | packages.NeedTypes | packages.NeedTypesSizes | packages.NeedImports | packages.NeedDeps,
		Dir: filepath.Join("testdata", "jsonharness")}, ".")
	if err != nil || len(pkgs) != 1 || len(pkgs[0].Errors) > 0 {
		t.Fatalf("load the helper: %v %v", err, pkgs)
	}
	pkg := pkgs[0].Types
	jsonPkg := pkgs[0].Imports["encoding/json"].Types
	lookup := func(name string) types.Type {
		switch name {
		case "Raw":
			return jsonPkg.Scope().Lookup("RawMessage").Type()
		case "Number":
			return jsonPkg.Scope().Lookup("Number").Type()
		}
		if inner, ok := strings.CutPrefix(name, "*"); ok {
			return types.NewPointer(pkg.Scope().Lookup(inner).Type())
		}
		obj := pkg.Scope().Lookup(name)
		if obj == nil {
			t.Fatalf("the helper declares no %s", name)
		}
		return obj.Type()
	}
	found := map[string]types.Type{}
	for _, name := range []string{"Basics", "Quoted", "Bytes", "Leaves", "Inner", "*Inner", "Nest", "Embeds", "Tags", "TopSlice", "TopMap", "Empty", "Loud", "Raw", "Number", "TwoBools", "TwoTimes", "TwoF64", "TwoF32", "TwoStrings", "TwoQuoted", "TwoQInts", "TopBools", "BoolMap"} {
		found[name] = lookup(name)
	}
	return pkg, pkgs[0].TypesSizes, found
}

// jsonCases walks each type with a table of weights.
func jsonCases(t *testing.T, wt jsonWeightTable, pkg *types.Package, sizes types.Sizes, found map[string]types.Type, want bool) []jsonHarnessCase {
	t.Helper()
	var cases []jsonHarnessCase
	for _, name := range slices.Sorted(func(yield func(string) bool) {
		for name := range found {
			if !yield(name) {
				return
			}
		}
	}) {
		why, walk := jsonWalkWith(wt, pkg, sizes, found[name], "v")
		if why != "" {
			t.Fatalf("the walk refuses %s: %s", name, why)
		}
		c := jsonHarnessCase{Type: name, Depth: walk.depth, Raw: walk.raw, Want: want}
		for _, g := range walk.groups {
			var hg jsonHarnessGroup
			hg.Konst = g.konst
			for _, s := range g.steps {
				hg.Steps = append(hg.Steps, struct{ Binder, Length, Guard string }{s.binder, s.length, s.guard})
			}
			for _, term := range g.terms {
				hg.Terms = append(hg.Terms, struct {
					Coef int64
					Path string
				}{term.coef, term.path})
			}
			c.Groups = append(c.Groups, hg)
		}
		cases = append(cases, c)
	}
	return cases
}

// jsonErrorTypes are the dynamic types of the errors that the entries of
// encoding/json were seen to return, in any build, whose methods were read
// against what vouches claims: each Error builds a string from the error's
// fields, and none writes, panics, or has an Is method that calls its
// target. A type not in the list fails the test until it is read.
var jsonErrorTypes = map[string]bool{
	"*json.UnsupportedValueError": true,
	"*json.MarshalerError":        true,
	"*json.SyntaxError":           true,
	"*errors.errorString":         true,
	"*jsontext.SyntacticError":    true,
	"*json.SemanticError":         true,
	"*fmt.wrapError":              true,
	"*time.ParseError":            true,
}

// TestJSONEntries holds the entries of json.Marshal and json.MarshalIndent
// against every build: what they write stays within the bound vego
// generates for the type, every method they call is one jsonMethods lists
// and every method listed is called by some build, nothing else of the
// value runs, no error refers to memory the value reaches but a float, and
// every error's type was read. Then it makes each weight of the table one
// smaller and finds a sample above that bound in some build.
func TestJSONEntries(t *testing.T) {
	parallel(t)
	pkg, sizes, found := jsonHarnessTypes(t)
	exact := jsonWeights
	exact.NoEntryAlloc = true
	cases := jsonCases(t, jsonWeights, pkg, sizes, found, false)
	called := map[string]bool{}
	var helpers []string
	for _, b := range jsonBuilds() {
		helper := jsonHelper(t, b)
		helpers = append(helpers, helper)
		out := runJSONHelper(t, helper, jsonHarnessInput{Seed: 29, Samples: 300, Cases: cases})
		for _, failure := range out.Failures {
			t.Errorf("%s: %s", out.Build, failure)
		}
		if out.Samples == 0 {
			t.Errorf("%s: no sample ran", out.Build)
		}
		for _, name := range out.Called {
			called[name] = true
		}
		for _, name := range out.Errors {
			if !jsonErrorTypes[name] {
				t.Errorf("%s: an entry of encoding/json returned an error of type %s, whose methods were not read", out.Build, name)
			}
		}
	}
	for _, name := range jsonMethods {
		if !called[name] {
			t.Errorf("no build called %s, which jsonMethods lists", name)
		}
	}
	// Each weight one smaller passes the bound in some build. EntryExtra
	// is checked without what a map's entries allocate, which is no part of
	// the output.
	table := reflect.ValueOf(&exact).Elem()
	for i := range table.NumField() {
		field := table.Type().Field(i)
		if field.Type.Kind() != reflect.Int64 {
			continue
		}
		t.Run("smaller "+field.Name, func(t *testing.T) {
			mutant := exact
			f := reflect.ValueOf(&mutant).Elem().Field(i)
			if field.Name == "IntLess" {
				f.SetInt(1)
			} else {
				f.SetInt(f.Int() - 1)
			}
			cases := jsonCases(t, mutant, pkg, sizes, found, true)
			above := 0
			for _, helper := range helpers {
				out := runJSONHelper(t, helper, jsonHarnessInput{Seed: 31, Samples: 300, Cases: cases})
				for _, n := range out.Above {
					above += n
				}
			}
			if above == 0 {
				t.Errorf("with %s one smaller, no output in any build passed the bound", field.Name)
			}
		})
	}
}
