package vego

import (
	"bytes"
	"encoding/json"
	"go/types"
	"maps"
	"math/big"
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
var jsonEntries = []string{"encoding/json.Marshal", "encoding/json.MarshalIndent", jsonEncodeKey, "encoding/json.Unmarshal", jsonDecodeKey}

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
	case key == jsonDecodeKey:
		if fn.decoded == nil || fn.decoded.Name() != "v" || fn.vouches[0] {
			t.Errorf("the entry of %s does not decode into v, or vouches for its error, which may be the reader's", key)
		}
	case key == "encoding/json.Unmarshal":
		if fn.decoded == nil || fn.decoded.Name() != "v" || fn.decodedFrom == nil || !fn.vouches[0] {
			t.Errorf("the entry of %s does not decode into v from data and vouch for its error", key)
		}
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
	Allocs  bool
}

type jsonHarnessCase struct {
	Type    string
	Lengths []jsonHarnessLength
}

type jsonHarnessLength struct {
	Key   string
	Steps []struct{ Binder, Length, Guard string }
	Text  string
}

// jsonHarnessOutput is what the helper writes.
type jsonHarnessOutput struct {
	Build        string
	Failures     []string
	Called       []string
	Errors       []string
	DecodeErrors []string
	Samples      []struct {
		Type  string
		Outs  []int64
		Maxes map[string]int64
	}
	Allocs []jsonAlloc
}

// jsonAlloc is the largest single allocation of one encoding call, with
// the length of what it wrote and the largest value the encoded value
// holds, in bytes.
type jsonAlloc struct {
	Type, Call                  string
	Largest, Out, Held, Entries int64
}

// jsonIndents are the lengths of the prefixes and indents the helper runs
// MarshalIndent with, after Marshal: "" and two spaces, ">" and three
// tabs, "<<" and none.
var jsonIndents = [][2]int64{{0, 2}, {1, 3}, {2, 0}}

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

// jsonWalks walks each type with a table of weights.
func jsonWalks(t *testing.T, wt jsonWeightTable, pkg *types.Package, sizes types.Sizes, found map[string]types.Type) map[string]*jsonWalk {
	t.Helper()
	walks := map[string]*jsonWalk{}
	for name, typ := range found {
		why, walk := jsonWalkWith(wt, pkg, sizes, typ, "v")
		if why != "" {
			t.Fatalf("the walk refuses %s: %s", name, why)
		}
		walks[name] = walk
	}
	return walks
}

// jsonCases are the cases the helper runs: each type with the lengths
// its walk counts.
func jsonCases(walks map[string]*jsonWalk) []jsonHarnessCase {
	var cases []jsonHarnessCase
	for _, name := range slices.Sorted(maps.Keys(walks)) {
		c := jsonHarnessCase{Type: name}
		for _, l := range walks[name].lengths() {
			hl := jsonHarnessLength{Key: l.key(), Text: l.text}
			for _, s := range l.steps {
				hl.Steps = append(hl.Steps, struct{ Binder, Length, Guard string }{s.binder, s.length, s.guard})
			}
			c.Lengths = append(c.Lengths, hl)
		}
		cases = append(cases, c)
	}
	return cases
}

// jsonAbove counts the outputs of samples that pass the bound vego proves
// a call against, computed by total from the longest instance of each
// length the sample holds, as checkEncodedAlloc computes it from the
// bounds it proves; for MarshalIndent with the lengths of the prefix and
// the indent.
func jsonAbove(t *testing.T, out jsonHarnessOutput, walks map[string]*jsonWalk, report bool) int {
	above := 0
	for _, sample := range out.Samples {
		walk := walks[sample.Type]
		for i, got := range sample.Outs {
			if got < 0 {
				continue
			}
			indented := i > 0
			total := walk.total(func(l jsonLength) *big.Int {
				switch {
				case l.text == "|prefix|":
					return big.NewInt(jsonIndents[i-1][0])
				case l.text == "|indent|":
					return big.NewInt(jsonIndents[i-1][1])
				}
				n, ok := sample.Maxes[l.key()]
				if !ok {
					t.Fatalf("%s: the helper measured no %s", sample.Type, l.key())
				}
				return big.NewInt(n)
			}, indented)
			if big.NewInt(got).Cmp(total) > 0 {
				above++
				if report && above <= 20 {
					t.Errorf("%s: %s built %d bytes, more than %s, the bound of its lengths %v (call %d)", out.Build, sample.Type, got, total, sample.Maxes, i)
				}
			}
		}
	}
	return above
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

// jsonDecodeErrorTypes are the dynamic types of the errors Unmarshal was
// seen to return, in any build, whose methods were read against what
// vouches claims: each Error builds a string from the error's own fields
// (the message of a SyntaxError, the type and field of an
// UnmarshalTypeError, the quoted value of a time.ParseError, the offset of
// a base64.CorruptInputError), and none writes, panics, or has an Is
// method. CorruptInputError is an int64, so == on it compares values, as
// on the syscall.Errno inside the vouched errors of os.
var jsonDecodeErrorTypes = map[string]bool{
	"*errors.errorString":         true,
	"*json.SyntaxError":           true,
	"*json.UnmarshalTypeError":    true,
	"*time.ParseError":            true,
	"base64.CorruptInputError":    true,
	"*jsontext.SyntacticError":    true,
	"*json.InvalidUnmarshalError": true,
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
	walks := jsonWalks(t, jsonWeights, pkg, sizes, found)
	cases := jsonCases(walks)
	called := map[string]bool{}
	var outs []jsonHarnessOutput
	// Each term is seen to be needed: some call allocated more than once
	// what exists, and some more than three times it, which only the term
	// for the entries of a map covers (v2 sorts the members of a map with
	// keys that are not strings in a slice of 80 bytes each; the harness's
	// map of a million short keys reaches it, F24 of the review of step 3).
	sharper, sorts := false, false
	for _, b := range jsonBuilds() {
		helper := jsonHelper(t, b)
		// Under a declared memory an encoding call is accepted with no
		// bound on what it builds, on the reading that each allocation it
		// makes is at most three times what exists, the output or one
		// value held, and a page (F8 of the review of F38).
		for _, a := range runJSONHelper(t, helper, jsonHarnessInput{Seed: 31, Samples: 1, Cases: cases, Allocs: true}).Allocs {
			exists := max(a.Out, a.Held)
			// What an encoding call may allocate at once, read from the
			// four builds of encoding/json (see Sizes under a declared
			// memory in the ROADMAP): three times what it writes or the
			// largest value it is handed holds, 81 bytes for each entry
			// of a map whose keys it sorts (v2's members of 80 bytes and
			// the key and the value of each), and 2^20 for the stacks of
			// its states, which grow with the depth of the value.
			if a.Largest > 3*exists+jsonEntryAlloc*a.Entries+1<<20 {
				t.Errorf("%s: %s of a %s allocated %d bytes at once, more than three times the %d bytes it wrote or the value holds, "+
					"81 bytes for each of the %d entries of its largest map, and 2^20", b.name, a.Call, a.Type, a.Largest, exists, a.Entries)
			}
			sharper = sharper || a.Largest > exists+jsonEntryAlloc*a.Entries+1<<20
			sorts = sorts || a.Largest > 3*exists+1<<20
		}
		out := runJSONHelper(t, helper, jsonHarnessInput{Seed: 29, Samples: 300, Cases: cases})
		outs = append(outs, out)
		for _, failure := range out.Failures {
			t.Errorf("%s: %s", out.Build, failure)
		}
		if len(out.Samples) == 0 {
			t.Errorf("%s: no sample ran", out.Build)
		}
		jsonAbove(t, out, walks, true)
		for _, name := range out.Called {
			called[name] = true
		}
		for _, name := range out.DecodeErrors {
			if !jsonDecodeErrorTypes[name] {
				t.Errorf("%s: Unmarshal returned an error of type %s, whose methods were not read", out.Build, name)
			}
		}
		for _, name := range out.Errors {
			if !jsonErrorTypes[name] {
				t.Errorf("%s: an entry of encoding/json returned an error of type %s, whose methods were not read", out.Build, name)
			}
		}
	}
	if !sorts {
		t.Errorf("no encoding call allocated more than three times what exists: the term for the entries of a map is not seen to be needed")
	}
	if !sharper {
		t.Errorf("no encoding call allocated more than once what it wrote or the value holds: the factor of three is not seen to be needed, nor the measure to work")
	}
	for _, name := range jsonMethods {
		if !called[name] {
			t.Errorf("no build called %s, which jsonMethods lists", name)
		}
	}
	// Each weight one smaller passes the bound in some build. EntryExtra
	// is checked without what a map's entries allocate, which is no part of
	// the output.
	exact := jsonWeights
	exact.NoEntryAlloc = true
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
			smaller := jsonWalks(t, mutant, pkg, sizes, found)
			above := 0
			for _, out := range outs {
				above += jsonAbove(t, out, smaller, false)
			}
			if above == 0 {
				t.Errorf("with %s one smaller, no output in any build passed the bound", field.Name)
			}
		})
	}
}
