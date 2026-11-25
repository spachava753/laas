package vego

import (
	"go/importer"
	"go/token"
	"go/types"
	"maps"
	"slices"
	"strings"
	"testing"
)

// TestRestedOn computes, from the shipped files and the types of the
// toolchain, the keys of type entries that other shipped entries rest on,
// and fails unless they are those of restedOn (S0 of F35). An entry rests
// on the entry of a method of an interface in two directions:
//   - it calls the method on what it is handed: a parameter, the receiver
//     included, that it lists under runs, keeps, prints, or asserts, whose
//     type, or the element type of whose slice, implements the interface, or
//     a type it lists under asserts that implements it;
//   - it vouches for a value of the interface: a result it lists under
//     vouches, or memory a vouched parameter's modifies covers, whose type
//     is an interface that has the method.
//
// A parameter that reaches an interface only through fields is not
// counted. (*net/http.Request).PathValue and net/http.NotFound run r and
// call nothing of its Body or context, which the probes of probes_test.go
// hand them failing; (*bufio.Scanner).Scan and the methods of *log.Logger
// reach their reader or writer through a field that the keeps of their
// constructor counts.
func TestRestedOn(t *testing.T) {
	parallel(t)
	imports := importer.ForCompiler(token.NewFileSet(), "source", nil)
	lookup := func(path string) *types.Package {
		pkg, err := imports.Import(path)
		if err != nil {
			t.Fatalf("import %s: %v", path, err)
		}
		return pkg
	}
	// The type entries: methods of interfaces that the shipped files give
	// an entry, by key.
	type method struct {
		iface *types.Interface
		obj   *types.Func
	}
	typeEntries := map[string]method{}
	var functions []*trustEntry
	for _, file := range shippedContracts() {
		for key, entry := range file.entries {
			path, name, ok := splitFuncName(key)
			if !ok {
				continue
			}
			receiver, methodName, isMethod := strings.Cut(strings.TrimPrefix(name, "("), ").")
			if !isMethod {
				functions = append(functions, entry)
				continue
			}
			obj, _ := lookup(path).Scope().Lookup(strings.TrimPrefix(receiver, "*")).(*types.TypeName)
			if obj == nil {
				t.Fatalf("%s: no type %s in %s", key, receiver, path)
			}
			if iface, isIface := obj.Type().Underlying().(*types.Interface); isIface {
				found, _, _ := types.LookupFieldOrMethod(obj.Type(), false, obj.Pkg(), methodName)
				typeEntries[key] = method{iface: iface, obj: found.(*types.Func)}
				continue
			}
			functions = append(functions, entry)
		}
	}
	signature := func(entry *trustEntry) (*types.Signature, *types.Package) {
		path, name, _ := splitFuncName(entry.key)
		pkg := lookup(path)
		receiver, methodName, isMethod := strings.Cut(strings.TrimPrefix(name, "("), ").")
		if !isMethod {
			fn, _ := pkg.Scope().Lookup(name).(*types.Func)
			if fn == nil {
				return nil, nil
			}
			return fn.Type().(*types.Signature), pkg
		}
		obj := pkg.Scope().Lookup(strings.TrimPrefix(receiver, "*")).(*types.TypeName)
		found, _, _ := types.LookupFieldOrMethod(types.NewPointer(obj.Type()), true, pkg, methodName)
		fn, _ := found.(*types.Func)
		if fn == nil {
			return nil, nil
		}
		return fn.Type().(*types.Signature), pkg
	}
	computed := map[string][]string{}
	rests := func(key, entry string) {
		if !slices.Contains(computed[key], entry) {
			computed[key] = append(computed[key], entry)
		}
	}
	implementing := func(t types.Type, entry string) {
		if t == nil {
			return
		}
		if slice, isSlice := t.Underlying().(*types.Slice); isSlice {
			t = slice.Elem()
		}
		for key, m := range typeEntries {
			if types.Implements(t, m.iface) {
				rests(key, entry)
			}
		}
	}
	having := func(t types.Type, entry string) {
		iface, isIface := t.Underlying().(*types.Interface)
		if !isIface {
			return
		}
		for m := range iface.Methods() {
			if _, ok := typeEntries[m.FullName()]; ok {
				rests(m.FullName(), entry)
			}
		}
	}
	for _, entry := range functions {
		sig, pkg := signature(entry)
		if sig == nil || sig.TypeParams() != nil || sig.RecvTypeParams() != nil {
			continue
		}
		params := map[string]types.Type{}
		if recv := sig.Recv(); recv != nil {
			params[recv.Name()] = recv.Type()
		}
		for param := range sig.Params().Variables() {
			params[param.Name()] = param.Type()
		}
		var called []string
		for _, f := range entry.runs {
			called = append(called, f.text)
		}
		for _, lists := range [][]trustKeep{entry.keeps, entry.prints, entry.asserts} {
			for _, item := range lists {
				called = append(called, item.name)
			}
		}
		for _, name := range called {
			implementing(params[name], entry.key)
		}
		for _, item := range entry.asserts {
			for _, dest := range item.dests {
				if listed, problem := resolveListed(pkg, dest.text); problem == "" {
					implementing(listed, entry.key)
				}
			}
		}
		results := map[string]types.Type{}
		for i := range sig.Results().Len() {
			name := sig.Results().At(i).Name()
			switch {
			case name != "":
			case sig.Results().Len() == 1:
				name = "result"
			default:
				name = "result" + string(rune('1'+i))
			}
			results[name] = sig.Results().At(i).Type()
		}
		for _, vouched := range entry.vouches {
			if t, ok := results[vouched.text]; ok {
				having(t, entry.key)
			}
			if t, ok := params[vouched.text]; ok {
				if p, isPointer := t.Underlying().(*types.Pointer); isPointer {
					t = p.Elem()
				}
				having(t, entry.key)
			}
		}
	}
	// The in-place encoder and decoder of encoding/json call Write and
	// Read of the writer and reader they are handed (json.go,
	// jsondecode.go); the entries above already count both keys.
	for _, key := range []string{"(io.Writer).Write", "(io.Reader).Read"} {
		rests(key, "the in-place routes of encoding/json")
	}
	if got, want := slices.Sorted(maps.Keys(computed)), slices.Sorted(maps.Keys(restedOn)); !slices.Equal(got, want) {
		t.Fatalf("the shipped entries rest on %v, and restedOn lists %v", got, want)
	}
	for key, named := range restedOn {
		entry, _, _ := strings.Cut(named, " ")
		if !slices.Contains(computed[key], entry) {
			t.Errorf("restedOn names %s for %s, which rests on it by %v", entry, key, computed[key])
		}
	}
	// The table covers no key whose entry is absent.
	for key := range restedOn {
		if shippedEntry(key) == nil {
			t.Errorf("restedOn lists %s, which has no shipped entry", key)
		}
	}
}

// TestProjectReplaces holds the rule of restedon.go on entries parsed from
// text: the shipped entry with a reason of its own is accepted, and each
// field that differs is refused, asserts and stores among them.
func TestProjectReplaces(t *testing.T) {
	parallel(t)
	shipped := "    receiver: w\n    modifies: [w]\n    ensures:\n      - \"0 <= n And n <= |p|\"\n      - \"n < |p| -> err != nil\"\n"
	cases := []struct {
		name, body string
		refused    bool
	}{
		{"same", shipped, false},
		{"weaker", "    receiver: w\n    modifies: [w]\n", true},
		{"stronger", shipped + "      - \"err = nil\"\n", true},
		{"vouches", shipped + "    vouches: [err]\n", true},
		{"asserts", shipped + "    asserts:\n      w: []\n", true},
		{"receiver", strings.Replace(shipped, "receiver: w", "receiver: x", 1), true},
	}
	for _, c := range cases {
		file := parseTrustFile("vego-trusted.yaml", []byte("version: 1\ntrusted:\n  (io.Writer).Write:\n    reason: r\n"+c.body), false)
		why := projectReplaces(file.entries["(io.Writer).Write"])
		if (why != "") != c.refused {
			t.Errorf("%s: projectReplaces = %q", c.name, why)
		}
	}
	// Another key is never refused by the rule.
	file := parseTrustFile("vego-trusted.yaml", []byte("version: 1\ntrusted:\n  (context.Context).Err:\n    reason: r\n    modifies: []\n"), false)
	if why := projectReplaces(file.entries["(context.Context).Err"]); why != "" {
		t.Errorf("a replacement of an entry nothing rests on: %q", why)
	}
}

// TestBehindParams holds the claim of behind(p) in a function entry (F20
// of the review of S2 of F35): that the function writes the footprint of
// what p holds and changes none of its states. Each shipped entry that
// makes it lists p under runs, and its harness, named in probedBy, hands
// it probes that refuse Close and every other method the entry does not
// declare, so a function that closed what it is handed would fail there.
func TestBehindParams(t *testing.T) {
	parallel(t)
	found := 0
	for _, file := range shippedContracts() {
		for key, entry := range file.entries {
			if strings.HasPrefix(key, "(") && !strings.HasPrefix(key, "(*") && strings.Count(key, ")") == 1 {
				// The receiver of a method of an interface names behind
				// for its own footprint.
				continue
			}
			for _, m := range entry.modifies {
				name, ok := strings.CutPrefix(m.text, "behind(")
				if !ok {
					continue
				}
				name = strings.TrimSuffix(name, ")")
				found++
				if !slices.ContainsFunc(entry.runs, func(f trustFormula) bool { return f.text == name }) {
					t.Errorf("%s lists behind(%s) and does not list %s under runs", key, name, name)
				}
				if probedBy[key] == "" {
					t.Errorf("%s lists behind(%s), and no harness of probedBy hands it values whose Close and other undeclared methods fail", key, name)
				}
			}
		}
	}
	if found < 6 {
		t.Errorf("only %d shipped entries list behind of a parameter", found)
	}
	for _, method := range []string{"Close", "Flush"} {
		if !slices.Contains(lookedFor, method) {
			t.Errorf("the probes do not refuse %s", method)
		}
	}
}
