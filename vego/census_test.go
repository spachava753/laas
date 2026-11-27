package vego

import (
	"bufio"
	"encoding/json"
	"fmt"
	"go/ast"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"

	"golang.org/x/tools/go/analysis"
	"golang.org/x/tools/go/analysis/checker"
	"golang.org/x/tools/go/packages"
)

// classifiers are the functions whose result a place that refuses may hand
// unsupported as its class, besides a constant and withDetail of one.
var classifiers = map[string]bool{
	"typeClass": true, "elemClass": true, "mapClass": true, "stmtClass": true, "rangeClass": true, "unusableClass": true, "fieldClass": true, "pointerClass": true, "makeClass": true,
	"addressClass": true, "callClass": true, "varClass": true, "exprClass": true, "ownerClass": true, "funcValueClass": true,
}

// TestRefusalClasses holds every place in the verifier that refuses to a
// class: each call of unsupported and each unsupported value names a class
// of the table, withDetail of one, or the result of a classifier; every
// class of the table is used and described.
func TestRefusalClasses(t *testing.T) {
	parallel(t)
	fset := token.NewFileSet()
	files, err := filepath.Glob("*.go")
	if err != nil {
		t.Fatal(err)
	}
	declared := map[string]bool{}
	described := map[string]bool{}
	used := map[string]bool{}
	sites, reports := 0, 0
	var parsed []*ast.File
	for _, name := range files {
		if strings.HasSuffix(name, "_test.go") {
			continue
		}
		file, err := parser.ParseFile(fset, name, nil, 0)
		if err != nil {
			t.Fatal(err)
		}
		parsed = append(parsed, file)
		for _, decl := range file.Decls {
			gen, ok := decl.(*ast.GenDecl)
			if !ok {
				continue
			}
			for _, spec := range gen.Specs {
				value, ok := spec.(*ast.ValueSpec)
				if !ok {
					continue
				}
				if id, ok := value.Type.(*ast.Ident); ok && id.Name == "refusal" && gen.Tok == token.CONST {
					for _, n := range value.Names {
						declared[n.Name] = true
					}
				}
				if len(value.Names) == 1 && value.Names[0].Name == "refusalClasses" {
					for _, elt := range value.Values[0].(*ast.CompositeLit).Elts {
						kv := elt.(*ast.KeyValueExpr)
						text := kv.Value.(*ast.BasicLit).Value
						// A class says in parentheses where the roadmap
						// plans what lifts it.
						if len(text) < 12 || !strings.Contains(text, "not a cause") && !strings.Contains(text, "(") {
							t.Errorf("%s: the class %s has no description that names where the roadmap plans it", fset.Position(kv.Pos()), kv.Key.(*ast.Ident).Name)
						}
						described[kv.Key.(*ast.Ident).Name] = true
					}
				}
			}
		}
	}
	// funcs holds the functions and literals of the files, innermost last,
	// with whether each has a parameter named class.
	type scope struct {
		from, to token.Pos
		class    bool
	}
	var funcs []scope
	for _, file := range parsed {
		ast.Inspect(file, func(n ast.Node) bool {
			var ft *ast.FuncType
			switch n := n.(type) {
			case *ast.FuncDecl:
				ft = n.Type
			case *ast.FuncLit:
				ft = n.Type
			}
			if ft != nil {
				has := false
				for _, field := range ft.Params.List {
					for _, name := range field.Names {
						has = has || name.Name == "class"
					}
				}
				funcs = append(funcs, scope{n.Pos(), n.End(), has})
			}
			return true
		})
	}
	// passedOn reports whether the class at a position is a parameter of
	// the innermost function around it, which refuses on behalf of its
	// caller and is held to it where that calls it.
	passedOn := func(at token.Pos) bool {
		inner := scope{}
		for _, f := range funcs {
			if f.from <= at && at < f.to && f.from >= inner.from {
				inner = f
			}
		}
		return inner.class
	}
	// check reports a class argument that is none of the accepted forms.
	var check func(e ast.Expr, at token.Pos)
	check = func(e ast.Expr, at token.Pos) {
		switch e := e.(type) {
		case *ast.Ident:
			if e.Name == "class" && passedOn(at) {
				return
			}
			if !declared[e.Name] {
				t.Errorf("%s: %s is not a class of the table", fset.Position(at), e.Name)
			}
			used[e.Name] = true
			return
		case *ast.SelectorExpr:
			if e.Sel.Name == "class" {
				// A refusal passed on from where it was made.
				return
			}
		case *ast.CallExpr:
			name := ""
			switch fun := e.Fun.(type) {
			case *ast.Ident:
				name = fun.Name
			case *ast.SelectorExpr:
				name = fun.Sel.Name
			}
			if name == "withDetail" {
				check(e.Args[0], at)
				return
			}
			if classifiers[name] {
				return
			}
		}
		t.Errorf("%s: the class of this refusal is %s, which is neither a class of the table nor a classifier's result",
			fset.Position(at), types.ExprString(e))
	}
	for _, file := range parsed {
		ast.Inspect(file, func(n ast.Node) bool {
			switch n := n.(type) {
			case *ast.CallExpr:
				if sel, ok := n.Fun.(*ast.SelectorExpr); ok && sel.Sel.Name == "unsupported" {
					sites++
					if len(n.Args) != 3 {
						t.Errorf("%s: unsupported takes a position, a class, and a message", fset.Position(n.Pos()))
						return true
					}
					check(n.Args[1], n.Pos())
				}
				// Every report says what it is: an obligation, a fault of an
				// annotation, or a refusal with its class.
				name := ""
				switch fun := n.Fun.(type) {
				case *ast.SelectorExpr:
					name = fun.Sel.Name
					// The ownership walk's refusals, reported later.
					if x, ok := fun.X.(*ast.Ident); ok && x.Name == "fl" && name == "refuse" {
						name = "report"
					}
				case *ast.Ident:
					name = fun.Name
				}
				if name == "report" || name == "fault" {
					reports++
					if len(n.Args) < 3 {
						t.Errorf("%s: report takes a position, a class, and a message", fset.Position(n.Pos()))
						return true
					}
					check(n.Args[1], n.Pos())
				}
			case *ast.CompositeLit:
				if id, ok := n.Type.(*ast.Ident); ok && id.Name == "unsupported" {
					found := false
					for i, elt := range n.Elts {
						if kv, ok := elt.(*ast.KeyValueExpr); ok && kv.Key.(*ast.Ident).Name == "class" {
							check(kv.Value, n.Pos())
							found = true
						} else if id, isID := elt.(*ast.Ident); !ok && i == 2 && isID && id.Name == "class" {
							// unsupported itself, which passes its class on.
							found = true
						} else if !ok && i == 2 {
							check(elt, n.Pos())
							found = true
						}
					}
					if !found {
						t.Errorf("%s: an unsupported value without a class", fset.Position(n.Pos()))
					}
				}
			case *ast.FuncDecl:
				// What the classifiers return, and the events the census
				// notes itself, count as used.
				if n.Body != nil {
					ast.Inspect(n.Body, func(m ast.Node) bool {
						if id, ok := m.(*ast.Ident); ok && declared[id.Name] {
							used[id.Name] = true
						}
						return true
					})
				}
			}
			return true
		})
	}
	if sites < 250 || reports < 170 {
		t.Fatalf("only %d places that refuse and %d that report were found", sites, reports)
	}
	for name := range declared {
		if !described[name] {
			t.Errorf("the class %s is not in refusalClasses", name)
		}
		if !used[name] {
			t.Errorf("the class %s is used by no place that refuses", name)
		}
	}
	for class := range proofClasses {
		if !strings.HasSuffix(refusalClasses[class], "made only when a proof fails") {
			t.Errorf("the class %s is made only when a proof fails, and its description does not say so", class)
		}
	}
	for class, text := range refusalClasses {
		if strings.HasSuffix(text, "made only when a proof fails") && !proofClasses[class] {
			t.Errorf("the class %s says it is made only when a proof fails, and is not among proofClasses", class)
		}
	}
	if len(refusalClasses) != len(declared) {
		t.Errorf("refusalClasses has %d entries for %d classes", len(refusalClasses), len(declared))
	}
	seen := map[string]bool{}
	for class := range refusalClasses {
		if strings.Contains(string(class), "|") || !strings.Contains(string(class), ":") || seen[string(class)] {
			t.Errorf("the class %q is not of the form group:kind, or is there twice", class)
		}
		seen[string(class)] = true
	}
}

// TestLayoutClasses checks typeClass on a type of every kind layoutOf has no
// layout for, and that it never falls through to type:other for a type
// built of what Go source can name.
func TestLayoutClasses(t *testing.T) {
	parallel(t)
	const src = `package p

import "unsafe"

type S struct{ a [4]int32 }
type E interface{ error; M() }
type G[T any] struct{ x T }

var (
	pUintptr uintptr
	pComplex complex128
	pUnsafe unsafe.Pointer
	pChan chan int
	pPtrSlice *[]int
	pPtrMap *map[string]int
	pPtrPtr **S
	pPtrArray *[4]int
	pPtrIface *error
	pPtrFunc *func()
	pArrayStrings [3]string
	pArrayStruct S
	pPtrArrayStruct *S
	pMapKey map[*S]int
	pMapStruct map[struct{ x int }]bool
	pIface interface{ E }
	pErrorIface E
	pMapFloat map[float64]int
	pMapArray map[[2]int]int
	pMapIface map[any]int
	pArrayPointers [2]*S
	pArrayArrays [2][2]int
	pArrayStructs [2]struct{ x int }
	pArrayIfaces [2]any
	pBigStruct struct{ big [64]uint64 }
)

func Generic[T any](x T, p *T) {}
`
	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "p.go", src, 0)
	if err != nil {
		t.Fatal(err)
	}
	pkg, err := (&types.Config{Importer: importer.Default()}).Check("p", fset, []*ast.File{file}, nil)
	if err != nil {
		t.Fatal(err)
	}
	want := map[string]refusal{
		"pUintptr": rTypeUintptr, "pComplex": rTypeComplex, "pUnsafe": rTypeUnsafe, "pChan": rChannel,
		"pPtrSlice": rPointerTo, "pPtrMap": rPointerTo, "pPtrPtr": rPointerTo, "pPtrArray": rPointerToArray, "pPtrIface": rPointerTo, "pPtrFunc": rPointerTo,
		"pArrayStrings": rTypeArray, "pArrayStruct": rTypeArrayStruct, "pPtrArrayStruct": rTypeArrayStruct,
		"pMapKey": rTypeMapKey, "pMapStruct": rTypeMapKey, "pIface": rTypeIface, "pErrorIface": rTypeIface,
		"pMapFloat": rTypeMapKey, "pMapArray": rTypeMapKey, "pMapIface": rTypeMapKey,
		"pArrayPointers": rTypeArray, "pArrayArrays": rTypeArray, "pArrayStructs": rTypeArray, "pArrayIfaces": rTypeArray,
		"pBigStruct": rTypeArrayStruct,
	}
	for name, class := range want {
		typ := pkg.Scope().Lookup(name).Type()
		if _, ok := layoutOf(typ); ok {
			t.Errorf("%s: %s has a layout", name, typ)
			continue
		}
		if got := typeClass(typ); got != withDetail(class, typ.String()) {
			t.Errorf("%s: typeClass(%s) = %q, want %s with the type as detail", name, typ, got, class)
		}
	}
	generic := pkg.Scope().Lookup("Generic").Type().(*types.Signature)
	for param := range generic.Params().Variables() {
		// layoutOf gives a type parameter itself the layout of an
		// interface value; a pointer to one has none.
		if _, ok := layoutOf(param.Type()); ok {
			continue
		}
		if got := typeClass(param.Type()).class(); got != string(rGenericTypeParam) {
			t.Errorf("typeClass(%s) = %s, want %s", param.Type(), got, rGenericTypeParam)
		}
	}
	if got := elemClass(pkg.Scope().Lookup("pArrayStrings").Type()).class(); got != string(rTypeArrayElem) {
		t.Errorf("elemClass of an array = %s, want %s", got, rTypeArrayElem)
	}
	// Every type of the standard library's unsafe-free packages that has no
	// layout gets a class other than type:other.
	checked := 0
	for _, path := range []string{"net/http", "os", "sync", "reflect", "go/types", "encoding/json", "time"} {
		lib, err := importer.Default().Import(path)
		if err != nil {
			t.Fatal(err)
		}
		for _, name := range lib.Scope().Names() {
			obj := lib.Scope().Lookup(name)
			var types_ []types.Type
			types_ = append(types_, obj.Type())
			if named, ok := obj.Type().(*types.Named); ok {
				if s, ok := named.Underlying().(*types.Struct); ok {
					for field := range s.Fields() {
						types_ = append(types_, field.Type())
					}
				}
			}
			for _, typ := range types_ {
				if _, ok := layoutOf(typ); ok {
					continue
				}
				checked++
				if typeClass(typ).class() == string(rTypeOther) {
					if _, isTuple := typ.(*types.Tuple); !isTuple && !slices.Contains([]string{"invalid type"}, typ.String()) {
						t.Errorf("%s.%s: typeClass(%s) is %s", path, name, typ, rTypeOther)
					}
				}
			}
		}
	}
	if checked < 50 {
		t.Errorf("only %d types without a layout were met", checked)
	}
}

// censusRun runs the analyzer on packages of testdata/census with the
// given flags, and returns the diagnostics.
func censusCorpus(t *testing.T, flags map[string]string, patterns ...string) []string {
	t.Helper()
	diagnostics, failed := censusTrial(t, flags, patterns...)
	for _, err := range failed {
		t.Fatal(err)
	}
	return diagnostics
}

// censusTrial is censusCorpus, which returns what failed.
func censusTrial(t *testing.T, flags map[string]string, patterns ...string) (diagnostics []string, failed []error) {
	t.Helper()
	root, err := filepath.Abs(filepath.Join("testdata", "census"))
	if err != nil {
		t.Fatal(err)
	}
	analyzer := newAnalyzer()
	for name, value := range flags {
		if err := analyzer.Flags.Set(name, value); err != nil {
			t.Fatal(err)
		}
	}
	config := &packages.Config{
		Mode: packages.LoadAllSyntax,
		Dir:  filepath.Join(root, "src"),
		Env:  append(os.Environ(), "GOPATH="+root, "GO111MODULE=off", "GOPROXY=off", "GOWORK=off"),
	}
	loaded, err := packages.Load(config, patterns...)
	if err != nil {
		t.Fatalf("load packages: %v", err)
	}
	if packages.PrintErrors(loaded) > 0 {
		t.Fatal("the test packages do not compile")
	}
	graph, err := checker.Analyze([]*analysis.Analyzer{analyzer}, loaded, nil)
	if err != nil {
		t.Fatal(err)
	}
	// The first package that fails says why; those that import it fail
	// for it.
	for action := range graph.All() {
		if action.Err != nil && !strings.Contains(action.Err.Error(), "failed prerequisites") {
			failed = append(failed, fmt.Errorf("analysis of %s failed: %v", action.Package.PkgPath, action.Err))
		}
	}
	for _, action := range graph.Roots {
		if action.Err != nil && len(failed) == 0 {
			failed = append(failed, fmt.Errorf("analysis of %s failed: %v", action.Package.PkgPath, action.Err))
		}
		for _, d := range action.Diagnostics {
			diagnostics = append(diagnostics, d.Message)
		}
	}
	return diagnostics, failed
}

// TestCensus runs the census on testdata/census and holds each function to
// what it must report: the classes of its causes, what it assumed, and
// whether it was looked at in full; and the first cause of each function
// of census/first, which carries the weakest contract in source, to the
// refusal the ordinary run makes of it.
func TestCensus(t *testing.T) {
	parallel(t)
	out := filepath.Join(t.TempDir(), "census.jsonl")
	// No Z3 may start: the path named is none.
	if got := censusCorpus(t, map[string]string{"census": out, "census-scope": "census", "z3": "/nonexistent/z3", "cache": ""}, "census/..."); len(got) > 0 {
		t.Fatalf("a census reports nothing, and it reported %q", got)
	}
	f, err := os.Open(out)
	if err != nil {
		t.Fatal(err)
	}
	defer f.Close()
	lines := map[string]censusLine{}
	scanner := bufio.NewScanner(f)
	scanner.Buffer(nil, 1<<20)
	for scanner.Scan() {
		var line censusLine
		if err := json.Unmarshal(scanner.Bytes(), &line); err != nil {
			t.Fatal(err)
		}
		lines[line.Package+"."+line.Function] = line
	}
	kinds := func(line censusLine, kind string) []string {
		var classes []string
		for _, e := range line.Events {
			if e.Kind == kind && !slices.Contains(classes, e.Class) {
				classes = append(classes, e.Class)
			}
		}
		slices.Sort(classes)
		return classes
	}
	type want struct {
		causes, assumed, annotate string
		partial, stopped          bool
	}
	wants := map[string]want{
		"census/through.add":               {},
		"census/through.Sum":               {assumed: "assumed:module"},
		"census/through.Index":             {},
		"census/through.Each":              {annotate: "annotate:calls"},
		"census/through.Total":             {assumed: "assumed:calls assumed:module"},
		"census/through.(*file).Next":      {},
		"census/through.Drain":             {assumed: "assumed:module-method"},
		"census/through.Open":              {},
		"census/through.Unreachable":       {},
		"census/through.AfterExit":         {},
		"census/through.Forever":           {},
		"census/through.Exit":              {},
		"census/through.Encode":            {},
		"census/stops.Channel":             {causes: "channel:use"},
		"census/stops.Address":             {causes: "address-of:element address-of:field"},
		"census/stops.Stat":                {causes: "no-entry:std"},
		"census/stops.Goroutine":           {causes: "channel:use goroutine:go"},
		"census/stops.Generic":             {causes: "generic:declared", partial: true, stopped: true},
		"census/stops.HandedThenExit":      {causes: "channel:use"},
		"census/stops.EncodeThenChannel":   {causes: "channel:use"},
		"census/stops.Twice":               {causes: "channel:use"},
		"census/stops.UnusableThenChannel": {causes: "channel:use contract:unusable"},
		"census/stops.Wrap":                {causes: "scoped:kept"},
		"census/stops.Feed":                {causes: "channel:use"},
		"census/stops.itoa":                {},
		"census/stops.Hidden":              {causes: "address-of:field no-entry:std", assumed: "assumed:module"},
		"census/stops.HiddenDecl":          {causes: "address-of:field no-entry:std", assumed: "assumed:module"},
		"census/stops.Boxed":               {causes: "closure:recursive", assumed: "assumed:closure"},
		"census/stops.AddrSlice":           {causes: "pointer:to-non-struct"},
		"census/through.Closure":           {},
		"census/stops.Exists":              {causes: "no-entry:std"},
		"census/stops.g":                   {},
		"census/stops.Switch":              {causes: "channel:use", assumed: "assumed:module"},
		"census/stops.Loop":                {causes: "channel:use", assumed: "assumed:module"},
		"census/stops.twoResults":          {},
		"census/stops.mustOf":              {},
		"census/stops.MustPair":            {causes: "call:multi-value-args", assumed: "assumed:module"},
		"census/stops.Map":                 {causes: "generic:declared", partial: true, stopped: true},
		"census/stops.double":              {},
		"census/stops.Doubles":             {causes: "generic:called"},
		"census/stops.Upper":               {causes: "no-entry:other"},
		"census/stops.Broken":              {causes: "annotation:broken", partial: true, stopped: true},
		"census/first.Address":             {causes: "address-of:field"},
		"census/first.Stat":                {causes: "no-entry:std"},
		"census/first.Channel":             {causes: "channel:use"},
		"census/first.Mixed":               {causes: "channel:use goroutine:go"},
	}
	for name, w := range wants {
		line, ok := lines[name]
		if !ok {
			t.Errorf("%s has no line", name)
			continue
		}
		got := want{causes: strings.Join(kinds(line, "cause"), " "), assumed: strings.Join(kinds(line, "assumed"), " "),
			annotate: strings.Join(kinds(line, "annotate"), " "), partial: line.Unseen > 0, stopped: line.Stopped}
		if got != w {
			t.Errorf("%s: got %+v, want %+v (events %+v, unseen at %v)", name, got, w, line.Events, line.UnseenAt)
		}
	}
	if len(lines) != len(wants) {
		t.Errorf("%d lines for %d functions", len(lines), len(wants))
	}
	// The first cause is the ordinary run's refusal of the same function.
	compared := 0
	for _, d := range censusCorpus(t, map[string]string{"cache": ""}, "census/first") {
		name, msg, ok := strings.Cut(strings.TrimPrefix(d, "vego: cannot verify "), ": ")
		if !ok || !strings.HasPrefix(d, "vego: cannot verify ") {
			continue
		}
		line := lines["census/first."+name]
		first := ""
		for _, e := range line.Events {
			if e.Kind == "cause" || e.Kind == "proof" {
				first = e.Message
				break
			}
		}
		if first != msg {
			t.Errorf("%s: the census's first cause is %q, and the ordinary run's refusal %q", name, first, msg)
		}
		compared++
	}
	if compared != 4 {
		t.Errorf("%d functions of census/first were compared with the ordinary run, not 4", compared)
	}
	// A trust file with a problem ends the census with an error that names
	// it (F20 of the review).
	bad := filepath.Join(t.TempDir(), "vego-trusted.yaml")
	if err := os.WriteFile(bad, []byte("sizes:\n  memory: 256GB\n  reason: a reason\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	_, failed := censusTrial(t, map[string]string{"census": filepath.Join(t.TempDir(), "bad.jsonl"), "census-scope": "census", "trusted": bad, "cache": ""}, "census/through")
	if len(failed) == 0 || !strings.Contains(failed[0].Error(), bad) || !strings.Contains(failed[0].Error(), "version") {
		t.Errorf("a census under a trust file without its version gave %v", failed)
	}
}
