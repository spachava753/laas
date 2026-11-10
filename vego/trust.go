package vego

import (
	"bytes"
	"embed"
	"errors"
	"fmt"
	"go/token"
	"go/types"
	"io"
	"io/fs"
	"maps"
	"os"
	"path/filepath"
	"slices"
	"sort"
	"strings"
	"sync"

	"github.com/spachava753/laas/vego/internal/logic"
	"github.com/spachava753/laas/vego/internal/solver"
	"gopkg.in/yaml.v3"
)

// TrustFileName is the name of the file that holds a module's trusted
// contracts. It sits next to go.mod.
const TrustFileName = "vego-trusted.yaml"

//go:embed trusted/std/*.yaml
var shippedFiles embed.FS

// trustFormula is one requires or ensures entry of a trusted contract.
type trustFormula struct {
	text string
	line int
	col  int
	node *logic.Node
}

// trustEntry is the contract of a function that is not verified: code of
// another module, of the standard library, or of this project where vego
// cannot follow it. Callers must prove what it requires and may assume what
// it ensures.
type trustEntry struct {
	key      string
	reason   string
	requires []trustFormula
	ensures  []trustFormula
	modifies []string
	file     *trustFile
	line     int
}

// trustFile is a parsed file of trusted contracts.
type trustFile struct {
	path    string
	content []byte
	shipped bool
	entries map[string]*trustEntry
	// problems are the defects of the file itself, by line.
	problems []trustProblem
}

type trustProblem struct {
	line int
	msg  string
}

func (f *trustFile) problem(line int, format string, args ...any) {
	f.problems = append(f.problems, trustProblem{line, fmt.Sprintf(format, args...)})
}

// parseTrustFile reads a file of trusted contracts. Anything it does not
// understand is recorded as a problem rather than skipped, so that a
// misspelt field cannot silently drop part of a contract.
func parseTrustFile(path string, content []byte, shipped bool) *trustFile {
	file := &trustFile{path: path, content: content, shipped: shipped, entries: map[string]*trustEntry{}}
	var document, second yaml.Node
	decoder := yaml.NewDecoder(bytes.NewReader(content))
	if err := decoder.Decode(&document); err != nil && !errors.Is(err, io.EOF) {
		file.problem(1, "not valid YAML: %v (a formula containing \": \", or starting with | or !, must be quoted)", err)
		return file
	}
	// A second document would be ignored, and with it whatever it says.
	if err := decoder.Decode(&second); !errors.Is(err, io.EOF) {
		file.problem(max(second.Line, 1), "the file must hold exactly one YAML document")
		return file
	}
	if len(document.Content) == 0 {
		return file
	}
	root := document.Content[0]
	file.rejectDuplicates(root)
	if root.Kind != yaml.MappingNode {
		file.problem(root.Line, "expected a mapping with the keys version and trusted")
		return file
	}
	sawVersion := false
	for i := 0; i+1 < len(root.Content); i += 2 {
		key, value := root.Content[i], root.Content[i+1]
		switch key.Value {
		case "version":
			sawVersion = true
			if value.Value != "1" {
				file.problem(value.Line, "unsupported version %q; this vego understands version 1", value.Value)
			}
		case "trusted":
			if value.Kind != yaml.MappingNode {
				file.problem(value.Line, "trusted must map function names to contracts")
				continue
			}
			for j := 0; j+1 < len(value.Content); j += 2 {
				file.addEntry(value.Content[j], value.Content[j+1])
			}
		default:
			file.problem(key.Line, "unknown key %q; expected version or trusted", key.Value)
		}
	}
	if !sawVersion {
		file.problem(root.Line, "missing \"version: 1\"")
	}
	return file
}

// rejectDuplicates records every mapping key that occurs twice, anywhere in
// the document. YAML libraries keep the last one, which would silently drop
// the clauses of the first.
func (f *trustFile) rejectDuplicates(node *yaml.Node) {
	if node.Kind == yaml.MappingNode {
		seen := map[string]bool{}
		for i := 0; i+1 < len(node.Content); i += 2 {
			key := node.Content[i]
			if seen[key.Value] {
				f.problem(key.Line, "%q occurs more than once in the same mapping", key.Value)
			}
			seen[key.Value] = true
		}
	}
	for _, child := range node.Content {
		f.rejectDuplicates(child)
	}
}

// addEntry reads one contract. The reason is mandatory: it is what lets a
// reviewer tell a checked claim from one written to silence an error.
func (f *trustFile) addEntry(name, body *yaml.Node) {
	entry := &trustEntry{key: name.Value, file: f, line: name.Line}
	if _, duplicate := f.entries[entry.key]; duplicate {
		return
	}
	f.entries[entry.key] = entry
	if body.Kind != yaml.MappingNode {
		f.problem(body.Line, "the entry for %s must be a mapping with a reason", entry.key)
		return
	}
	scalars := func(field string, node *yaml.Node) []*yaml.Node {
		if node.Kind != yaml.SequenceNode {
			f.problem(node.Line, "%s of %s must be a list", field, entry.key)
			return nil
		}
		for _, item := range node.Content {
			if item.Kind != yaml.ScalarNode {
				f.problem(item.Line, "%s of %s must be a list of strings; a formula containing \": \" must be quoted",
					field, entry.key)
				return nil
			}
		}
		return node.Content
	}
	formulas := func(field string, node *yaml.Node) []trustFormula {
		var list []trustFormula
		for _, item := range scalars(field, node) {
			parsed, err := logic.ParseFormula(item.Value)
			if err != nil {
				f.problem(item.Line, "syntax error in %s of %s: %v", field, entry.key, err)
				continue
			}
			list = append(list, trustFormula{item.Value, item.Line, item.Column, parsed})
		}
		return list
	}
	for i := 0; i+1 < len(body.Content); i += 2 {
		field, value := body.Content[i], body.Content[i+1]
		switch field.Value {
		case "reason":
			entry.reason = strings.TrimSpace(value.Value)
		case "requires":
			entry.requires = formulas("requires", value)
		case "ensures":
			entry.ensures = formulas("ensures", value)
		case "modifies":
			for _, item := range scalars("modifies", value) {
				entry.modifies = append(entry.modifies, item.Value)
			}
		default:
			f.problem(field.Line, "unknown field %q in the entry for %s; expected reason, requires, ensures, or modifies",
				field.Value, entry.key)
		}
	}
	if entry.reason == "" {
		f.problem(name.Line, "the entry for %s needs a reason saying why the contract is believed", entry.key)
	}
}

var (
	trustFiles   = map[string]*trustFile{}
	trustFilesMu sync.Mutex
	shippedOnce  sync.Once
	shippedTrust []*trustFile
)

// loadTrustFile reads and caches a trust file. A file that does not exist is
// no file; one that exists but cannot be read is a problem, since falling
// back to the shipped contracts would change what is trusted without notice.
func loadTrustFile(path string) *trustFile {
	trustFilesMu.Lock()
	defer trustFilesMu.Unlock()
	if file, ok := trustFiles[path]; ok {
		return file
	}
	var file *trustFile
	content, err := os.ReadFile(path)
	switch {
	case err == nil:
		file = parseTrustFile(path, content, false)
	case !errors.Is(err, fs.ErrNotExist):
		file = &trustFile{path: path, entries: map[string]*trustEntry{}}
		file.problem(1, "cannot read the trust file: %v", err)
	}
	trustFiles[path] = file
	return file
}

// shippedContracts returns the contracts that come with vego.
func shippedContracts() []*trustFile {
	shippedOnce.Do(func() {
		names, _ := shippedFiles.ReadDir("trusted/std")
		for _, name := range names {
			path := "trusted/std/" + name.Name()
			content, _ := shippedFiles.ReadFile(path)
			shippedTrust = append(shippedTrust, parseTrustFile("vego/"+path, content, true))
		}
	})
	return shippedTrust
}

// projectTrustPath locates the trust file of the module a source file
// belongs to: the one next to the nearest go.mod above it.
func projectTrustPath(sourceFile string) string {
	for dir := filepath.Dir(sourceFile); ; dir = filepath.Dir(dir) {
		if _, err := os.Stat(filepath.Join(dir, "go.mod")); err == nil {
			return filepath.Join(dir, TrustFileName)
		}
		if dir == filepath.Dir(dir) {
			return ""
		}
	}
}

// Usage is the result of analysing one package: which trusted contracts
// its proofs, and the proofs of the packages it depends on, rest on. The
// trust report is built from the usages of the analysed packages.
type Usage struct {
	// ProjectKeys lists, for each project trust file seen, all its entries,
	// used or not.
	ProjectKeys map[string][]string
	// Entries holds the contracts used.
	Entries []*EntryUse
	// Constructors holds the calls to errors.New and fmt.Errorf, whose
	// non-nil result vego knows without a contract.
	Constructors []token.Position
}

// EntryUse describes one trusted contract and where it is relied on. Two
// trust files may each have a contract for the same function; the file is
// part of what identifies a contract.
type EntryUse struct {
	Key     string
	Reason  string
	Shipped bool
	File    string
	Line    int
	// Unpredictable is set when the function returns an error and its
	// contract never says that it succeeds.
	Unpredictable bool
	Calls         []token.Position
}

// add merges another usage into u.
func (u *Usage) add(other *Usage) {
	for file, keys := range other.ProjectKeys {
		if u.ProjectKeys == nil {
			u.ProjectKeys = map[string][]string{}
		}
		u.ProjectKeys[file] = keys
	}
	for _, position := range other.Constructors {
		if !slices.Contains(u.Constructors, position) {
			u.Constructors = append(u.Constructors, position)
		}
	}
	for _, use := range other.Entries {
		index := slices.IndexFunc(u.Entries, func(known *EntryUse) bool {
			return known.Key == use.Key && known.File == use.File
		})
		if index < 0 {
			copied := *use
			copied.Calls = nil
			u.Entries = append(u.Entries, &copied)
			index = len(u.Entries) - 1
		}
		merged := u.Entries[index]
		merged.Unpredictable = merged.Unpredictable || use.Unpredictable
		for _, call := range use.Calls {
			if !slices.Contains(merged.Calls, call) {
				merged.Calls = append(merged.Calls, call)
			}
		}
	}
}

// usageFact publishes the usage of a package to the packages that import
// it, whose proofs rest on the same contracts through it.
type usageFact struct {
	Usage Usage
}

func (*usageFact) AFact() {}

func (f *usageFact) String() string { return fmt.Sprintf("usage(%d contracts)", len(f.Usage.Entries)) }

// trustPos converts a line and column of a trust file to a position, adding
// the file to the file set on first use so that diagnostics can point at it.
func (pv *pkgVerifier) trustPos(file *trustFile, line, col int) token.Pos {
	registered, ok := pv.trustSources[file]
	if !ok {
		registered = pv.pass.Fset.AddFile(file.path, -1, len(file.content))
		registered.SetLinesForContent(file.content)
		pv.trustSources[file] = registered
	}
	if line < 1 || line > registered.LineCount() {
		return registered.Pos(0)
	}
	return registered.LineStart(line) + token.Pos(max(col-1, 0))
}

// loadTrust finds the trust files that apply to the package and reports the
// defects of the project's file.
func (pv *pkgVerifier) loadTrust(explicit string) {
	path := explicit
	if path == "" && len(pv.pass.Files) > 0 {
		path = projectTrustPath(pv.pass.Fset.Position(pv.pass.Files[0].Pos()).Filename)
	}
	pv.usage = &Usage{}
	if path != "" {
		pv.projectTrust = loadTrustFile(path)
	}
	if pv.projectTrust == nil {
		if explicit != "" {
			pv.report(pv.pass.Files[0].Pos(), "cannot read the trust file %s", explicit)
		}
		return
	}
	keys := slices.Sorted(maps.Keys(pv.projectTrust.entries))
	pv.usage.ProjectKeys = map[string][]string{path: keys}
	for _, problem := range pv.projectTrust.problems {
		pv.report(pv.trustPos(pv.projectTrust, problem.line, 1), "%s", problem.msg)
	}
	visible := map[string]*types.Package{}
	var visit func(pkg *types.Package)
	visit = func(pkg *types.Package) {
		if _, seen := visible[pkg.Path()]; seen {
			return
		}
		visible[pkg.Path()] = pkg
		for _, imported := range pkg.Imports() {
			visit(imported)
		}
	}
	visit(pv.pass.Pkg)
	for _, key := range keys {
		entry := pv.projectTrust.entries[key]
		if pkg, name, ok := splitFuncName(key); ok && visible[pkg] != nil && !declares(visible[pkg], name) {
			pv.report(pv.trustPos(pv.projectTrust, entry.line, 1),
				"the trusted contract names %s, but package %s has no such function", key, pkg)
		}
	}
}

// splitFuncName splits the full name of a function or method, as Go prints
// it, into its package path and the rest: "sort.Ints" gives "sort" and
// "Ints"; "(*bytes.Buffer).Len" gives "bytes" and "(*Buffer).Len".
func splitFuncName(key string) (pkg, name string, ok bool) {
	receiver, method, isMethod := strings.Cut(strings.TrimPrefix(key, "("), ").")
	qualified := key
	if isMethod {
		qualified = strings.TrimPrefix(receiver, "*")
	}
	dot := strings.LastIndex(qualified, ".")
	if dot < 0 {
		return "", "", false
	}
	pkg, name = qualified[:dot], qualified[dot+1:]
	if isMethod {
		name = "(" + strings.Repeat("*", len(receiver)-len(qualified)) + name + ")." + method
	}
	return pkg, name, true
}

// declares reports whether a package declares the function or method that
// splitFuncName named.
func declares(pkg *types.Package, name string) bool {
	receiver, method, isMethod := strings.Cut(strings.TrimPrefix(name, "("), ").")
	if !isMethod {
		_, ok := pkg.Scope().Lookup(name).(*types.Func)
		return ok
	}
	typeName, ok := pkg.Scope().Lookup(strings.TrimPrefix(receiver, "*")).(*types.TypeName)
	if !ok {
		return false
	}
	found, _, _ := types.LookupFieldOrMethod(types.NewPointer(typeName.Type()), true, pkg, method)
	_, ok = found.(*types.Func)
	return ok
}

// trustedContract returns the trusted contract of a function as a funcInfo,
// or nil when it has none. A project entry replaces a shipped one. The
// contract is checked against the real signature on first use: its names
// must be parameters and results of the right types, modifies may only list
// slice parameters, and the contract must not contradict itself.
func (pv *pkgVerifier) trustedContract(callee *types.Func) *funcInfo {
	if fn, done := pv.trusted[callee]; done {
		return fn
	}
	key := callee.FullName()
	var entry *trustEntry
	if pv.projectTrust != nil {
		entry = pv.projectTrust.entries[key]
	}
	for _, file := range shippedContracts() {
		if entry == nil {
			entry = file.entries[key]
		}
	}
	if entry == nil {
		pv.trusted[callee] = nil
		return nil
	}
	fn := newFuncInfo(callee)
	fn.trust = entry
	pv.trusted[callee] = fn
	if entry.file.shipped {
		// A shipped file with a defect is a bug in vego; surface it.
		for _, problem := range entry.file.problems {
			fn.defect("%s", problem.msg)
		}
	}
	clauses := func(kind string, formulas []trustFormula) []*clause {
		var list []*clause
		for _, formula := range formulas {
			list = append(list, &clause{
				kind: kind, text: formula.text, node: formula.node,
				pos: pv.trustPos(entry.file, formula.line, formula.col),
			})
		}
		return list
	}
	fn.requires, fn.ensures = clauses("requires", entry.requires), clauses("ensures", entry.ensures)
	// A trusted contract means the same wherever it is used, so it may not
	// mention the predicates or constants of whichever package calls it.
	for _, c := range slices.Concat(fn.requires, fn.ensures) {
		c.res = pv.plain
	}
	fn.modifies = map[*types.Var]bool{}
	for _, name := range entry.modifies {
		param, ok := fn.paramNames[name]
		if !ok || !isSlice(param.Type()) {
			fn.defect("its modifies lists %s, which is not a slice parameter of the function", name)
			continue
		}
		fn.modifies[param] = true
	}
	pv.checkTrusted(fn)
	return fn
}

// defect records that a trusted contract is unusable. Defects are reported
// where the contract is used, which is where the proof would have relied on
// it.
func (fn *funcInfo) defect(format string, args ...any) {
	fn.defects = append(fn.defects, fmt.Sprintf(format, args...))
	fn.broken = true
}

// checkTrusted resolves a trusted contract against the function's signature
// and rejects one that contradicts itself, from which anything would follow.
func (pv *pkgVerifier) checkTrusted(fn *funcInfo) {
	args := map[*types.Var]*logic.Term{}
	post := map[*types.Var]*logic.Term{}
	var facts []*logic.Term
	for i, param := range fn.params {
		sort, ok := sortOf(param.Type())
		if !ok {
			// A parameter of a type vego does not model cannot be named.
			delete(fn.paramNames, param.Name())
			continue
		}
		args[param] = logic.Const(fmt.Sprintf("in@%d", i), sort)
		post[param] = args[param]
		if fn.modifies[param] {
			post[param] = logic.Const(fmt.Sprintf("out@%d", i), sort)
			facts = append(facts, logic.Eq(logic.Len(post[param]), logic.Len(args[param])))
		}
		facts = append(facts, pv.valueFacts(args[param], param.Type()), pv.valueFacts(post[param], param.Type()))
	}
	results := make([]*logic.Term, len(fn.results))
	for i, result := range fn.results {
		if sort, ok := sortOf(result.Type()); ok {
			results[i] = logic.Const(fmt.Sprintf("result@%d", i), sort)
			facts = append(facts, pv.valueFacts(results[i], result.Type()))
		}
	}
	resolve := func(c *clause, env *contractEnv) {
		formula, err := pv.resolverOf(c).Formula(c.node, &partialEnv{env})
		if err != nil {
			fn.defect("in its %s %q: %v", c.kind, c.text, err)
			return
		}
		facts = append(facts, formula)
	}
	for _, c := range fn.requires {
		resolve(c, &contractEnv{pv: pv, fn: fn, args: args})
	}
	for _, c := range fn.ensures {
		resolve(c, &contractEnv{pv: pv, fn: fn, args: args, post: post, results: results})
	}
	opts := solver.Options{Preds: pv.res.Preds, MaxSteps: pv.maxSteps}
	if !fn.broken && solver.Prove(facts, logic.False(), opts) == solver.Proved {
		fn.defect("it contradicts itself, so anything could be proved from it")
	}
}

// valueFacts states everything a value's Go type guarantees, including, for
// a slice or string, that every element is a value of the element type.
func (pv *pkgVerifier) valueFacts(value *logic.Term, t types.Type) *logic.Term {
	fact := pv.typeFact(value, t)
	if !value.Sort.IsSeq() {
		return fact
	}
	var elementType types.Type = types.Typ[types.Uint8]
	if isSlice(t) {
		elementType = t.Underlying().(*types.Slice).Elem()
	}
	index := logic.Bound("k#"+value.Name, logic.Int)
	inRange := logic.And(logic.Le(logic.IntLit(0), index), logic.Lt(index, logic.Len(value)))
	return logic.And(fact, logic.Forall(index, logic.Implies(inRange, pv.typeFact(logic.Select(value, index), elementType))))
}

// noteUse records that a proof relies on a trusted contract.
func (pv *pkgVerifier) noteUse(fn *funcInfo, at token.Pos) {
	entry := fn.trust
	index := slices.IndexFunc(pv.usage.Entries, func(use *EntryUse) bool {
		return use.Key == entry.key && use.File == entry.file.path
	})
	if index < 0 {
		pv.usage.Entries = append(pv.usage.Entries, &EntryUse{
			Key: entry.key, Reason: entry.reason, Shipped: entry.file.shipped,
			File: entry.file.path, Line: entry.line,
		})
		index = len(pv.usage.Entries) - 1
	}
	use := pv.usage.Entries[index]
	position := pv.pass.Fset.Position(at)
	if !slices.Contains(use.Calls, position) {
		use.Calls = append(use.Calls, position)
		sort.Slice(use.Calls, func(i, j int) bool { return use.Calls[i].String() < use.Calls[j].String() })
	}
	fn.use = use
}
