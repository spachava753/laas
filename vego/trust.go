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
	"math/big"
	"os"
	"path/filepath"
	"regexp"
	"slices"
	"sort"
	"strings"
	"sync"

	"github.com/spachava753/laas/vego/internal/logic"
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
	key    string
	reason string
	// initialiserOnly marks an entry whose claims hold only for a call that
	// the initialiser of a package-level variable makes itself, outside
	// every function: a panic there stops the program, or the plugin that
	// holds the package, before any code reads the variable (D4 of F31, F5
	// of the design review of F32).
	initialiserOnly bool
	// isolated is the claim that the function runs no code but what the
	// call hands it through its arguments and receiver, and reaches no code
	// through memory that another call set, also not through any function
	// it calls (F11 of the review of the design of F32). A call of it that
	// is handed no code reaches no code of the calling package.
	isolated bool
	// exits is the claim that the function may end the process as os.Exit
	// does, without returning and without running a deferred call; with
	// an ensures that is the single clause False, that it never returns.
	// See exits.go.
	exits    bool
	requires []trustFormula
	// declared holds what a call must also meet under a declared memory,
	// formulas that may name Memory, the bytes declared; only the shipped
	// files have it, for the functions that reserve by a number (sizes.go).
	declared []trustFormula
	ensures  []trustFormula
	modifies []trustFormula
	// runs names the parameters whose code the function may run: methods
	// of an error or an interface, or a function, held in them.
	runs []trustFormula
	// vouches names the error results whose errors the author vouches
	// for; see knownError.
	vouches []trustFormula
	// formats names the parameters the function formats as package fmt
	// does: one of type any or ...any whose values it formats, and at most
	// one string that it uses as the format; see formatting.go.
	formats []trustFormula
	// encodes names the parameter of type any whose value the function
	// encodes as package encoding/json does; see json.go.
	encodes []trustFormula
	// decodes names the parameter of type any into which the function
	// decodes as package encoding/json does; see jsondecode.go.
	decodes []trustFormula
	// calls gives function parameters a contract: how the function calls
	// what it is given there.
	calls []trustCall
	// keeps names the parameters whose code the function keeps, each with
	// where it keeps it: results, or other parameters whose memory it
	// writes; see keeps.go.
	keeps []trustKeep
	// asserts names, for parameters that hold code, what the function may
	// find on what they hold by a type assertion; see asserts.go.
	asserts []trustKeep
	// receiver names the receiver of a method of an interface, so that the
	// contract can speak of its states; see ifacestate.go.
	receiver trustFormula
	// prints names the writer a function that formats writes to, and the
	// function whose result it writes; see prints.go.
	prints []trustKeep
	// stores names the parameters under whose memory, as modifies lists
	// it, the function stores only memory it made during the call; see
	// memorigins.go.
	stores []trustFormula
	file   *trustFile
	line   int
}

// trustCall is one entry under calls: a function parameter, names for the
// parameters of its function type, and what holds whenever the trusted
// function calls it.
type trustCall struct {
	name     string
	params   []string
	requires []trustFormula
	// deterministic says that the function relies on what it is handed
	// returning the same result whenever it is called with the same
	// arguments.
	deterministic bool
	line          int
	col           int
}

// trustKeep is one entry under keeps: a parameter and the results and
// parameters in which the function keeps the code it holds.
type trustKeep struct {
	name  string
	dests []trustFormula
	line  int
	col   int
}

// callShape reads the key of an entry under calls, as in f(i) or less(i, j).
var callShape = regexp.MustCompile(`^([A-Za-z_][A-Za-z0-9_]*)\(\s*((?:[A-Za-z_][A-Za-z0-9_]*)(?:\s*,\s*[A-Za-z_][A-Za-z0-9_]*)*)?\s*\)$`)

// trustFile is a parsed file of trusted contracts.
type trustFile struct {
	path    string
	content []byte
	shipped bool
	// isolated is set when the file claims of every function and method of
	// the package it covers what isolated claims of one entry, and
	// isolatedReason says what supports it; see trustEntry.isolated.
	isolated       bool
	isolatedReason string
	// sizes is the file's declaration of the memory of the machines the
	// program runs on, or nil; see sizes.go.
	sizes   *sizesDecl
	entries map[string]*trustEntry
	// states holds the states the file declares, by the type they belong
	// to, as in sync.Mutex. Only the shipped files may declare one of a
	// struct type; a project file may declare those of an interface of
	// another module.
	states map[string][]stateDecl
	// owns holds, by type, the fields whose memory a value of the type
	// owns; only the shipped files declare any. See footprint.go.
	owns map[string]ownsDecl
	// scoped and hidden hold the scoped interface types and the hidden
	// fields of struct types that the shipped files declare; see
	// scoped.go.
	scoped map[string]scopedDecl
	hidden map[string]hiddenDecl
	// notWritten holds fields that verified code reads but does not
	// store into, whose value writes nothing else of the struct; see
	// scoped.go.
	notWritten map[string]hiddenDecl
	// progresses holds fields of a struct whose value, a reader that code
	// which is not verified made, returns bytes or an error from every Read
	// with a buffer that is not empty; verified code does not store into
	// them (jsondecode.go).
	progresses map[string]hiddenDecl
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
	file := &trustFile{path: path, content: content, shipped: shipped, entries: map[string]*trustEntry{}, states: map[string][]stateDecl{}, owns: map[string]ownsDecl{}, scoped: map[string]scopedDecl{}, hidden: map[string]hiddenDecl{}, notWritten: map[string]hiddenDecl{}, progresses: map[string]hiddenDecl{}}
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
		case "state":
			file.addStates(value)
		case "owns":
			file.addOwns(value)
		case "scoped":
			file.addScoped(value)
		case "hidden":
			file.addFields("hidden", file.hidden, value)
		case "notWrittenBy":
			file.addFields("notWrittenBy", file.notWritten, value)
		case "progresses":
			file.addFields("progresses", file.progresses, value)
		case "isolated":
			// A claim of the whole package, with what supports it, which
			// the trust report prints.
			if value.Kind != yaml.MappingNode || len(value.Content) != 2 || value.Content[0].Value != "reason" || strings.TrimSpace(value.Content[1].Value) == "" {
				file.problem(value.Line, "isolated must be a mapping with a reason that says what was read to support the claim")
				continue
			}
			file.isolated, file.isolatedReason = true, strings.TrimSpace(value.Content[1].Value)
		case "sizes":
			// An assumption of the project about the machines it runs on
			// (sizes.go), which no shipped file can make for it.
			file.addSizes(key, value)
		default:
			// A project file cannot declare owns, so it is not offered one.
			expected := "version, trusted, state, isolated, or sizes"
			if file.shipped {
				expected = "version, trusted, state, isolated, owns, scoped, hidden, notWrittenBy, or progresses"
			}
			file.problem(key.Line, "unknown key %q; expected %s", key.Value, expected)
		}
	}
	if !sawVersion {
		file.problem(root.Line, "missing \"version: 1\"")
	}
	return file
}

// rejectDuplicates records every mapping key that occurs twice, anywhere in
// the document. YAML libraries keep the last one, which would silently drop
// the clauses of the first. It also rejects aliases, whose node carries the
// name of the anchor instead of the value it stands for.
func (f *trustFile) rejectDuplicates(node *yaml.Node) {
	if node.Kind == yaml.AliasNode {
		f.problem(node.Line, "YAML aliases are not supported; write the value out")
		return
	}
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
	listed := false
	for i := 0; i+1 < len(body.Content); i += 2 {
		field, value := body.Content[i], body.Content[i+1]
		listed = listed || field.Value == "modifies"
		switch field.Value {
		case "reason":
			if value.Kind != yaml.ScalarNode {
				f.problem(value.Line, "the reason of %s must be text", entry.key)
				continue
			}
			entry.reason = strings.TrimSpace(value.Value)
		case "requires":
			entry.requires = formulas("requires", value)
		case "declared":
			if !f.shipped {
				f.problem(field.Line, "declared of %s may be written only in the shipped files of vego", entry.key)
				continue
			}
			for _, item := range scalars("declared", value) {
				parsed, err := logic.ParseFormula(declaredText(item.Value, big.NewInt(1)))
				if err != nil {
					f.problem(item.Line, "syntax error in declared of %s: %v", entry.key, err)
					continue
				}
				entry.declared = append(entry.declared, trustFormula{item.Value, item.Line, item.Column, parsed})
			}
		case "ensures":
			entry.ensures = formulas("ensures", value)
		case "modifies":
			for _, item := range scalars("modifies", value) {
				entry.modifies = append(entry.modifies, trustFormula{text: item.Value, line: item.Line, col: item.Column})
			}
		case "runs":
			for _, item := range scalars("runs", value) {
				entry.runs = append(entry.runs, trustFormula{text: item.Value, line: item.Line, col: item.Column})
			}
		case "vouches":
			for _, item := range scalars("vouches", value) {
				entry.vouches = append(entry.vouches, trustFormula{text: item.Value, line: item.Line, col: item.Column})
			}
		case "stores":
			for _, item := range scalars("stores", value) {
				entry.stores = append(entry.stores, trustFormula{text: item.Value, line: item.Line, col: item.Column})
			}
		case "formats":
			for _, item := range scalars("formats", value) {
				entry.formats = append(entry.formats, trustFormula{text: item.Value, line: item.Line, col: item.Column})
			}
		case "decodes":
			for _, item := range scalars("decodes", value) {
				entry.decodes = append(entry.decodes, trustFormula{text: item.Value, line: item.Line, col: item.Column})
			}
		case "encodes":
			for _, item := range scalars("encodes", value) {
				entry.encodes = append(entry.encodes, trustFormula{text: item.Value, line: item.Line, col: item.Column})
			}
		case "calls":
			f.addCalls(entry, value, formulas)
		case "keeps":
			f.addKeeps(entry, value)
		case "asserts":
			f.addAsserts(entry, value)
		case "prints":
			f.addPrints(entry, value)
		case "isolated":
			if value.Kind != yaml.ScalarNode || value.Value != "true" {
				f.problem(value.Line, "isolated of %s must be true, or left out", entry.key)
				continue
			}
			entry.isolated = true
		case "exits":
			if value.Kind != yaml.ScalarNode || value.Value != "true" {
				f.problem(value.Line, "exits of %s must be true, or left out", entry.key)
				continue
			}
			entry.exits = true
		case "initialiserOnly":
			if value.Kind != yaml.ScalarNode || value.Value != "true" {
				f.problem(value.Line, "initialiserOnly of %s must be true, or left out", entry.key)
				continue
			}
			entry.initialiserOnly = true
		case "receiver":
			if value.Kind != yaml.ScalarNode {
				f.problem(value.Line, "the receiver of %s must be a name", entry.key)
				continue
			}
			entry.receiver = trustFormula{text: value.Value, line: value.Line, col: value.Column}
		default:
			f.problem(field.Line, "unknown field %q in the entry for %s; expected reason, receiver, requires, ensures, modifies, exits, stores, runs, keeps, asserts, vouches, formats, encodes, decodes, prints, calls, isolated, or initialiserOnly",
				field.Value, entry.key)
		}
	}
	if entry.reason == "" {
		f.problem(name.Line, "the entry for %s needs a reason saying why the contract is believed", entry.key)
	}
	// That a function writes nothing is a claim like any other, and has to
	// be made rather than left out.
	if !listed {
		f.problem(name.Line, "the entry for %s needs a modifies list saying what the function may write; "+
			"write \"modifies: []\" if it writes nothing a caller can see", entry.key)
	}
}

// addCalls reads the calls of an entry: a mapping from the function
// parameter, written with names for its parameters as in f(i), to what
// holds when the function calls it.
func (f *trustFile) addCalls(entry *trustEntry, node *yaml.Node, formulas func(string, *yaml.Node) []trustFormula) {
	if node.Kind != yaml.MappingNode {
		f.problem(node.Line, "calls of %s must map a function parameter, written as in f(i), to what holds when %s calls it",
			entry.key, entry.key)
		return
	}
	for i := 0; i+1 < len(node.Content); i += 2 {
		key, body := node.Content[i], node.Content[i+1]
		match := callShape.FindStringSubmatch(key.Value)
		if key.Kind != yaml.ScalarNode || match == nil {
			f.problem(key.Line, "calls of %s: %q must name a function parameter and its parameters, as in f(i) or do()", entry.key, key.Value)
			continue
		}
		call := trustCall{name: match[1], line: key.Line, col: key.Column}
		for _, name := range strings.Split(match[2], ",") {
			if name = strings.TrimSpace(name); name != "" {
				call.params = append(call.params, name)
			}
		}
		if body.Kind != yaml.MappingNode {
			f.problem(body.Line, "calls of %s: %s must be a mapping, such as {} or one with requires", entry.key, key.Value)
			continue
		}
		for j := 0; j+1 < len(body.Content); j += 2 {
			field, value := body.Content[j], body.Content[j+1]
			switch field.Value {
			case "requires":
				call.requires = formulas("requires of "+key.Value+" in calls", value)
			case "deterministic":
				if value.Kind != yaml.ScalarNode || (value.Value != "true" && value.Value != "false") {
					f.problem(value.Line, "deterministic under %s in the calls of %s must be true or false", key.Value, entry.key)
				}
				call.deterministic = value.Value == "true"
			default:
				f.problem(field.Line, "unknown field %q under %s in the calls of %s; expected requires or deterministic", field.Value, key.Value, entry.key)
			}
		}
		entry.calls = append(entry.calls, call)
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
	// Unentered holds the types that proofs looked up an entry for and
	// found none: such a proof rests on the type having no contract.
	Unentered []Unentered
	// AnswerCaches lists the cache directories that answers of Z3 the
	// proofs rest on were read from; see -vego.cache.
	AnswerCaches []string
	// Optional records, for each package with proofs, the types to whose
	// methods its trust files give entries (optional.go).
	Optional []OptionalUse
	// Sizes records, for each package whose trust file declares that
	// sizes fit, the declaration and how many obligations of the package
	// only it proved (sizes.go).
	Sizes []SizesUse
	// Memories records, for each package with verified functions, the
	// memory its module's trust file declares, so that two built together
	// that declare differently are reported (reportTwoMemories).
	Memories []MemoryUse
}

// OptionalUse records, for a package with proofs, the types to whose
// methods the trust files it reads give entries, by their keys as written
// (Keys), with the file that gives each (Files), and those of them that
// resolve in the package's build to a type that is not an interface
// (Concrete). The interfaces among them whose every method has an entry
// are what conversions are checked against (O, optional.go), so two
// packages built together that read different ones let a value checked
// against fewer reach code that relies on more (D5 of the design of F35,
// and F16 of the review of S1: keys of the files, not the types a package
// meets, so that no route between the two packages is missed).
type OptionalUse struct {
	Package  string
	Keys     []string
	Files    []string
	Concrete []string
}

// Unentered is a type, by the key its entry would have, that the proofs of
// a package rely on having no entry. Own is set when the package is in the
// module that declares the type, which gives it a contract in source if at
// all.
type Unentered struct {
	Key     string
	Package string
	Own     bool
}

// EntryUse describes one trusted contract and where it is relied on. Two
// trust files may each have a contract for the same function; the file is
// part of what identifies a contract.
type EntryUse struct {
	Key     string
	Reason  string
	Shipped bool
	// Isolated is set when the entry claims that the function runs no code
	// but what the call hands it (trustEntry.isolated), and IsolatedReason
	// holds what supports a claim its file makes of the whole package.
	Isolated       bool
	IsolatedReason string
	// Exits is set when the entry claims that the function may end the
	// process (trustEntry.exits), and Never when it claims that it always
	// does.
	Exits bool
	Never bool
	File  string
	Line  int
	// Unpredictable is set when the function returns an error and its
	// contract never says that it succeeds.
	Unpredictable bool
	// Runs names the parameters whose code the function may run, and
	// Vouches the error results whose errors the contract vouches for.
	Runs []string
	// Keeps describes each parameter whose code the function keeps, and
	// where, as in "r in result".
	Keeps []string
	// Asserts describes, for each parameter the entry claims it for, what
	// the function may find on what the parameter holds by a type
	// assertion, as in "r: io.WriterTo" or "r: nothing".
	Asserts []string
	Vouches []string
	// Formats names the parameters the function formats as package fmt
	// does.
	Formats []string
	// Encodes names the parameter the function encodes as package
	// encoding/json does.
	Encodes []string
	// Decodes names the parameter into which the function decodes as
	// package encoding/json does.
	Decodes []string
	// Callbacks describes each function parameter given a contract under
	// calls, as in "f(i) when: 0 <= i; i < n".
	Callbacks []string
	// Every names the type of an entry that gives a contract to a method
	// of an interface type or to a function type, as in io.Writer; such an
	// entry is a claim about every value of the type. Relied names the
	// packages whose proofs rest on it, which may be none of the places in
	// Calls.
	Every  string
	Relied []string
	// Fingerprint is, for such an entry, what it says, so that two entries
	// for one type in a build can be told apart from two copies of one.
	Fingerprint string
	// States lists the states that the types of the parameters declare,
	// each as the type, the name, and the reason, as in "sync.Mutex held:
	// True when ...": what the entry's formulas mean by them.
	States []string
	Calls  []token.Position
}

// add merges another usage into u.
func (u *Usage) add(other *Usage) {
	for file, keys := range other.ProjectKeys {
		if u.ProjectKeys == nil {
			u.ProjectKeys = map[string][]string{}
		}
		u.ProjectKeys[file] = keys
	}
	for _, use := range other.Optional {
		if !slices.ContainsFunc(u.Optional, func(known OptionalUse) bool { return known.Package == use.Package }) {
			u.Optional = append(u.Optional, use)
		}
	}
	for _, use := range other.Memories {
		if !slices.ContainsFunc(u.Memories, func(known MemoryUse) bool { return known.Package == use.Package }) {
			u.Memories = append(u.Memories, use)
		}
	}
	for _, use := range other.Sizes {
		if !slices.ContainsFunc(u.Sizes, func(known SizesUse) bool { return known.Package == use.Package }) {
			u.Sizes = append(u.Sizes, use)
		}
	}
	for _, dir := range other.AnswerCaches {
		if !slices.Contains(u.AnswerCaches, dir) {
			u.AnswerCaches = append(u.AnswerCaches, dir)
		}
	}
	for _, none := range other.Unentered {
		if !slices.Contains(u.Unentered, none) {
			u.Unentered = append(u.Unentered, none)
		}
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
			copied.Calls, copied.Relied = nil, nil
			u.Entries = append(u.Entries, &copied)
			index = len(u.Entries) - 1
		}
		merged := u.Entries[index]
		merged.Unpredictable = merged.Unpredictable || use.Unpredictable
		for _, pkg := range use.Relied {
			if !slices.Contains(merged.Relied, pkg) {
				merged.Relied = append(merged.Relied, pkg)
			}
		}
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
	pv.noteSizes(path)
	for _, problem := range pv.projectTrust.problems {
		pv.report(pv.trustPos(pv.projectTrust, problem.line, 1), "%s", problem.msg)
	}
	// Whether or not this package looks the key up, shipped entries it
	// uses may rest on it (F11 of the review of S0 of F35).
	for _, key := range keys {
		if why := projectReplaces(pv.projectTrust.entries[key]); why != "" {
			pv.report(pv.trustPos(pv.projectTrust, pv.projectTrust.entries[key].line, 1), "%s", why)
		}
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
		pkg, name, ok := splitFuncName(key)
		// Unexported names of another package may be missing from what
		// is known about it here; they are checked when it is analysed.
		checkable := ok && visible[pkg] != nil && (visible[pkg] == pv.pass.Pkg || token.IsExported(name[strings.LastIndex(name, ".")+1:]))
		if !checkable {
			continue
		}
		if isType, problem := pv.typeKeyProblem(visible[pkg], key, name); isType {
			if problem != "" {
				pv.report(pv.trustPos(pv.projectTrust, entry.line, 1), "%s", problem)
			}
			continue
		}
		if !declares(visible[pkg], name) {
			pv.report(pv.trustPos(pv.projectTrust, entry.line, 1),
				"the trusted contract names %s, but package %s has no such function", key, pkg)
		}
	}
	// A state declared for a type of the build must be one an interface
	// of another module can have; see fileStates.
	for _, key := range slices.Sorted(maps.Keys(pv.projectTrust.states)) {
		line := pv.projectTrust.states[key][0].typeLine
		pkg, name, _ := splitTypeName(key)
		if visible[pkg] == nil {
			continue
		}
		owner, ok := visible[pkg].Scope().Lookup(name).(*types.TypeName)
		if !ok {
			pv.report(pv.trustPos(pv.projectTrust, line, 1), "the trust file declares states of %s, but package %s has no such type", key, pkg)
			continue
		}
		if problem := pv.fileStateProblem(owner, key); problem != "" {
			pv.report(pv.trustPos(pv.projectTrust, line, 1), "the trust file declares states of %s, which %s", key, problem)
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

// entryFor returns the entry of the trust files for a key, or nil. A
// project entry replaces a shipped one.
func (pv *pkgVerifier) entryFor(key string) *trustEntry {
	if pv.projectTrust != nil {
		// A replacement of an entry that shipped entries rest on that
		// differs from it is reported, and the shipped entry stands
		// (restedon.go).
		if entry := pv.projectTrust.entries[key]; entry != nil && projectReplaces(entry) == "" {
			return entry
		}
	}
	for _, file := range shippedContracts() {
		if entry := file.entries[key]; entry != nil {
			return entry
		}
	}
	return nil
}

// readEntry reads the requires, ensures, and modifies of an entry into the
// contract fn, recording as defects what cannot be read. The clauses mean
// the same wherever the contract is used.
func (pv *pkgVerifier) readEntry(fn *funcInfo, entry *trustEntry) {
	// A file with any problem is not a source of trust at all: which of
	// its entries the problem touched cannot be told apart reliably, and a
	// proof must not rest on a contract that was read wrongly.
	for _, problem := range entry.file.problems {
		fn.defect("%s:%d: %s", filepath.Base(entry.file.path), problem.line, problem.msg)
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
	// A requires is read in one state, so old(x) there could only mean x;
	// it is refused rather than given that meaning without notice.
	for _, c := range fn.requires {
		if mentionsOld(c.node) {
			fn.defect("its requires %q uses old, which has no meaning there: a requires is read in the state of the call", c.text)
		}
	}
	// A trusted contract means the same wherever it is used, so it may not
	// mention the predicates or constants of whichever package calls it.
	for _, c := range slices.Concat(fn.requires, fn.ensures) {
		c.res = pv.plain
	}
	for _, item := range entry.modifies {
		targets, err := logic.ParseTargets(item.text)
		if err != nil {
			fn.defect("its modifies %q cannot be read: %v", item.text, err)
			continue
		}
		c := &clause{kind: "modifies", text: item.text, pos: pv.trustPos(entry.file, item.line, item.col), res: pv.plain}
		fn.modifies = append(fn.modifies, newModTargets(targets, c)...)
	}
}

// trustedContract returns the trusted contract of a function as a funcInfo,
// or nil when it has none. A project entry replaces a shipped one. The
// contract is checked against the real signature on first use: its names
// must be parameters and results of the right types, modifies must list
// what a caller can see change, and the contract must not contradict itself.
func (pv *pkgVerifier) trustedContract(callee *types.Func) *funcInfo {
	if fn, done := pv.trusted[callee]; done {
		return fn
	}
	// A generic function has a contract only at each instantiation, which
	// calleeAt makes; one built over type parameters would mean nothing.
	if isGeneric(callee) {
		panic(fmt.Sprintf("vego: internal error: a contract is asked of the generic function %s; ask it of an instantiation, by calleeAt", callee.FullName()))
	}
	// The method of an interface has no code of its own to trust: an
	// entry for one is a contract of the interface, read by
	// methodContract.
	key := callee.FullName()
	entry := pv.entryFor(key)
	if entry == nil || isIfaceMethod(callee) {
		pv.trusted[callee] = nil
		return nil
	}
	fn := newFuncInfo(callee)
	fn.trust = entry
	nameUnnamed(fn, entry)
	fn.genericTypes = pv.genericTypes(callee)
	pv.trusted[callee] = fn
	pv.readEntry(fn, entry)
	if entry.receiver.text != "" {
		fn.defect("it names a receiver, which only an entry for a method of an interface can do")
	}
	// What exits claims: that the function may end the process.
	switch {
	case entry.exits && fn.obj.Type().(*types.Signature).Recv() != nil:
		fn.defect("%s", exitsOnlyFunctions)
	case entry.exits:
		fn.exits = true
	}
	// The parameters whose code the function is said to run. Listing one
	// that can hold no code would be a claim about nothing.
	for _, item := range entry.runs {
		param, ok := fn.paramNames[item.text]
		switch {
		case !ok:
			fn.defect("its runs %q: %s is not a parameter", item.text, item.text)
		case !holdsCode(param.Type(), map[types.Type]bool{}):
			fn.defect("its runs lists %s, whose type %s can hold no error, interface value, function value, channel, or unsafe.Pointer to run", item.text, param.Type())
		default:
			fn.runs.set(param, true)
		}
	}
	for _, item := range entry.calls {
		pv.trustedCall(fn, item)
	}
	// A parameter under stores claims something of memory modifies lists
	// under it; one with none listed claims it of nothing.
	for _, item := range entry.stores {
		if _, ok := fn.paramNames[item.text]; !ok {
			fn.defect("its stores %q: %s is not a parameter", item.text, item.text)
			continue
		}
		if !slices.ContainsFunc(fn.modifies, func(m *modTarget) bool { return m.name == item.text }) {
			fn.defect("its stores lists %s, under which its modifies lists nothing; stores says what the function stores into memory that modifies lists", item.text)
		}
	}
	pv.readFormats(fn, entry)
	pv.readEncodes(fn, entry)
	pv.readDecodes(fn, entry)
	pv.readPrints(fn, entry)
	pv.readKeeps(fn, entry)
	pv.checkAsserts(fn, entry)
	// The error results whose errors the author vouches for. Listing
	// anything else would be a claim about nothing.
	pv.readVouches(fn, entry, true)
	// A function value that a trusted function hands back is code its
	// author may not have seen, as an error is. Verified code calls it only
	// on the claim that it meets the contract of its type, which vouches
	// makes for a result, and for a parameter for what the function writes
	// into memory it reaches.
	for i, result := range fn.results {
		if !fn.vouches[i] && pv.holdsContractedValue(result.Type(), map[types.Type]bool{}) {
			fn.defect("its result %s can hold a function value or an interface value of a type with a contract; "+
				"list it under vouches to claim that every such value meets the contract of its type", spelledResult(fn, i))
		}
	}
	for _, m := range fn.modifies {
		root := fn.paramNames[m.name]
		if covered := coveredType(fn, m); covered != nil && pv.holdsContractedValue(covered, map[types.Type]bool{}) && !fn.vouchedWrites.get(root) {
			fn.defect("its modifies %q covers memory that can hold a function value or an interface value of a type with a contract; "+
				"list %s under vouches to claim that every such value the function writes there meets the contract of its type", m.text, m.name)
		}
	}
	for name := range fn.paramNames {
		if fn.ambiguous(name, false) {
			fn.defect("its parameter %s has a name that means something else in a contract", name)
		}
	}
	pv.checkTrusted(fn)
	return fn
}

// readVouches reads what an entry vouches for. A result of type error
// claims that its errors meet what vouches says of errors; a result that can
// hold a function value or an interface value of a type with a contract,
// that every such value meets its contract. For a trusted function, and not
// for the contract of a type, a parameter claims that every such value the
// function writes into memory that the parameter reaches, and that its
// modifies covers, meets its contract. Listing anything else would be a
// claim about nothing.
func (pv *pkgVerifier) readVouches(fn *funcInfo, entry *trustEntry, writes bool) {
	for _, item := range entry.vouches {
		index, isResult := fn.resultNames[item.text]
		param, isParam := fn.paramNames[item.text]
		switch {
		case isParam && writes:
			covers := false
			for _, m := range fn.modifies {
				covered := coveredType(fn, m)
				covers = covers || (fn.paramNames[m.name] == param && covered != nil && pv.holdsContractedValue(covered, map[types.Type]bool{}))
			}
			switch {
			case !covers:
				fn.defect("its vouches lists %s, but nothing its modifies lists under %s can hold a function value or an interface value of a type with a contract", item.text, item.text)
			case fn.vouchedWrites.get(param):
				fn.defect("its vouches lists %s twice", item.text)
			default:
				fn.vouchedWrites.set(param, true)
			}
		case !isResult && writes:
			fn.defect("its vouches %q: %s is not a result or a parameter", item.text, item.text)
		case !isResult:
			fn.defect("its vouches %q: %s is not a result", item.text, item.text)
		case !writes && !isError(fn.results[index].Type()):
			fn.defect("its vouches lists %s, whose type %s is not error; what a call through a value of the type returns comes from code that is not verified, "+
				"or from code that verified code made, and needs no claim", item.text, fn.results[index].Type())
		case !isError(fn.results[index].Type()) && !pv.holdsContractedValue(fn.results[index].Type(), map[types.Type]bool{}):
			fn.defect("its vouches lists %s, whose type %s is not error and can hold no function value or interface value of a type with a contract", item.text, fn.results[index].Type())
		case fn.vouches[index]:
			fn.defect("its vouches lists %s twice", item.text)
		default:
			fn.vouches[index] = true
		}
	}
}

// spelledResult names a result of a contract as its clauses spell it: by
// its name, or as result, result1, ... when it has none.
func spelledResult(fn *funcInfo, index int) string {
	name := fn.results[index].Name()
	for spelled, i := range fn.resultNames {
		if i == index {
			name = spelled
		}
	}
	return name
}

// defect records that a trusted contract is unusable. Defects are reported
// where the contract is used, which is where the proof would have relied on
// it.
func (fn *funcInfo) defect(format string, args ...any) {
	fn.defects = append(fn.defects, fmt.Sprintf(format, args...))
	fn.broken = true
}

// typeDefect records a defect found by reading or checking a contract at
// the types of its parameters, which for the contract of an instantiation
// of a generic function belongs to that instantiation and may not hold at
// another. A defect found otherwise is one of the entry at every type
// argument; see insteadOf.
func (fn *funcInfo) typeDefect(format string, args ...any) {
	fn.defect(format, args...)
	if fn.atTypes == nil {
		fn.atTypes = map[string]bool{}
	}
	fn.atTypes[fn.defects[len(fn.defects)-1]] = true
}

// checkTrusted resolves a trusted contract against the function's signature
// and rejects one that contradicts itself, from which anything would follow.
func (pv *pkgVerifier) checkTrusted(fn *funcInfo) {
	pv.run(fn, func(v *fnVerifier) {
		v.lenient = true
		v.misreadAs = func(c *clause, err error) {
			// A clause is wrong at every type argument when it names a
			// field, a state, or an address of a value of a type
			// parameter, or a name that is nothing, or has a form the
			// resolver refuses whatever the types. Anything else, the
			// sorts of what it reads and what the environment finds at
			// the types of the parameters, may differ at another type
			// argument.
			if errors.As(err, new(entryDefect)) || errors.As(err, new(*logic.FormError)) {
				fn.defect("in its %s %q: %v", c.kind, c.text, err)
				return
			}
			fn.typeDefect("in its %s %q: %v", c.kind, c.text, err)
		}
		// A primed path describes memory after the call. A call changes
		// a table only if modifies lists something in it, and a path reads
		// a table at each step that goes through memory. If none of the
		// tables a primed path reads can have changed, what it describes is
		// as it was, and a clause that needs the prime could only
		// contradict the caller. Tables are compared, not objects, so that
		// a path through one parameter may describe what the function
		// writes through another that is the same object.
		v.primedPaths(fn)
		entry := v.enter()
		for _, refused := range v.entryOnly(entry) {
			fn.typeDefect("%s", refused.message(fn.obj.Name()))
		}
		// The requires of calls are read once here, so that a name they
		// cannot use is a defect of the entry.
		for _, param := range fn.params {
			if cb := fn.calls.get(param); cb != nil {
				given := make([]value, len(cb.params))
				for i, p := range cb.params {
					given[i] = v.unknown(p.Name(), p.Type(), entry)
				}
				at := entry.clone()
				facts := v.callRequires(cb, given, v.entry, at)
				// What f returns for an argument is stated for every argument
				// its requires allow, read in the state at the call of the
				// trusted function, so they may not read memory, which changes
				// between the calls of f.
				if cb.applied && slices.ContainsFunc(append(facts, at.hyps[len(entry.hyps):]...), mentionsMemory) {
					fn.typeDefect("its ensures applies %s, and its calls requires for %s read memory; a requires of a function that is applied "+
						"may speak only of values", cb.param.Name(), cb.param.Name())
				}
			}
		}
		// The one contradiction an entry may state is that its function
		// never returns, which exits says how: by ending the process. Its
		// requires may still not contradict each other.
		if neverReturns(fn) {
			if v.quickly(entry, nil, logic.False()) {
				fn.typeDefect("it contradicts itself, so anything could be proved from it")
			}
			return
		}
		_, outcome, _ := v.contractInstance(entry)
		if pv.contradictory(outcome) {
			fn.typeDefect("it contradicts itself, so anything could be proved from it")
		}
	})
}

// primedPaths rejects every path of an ensures that is primed although no
// table it reads is one the function may change; see checkPrimed.
func (v *fnVerifier) primedPaths(fn *funcInfo) {
	// For each table, the slice parameters whose own elements an entry
	// lists, or nil for an entry that may reach anything in the table.
	changed := map[string][]*types.Var{}
	for _, m := range fn.modifies {
		if form, _, err := v.locateTarget(fn, m, nil, nil, nil); err == nil {
			var whose *types.Var
			if form.direct && form.elem != nil {
				whose = form.param
			}
			target{cells: form.cells, mapType: form.mapType}.regions(func(key string, _ logic.Sort) {
				changed[key] = append(changed[key], whose)
			})
			// A struct that a pointer of a type with states points to
			// comes with the row of its states (A5 of S0b of F34).
			if len(v.pointerStatesSites(form, site{})) > 0 {
				changed[stateRegion] = append(changed[stateRegion], nil)
			}
		}
	}
	for _, c := range fn.ensures {
		var visit func(n *logic.Node, whole bool, state string)
		visit = func(n *logic.Node, whole bool, state string) {
			isPath := n.Kind == logic.NIdent || n.Kind == logic.NField || n.Kind == logic.NIndex || n.Kind == logic.NDeref
			if isPath && whole {
				v.checkPrimed(fn, c, n, changed, state)
			}
			// The one argument of a state, as in held(m'), reads the state
			// where it lies.
			inner := ""
			if n.Kind == logic.NCall && len(n.Kids) == 1 && v.stateNamed(n.Name) {
				inner = n.Name
			}
			// The length of an owner, as |b'|, reads the fields its
			// declaration names, where the pointer points.
			if n.Kind == logic.NLen {
				inner = lengthRead
			}
			for i, kid := range n.Kids {
				visit(kid, !isPath || i > 0, inner)
			}
		}
		visit(c.node, true, "")
	}
}

// checkPrimed rejects a path of a trusted ensures that is primed somewhere
// although no table it reads is one the function may change. The elements
// of a slice parameter are a special case: slice parameters of one element
// type do not overlap, so listing another one changes nothing in this one.
// A path it cannot follow is left to the checks that read the clause. With
// state set, the path is the argument of that state, which is read too.
func (v *fnVerifier) checkPrimed(fn *funcInfo, c *clause, path *logic.Node, changed map[string][]*types.Var, state string) {
	// *p reads the box p points to, where the rest of the path leads
	// (F19 of the review of step 2 of F37).
	whole, derefs := path, 0
	for path.Kind == logic.NDeref {
		path, derefs = path.Kids[0], derefs+1
	}
	if derefs > 1 {
		return
	}
	primed := false
	for n := path; ; n = n.Kids[0] {
		primed = primed || n.Primed
		if n.Kind == logic.NIdent {
			break
		}
		// A path from a package in quotes names an error variable, which
		// the resolver refuses to see primed.
		if len(n.Kids) == 0 {
			return
		}
	}
	steps := newModTargets([]*logic.Node{path}, c)[0]
	param, isParam := fn.paramNames[steps.name]
	if !primed || !isParam {
		return
	}
	if _, modelled := layoutOf(param.Type()); !modelled {
		return
	}
	// A struct lies in memory once a pointer has been followed or an
	// element of a slice taken; a field of a struct that was passed by
	// value, or read out of a map, does not.
	t, inMemory := param.Type(), false
	// read holds the cells the path reads, and own, for each, whether it
	// is an element of the slice parameter itself.
	var read []cell
	var own []bool
	elements := func(elem types.Type, first bool) {
		for _, c := range v.cellsOf(elem) {
			read, own = append(read, c), append(own, first)
		}
	}
	// owned is set while the path is inside an element of the slice
	// parameter itself: from the first index on, through fields, until a
	// pointer is followed or another slice or a map is entered.
	owned := false
	for i, step := range steps.steps {
		if step.field == "" {
			switch {
			case isMap(t) && mapModelled(t):
				target{mapType: t}.regions(func(key string, _ logic.Sort) { read, own = append(read, cell{key: key}), append(own, false) })
				_, t = mapParts(t)
				inMemory, owned = false, false
			case isSlice(t):
				t = elemType(t)
				if _, modelled := layoutOf(t); !modelled {
					return
				}
				owned = i == 0
				elements(t, owned)
				inMemory = true
			case isString(t):
				t = types.Typ[types.Uint8]
			default:
				return
			}
			continue
		}
		found, indices, _ := types.LookupFieldOrMethod(t, true, fn.obj.Pkg(), step.field)
		if _, isField := found.(*types.Var); !isField {
			return
		}
		for _, index := range indices {
			object := t
			if target, viaPointer := pointee(t); viaPointer {
				object, inMemory, owned = target, true, false
			}
			fields, isStruct := object.Underlying().(*types.Struct)
			if _, modelled := layoutOf(object); !isStruct || !modelled {
				return
			}
			if lo, hi, _ := fieldLeaves(object, index); inMemory && hi > lo {
				read, own = append(read, v.cellsOf(object)[lo:hi]...), append(own, slices.Repeat([]bool{owned}, hi-lo)...)
			}
			t = fields.Field(index).Type()
		}
	}
	// What the path leads to is read as well: what *p reads, the elements
	// of a slice, the keys and values of a map, and a state where a pointer
	// points.
	if object, viaPointer := pointee(t); viaPointer && derefs == 1 {
		for _, c := range v.cellsOf(object) {
			read, own = append(read, c), append(own, false)
		}
	}
	if object, viaPointer := pointee(t); viaPointer && state != "" && state != lengthRead {
		if u, isStruct := object.Underlying().(*types.Struct); isStruct {
			decls := statesOf(u)
			if index := slices.IndexFunc(decls, func(d stateDecl) bool { return d.name == state }); index >= 0 {
				cells := v.cellsOf(object)
				read, own = append(read, cells[len(cells)-len(decls)+index]), append(own, false)
			}
		}
	}
	// A state that an interface the pointer's type implements declares
	// lies in the region of states, at the pointer's key.
	if _, viaPointer := pointee(t); viaPointer && state != "" && state != lengthRead && v.pointerKeyed(t) &&
		slices.ContainsFunc(v.pointerStates(t), func(s ifaceState) bool { return s.name == state }) {
		read, own = append(read, stateCell), append(own, false)
	}
	// The length of an owner reads its struct, where a pointer points.
	if object, viaPointer := pointee(t); viaPointer && state == lengthRead && ownerLength(object) != nil {
		for _, c := range v.cellsOf(object) {
			read, own = append(read, c), append(own, false)
		}
	}
	// The states of an interface value lie in the row of its home.
	if isIface(t) && state != "" && state != lengthRead {
		read, own = append(read, stateCell), append(own, false)
	}
	switch {
	case isMap(t) && mapModelled(t):
		target{mapType: t}.regions(func(key string, _ logic.Sort) { read, own = append(read, cell{key: key}), append(own, false) })
	case isSlice(t):
		if _, modelled := elemLayout(elemType(t)); modelled {
			elements(elemType(t), len(steps.steps) == 0)
		}
	}
	reached := false
	for i, c := range read {
		reached = reached || slices.ContainsFunc(changed[c.key], func(whose *types.Var) bool { return !own[i] || whose == nil || whose == param })
	}
	if !reached {
		fn.typeDefect("its ensures %q describes %s after the call, but nothing its modifies lists is memory that %s reads, so the call cannot have changed it; "+
			"drop the prime or list what the function writes", c.text, c.text[whole.Start:whole.End], c.text[whole.Start:whole.End])
	}
}

// lengthRead is the state checkPrimed is given for the operand of |...|.
const lengthRead = "|length|"

// noteUse records that a proof relies on a trusted contract.
func (pv *pkgVerifier) noteUse(fn *funcInfo, at token.Pos) {
	entry := fn.trust
	// The project's file may hold an entry that would take the place of
	// this one, or say more, among what could not be read.
	if problem := pv.trustProblem(); problem != "" {
		pv.report(at, "%s, so the contract used here for %s may not be the one the file means to give it: fix the file first", problem, entry.key)
	}
	index := slices.IndexFunc(pv.usage.Entries, func(use *EntryUse) bool {
		return use.Key == entry.key && use.File == entry.file.path
	})
	if index < 0 {
		var runs, vouches, formats, encodes []string
		for _, item := range entry.encodes {
			encodes = append(encodes, item.text)
		}
		var decodes []string
		for _, item := range entry.decodes {
			decodes = append(decodes, item.text)
		}
		for _, item := range entry.runs {
			runs = append(runs, item.text)
		}
		for _, item := range entry.formats {
			formats = append(formats, item.text)
		}
		for _, item := range entry.vouches {
			vouches = append(vouches, item.text)
		}
		var callbacks []string
		for _, call := range entry.calls {
			described := call.name + "(" + strings.Join(call.params, ", ") + ")"
			var conditions []string
			for _, formula := range call.requires {
				conditions = append(conditions, formula.text)
			}
			// Each clause is shown as written, apart from the others, so
			// that no clause reads as part of its neighbour.
			if len(conditions) > 0 {
				described += " when: " + strings.Join(conditions, "; ")
			}
			callbacks = append(callbacks, described)
		}
		every := ""
		switch {
		case fn.methodOf != nil:
			every = types.TypeString(fn.methodOf.Type().(*types.Signature).Recv().Type(), nil)
		case fn.valueOf != nil:
			every = funcTypeKey(fn.valueOf)
		}
		var states []string
		for _, param := range fn.params {
			object, isPointer := pointee(param.Type())
			if !isPointer {
				object = param.Type()
			}
			if u, isStruct := object.Underlying().(*types.Struct); isStruct {
				for _, decl := range statesOf(u) {
					states = append(states, fmt.Sprintf("%s %s: %s", types.TypeString(object, nil), decl.name, decl.reason))
				}
			}
		}
		pv.usage.Entries = append(pv.usage.Entries, &EntryUse{
			Key: entry.key, Reason: entry.reason, Shipped: entry.file.shipped, Isolated: entry.isIsolated(), IsolatedReason: entry.file.isolatedReason,
			Exits: entry.exits, Never: neverReturns(fn), File: entry.file.path, Line: entry.line, Runs: runs, Keeps: keepsDescribed(entry), Asserts: assertsDescribed(entry), Vouches: vouches, Formats: formats, Encodes: encodes, Decodes: decodes, Callbacks: callbacks,
			Every: every, Relied: []string{pv.pass.Pkg.Path()}, Fingerprint: entry.fingerprint(), States: states,
		})
		index = len(pv.usage.Entries) - 1
	}
	use := pv.usage.Entries[index]
	fn.use = use
	if !at.IsValid() {
		return
	}
	position := pv.pass.Fset.Position(at)
	if !slices.Contains(use.Calls, position) {
		use.Calls = append(use.Calls, position)
		sort.Slice(use.Calls, func(i, j int) bool { return use.Calls[i].String() < use.Calls[j].String() })
	}
	fn.use = use
}

// paramPosition reads a name param1, param2, ...
var paramPosition = regexp.MustCompile(`\bparam([1-9][0-9]*)\b`)

// nameUnnamed names each unnamed parameter of a function or method that a
// trust entry describes by its position, param1, param2, ..., as unnamed
// results are result1, result2 (decided by the orchestrator, F28): Go
// declares (net/http.ResponseWriter).Write([]byte) with no name for what it
// is handed. A name a parameter has keeps it, and an entry that writes
// paramN for a parameter that has a name is a defect, so that nobody writes
// param1 for p by habit.
func nameUnnamed(fn *funcInfo, entry *trustEntry) {
	sig := fn.obj.Type().(*types.Signature)
	for i := range sig.Params().Len() {
		p := sig.Params().At(i)
		name := fmt.Sprintf("param%d", i+1)
		if p.Name() != "" && p.Name() != "_" {
			continue
		}
		// Go forbids mixing named and unnamed parameters, so the name can
		// clash only with the receiver or a named result.
		_, takenParam := fn.paramNames[name]
		_, takenResult := fn.resultNames[name]
		if takenParam || takenResult {
			fn.defect("its parameter %d has no name, and %s, the name an entry gives it, names the receiver or a result", i+1, name)
			continue
		}
		fn.paramNames[name] = p
	}
	var texts []string
	for _, list := range [][]trustFormula{entry.requires, entry.ensures, entry.modifies, entry.runs, entry.vouches, entry.formats, entry.encodes, entry.decodes, entry.stores} {
		for _, f := range list {
			texts = append(texts, f.text)
		}
	}
	for _, list := range [][]trustKeep{entry.keeps, entry.asserts, entry.prints} {
		for _, k := range list {
			texts = append(texts, k.name)
		}
	}
	reported := map[string]bool{}
	for _, text := range texts {
		for _, match := range paramPosition.FindAllStringSubmatch(text, -1) {
			n := 0
			fmt.Sscan(match[1], &n)
			if n < 1 || n > sig.Params().Len() || reported[match[0]] {
				continue
			}
			if p := sig.Params().At(n - 1); p.Name() != "" && p.Name() != "_" && p.Name() != match[0] {
				reported[match[0]] = true
				fn.defect("it writes %s, but parameter %d has the name %s; write %s", match[0], n, p.Name(), p.Name())
			}
		}
	}
}

// isIsolated reports whether an entry, or the file that holds it, claims
// that the function runs no code but what the call hands it.
func (entry *trustEntry) isIsolated() bool {
	return entry.isolated || entry.file != nil && entry.file.isolated
}

// isolatedPackages returns the packages that a shipped file claims, at its
// top, to be isolated as a whole: every function and method of the package
// runs no code but what its call hands it. TestIsolatedHooks holds the
// claim against the hooks each package exposes.
func isolatedPackages() map[string]bool {
	isolatedOnce.Do(func() {
		isolatedPkgs = map[string]bool{}
		for _, file := range shippedContracts() {
			if !file.isolated {
				continue
			}
			for key := range file.entries {
				name := key
				if strings.HasPrefix(key, "(") {
					name = strings.TrimPrefix(key[1:strings.Index(key, ")")], "*")
				}
				isolatedPkgs[name[:strings.LastIndex(name, ".")]] = true
			}
		}
	})
	return isolatedPkgs
}

var (
	isolatedOnce sync.Once
	isolatedPkgs map[string]bool
)
