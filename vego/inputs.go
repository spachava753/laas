package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"maps"
	"math/big"
	"regexp"
	"slices"
	"strings"

	"github.com/spachava753/laas/vego/internal/logic"
	"gopkg.in/yaml.v3"
)

// Inputs that end (F39, part B).
//
// A project declares in its trust file that what its program reads ends:
//
//	inputs:
//	  bytes: 1TB
//	  reason: ...
//
// The claim is about what files, pipes, terminals, sockets, and standard
// input hold, which the verifier cannot see: through any one reader the
// declaration covers, at most the declared number of bytes arrive before
// Read returns an error, and every Read into a buffer that is not empty
// returns a byte or an error (What a proof assumes). A reader the
// declaration covers is one of which ends(r) holds; unread(r) is the
// declared amount less what was read through r. Without the declaration
// neither is known, no clause of the shipped files that speaks of them is
// assumed, and every problem is what it was.

// inputsDecl is a project's declaration that its inputs end.
type inputsDecl struct {
	bytes *big.Int
	// written is the amount as the file writes it, as in 1TB.
	written string
	reason  string
	line    int
}

// addInputs reads the declaration that inputs end.
func (f *trustFile) addInputs(key, value *yaml.Node) {
	if f.shipped {
		f.problem(key.Line, "inputs may be declared only in the trust file of a project")
		return
	}
	const shape = "inputs must be a mapping with bytes, the most that any one reader of the program's files, pipes, terminals, sockets, " +
		"and standard input yields before it ends, as in 1TB, and a reason, which says why they end"
	if value.Kind != yaml.MappingNode {
		f.problem(value.Line, shape)
		return
	}
	decl := &inputsDecl{line: key.Line}
	for i := 0; i+1 < len(value.Content); i += 2 {
		field, text := value.Content[i], value.Content[i+1]
		if text.Kind != yaml.ScalarNode {
			f.problem(text.Line, "%s of inputs must be text", field.Value)
			return
		}
		switch field.Value {
		case "bytes":
			n, err := parseMemory(text.Value)
			if err != nil {
				f.problem(text.Line, "the bytes of inputs %s", err)
				return
			}
			decl.bytes, decl.written = n, strings.TrimSpace(text.Value)
		case "reason":
			decl.reason = strings.TrimSpace(text.Value)
		default:
			f.problem(field.Line, "unknown field %q of inputs; expected bytes and reason", field.Value)
			return
		}
	}
	if decl.bytes == nil || decl.reason == "" {
		f.problem(value.Line, shape)
		return
	}
	f.inputs = decl
}

// inputsOf returns the declaration in effect for the package, or nil.
func (pv *pkgVerifier) inputsOf() *inputsDecl {
	if pv.projectTrust == nil {
		return nil
	}
	return pv.projectTrust.inputs
}

// InputsUse records the declaration that inputs end of the trust file of a
// package with verified functions: File is the trust file, or empty, and
// Bytes is empty when it declares none.
type InputsUse struct {
	Package string
	File    string
	Line    int
	Written string
	Bytes   string
	Reason  string
}

// noteInputs records the declaration of a package with verified functions.
func (pv *pkgVerifier) noteInputs() {
	if !slices.ContainsFunc(pv.order, func(fn *funcInfo) bool { return fn.annotated() }) {
		return
	}
	use := InputsUse{Package: pv.pass.Pkg.Path()}
	if pv.projectTrust != nil {
		use.File = pv.projectTrust.path
		if decl := pv.projectTrust.inputs; decl != nil {
			use.Line, use.Written, use.Bytes, use.Reason = decl.line, decl.written, decl.bytes.String(), decl.reason
		}
	}
	pv.usage.Inputs = append(pv.usage.Inputs, use)
}

// reportTwoInputs reports two packages with verified functions, built
// together, whose trust files declare different amounts under inputs, or of
// which one declares and the other does not: a reader that one of them
// required to end, or bounded by its amount, can reach the other.
func (pv *pkgVerifier) reportTwoInputs(total *Usage) {
	uses := slices.Clone(total.Inputs)
	slices.SortFunc(uses, func(a, b InputsUse) int { return strings.Compare(a.Package, b.Package) })
	said := func(use InputsUse) string {
		file := "no trust file"
		if use.File != "" {
			file = use.File
		}
		if use.Bytes == "" {
			return fmt.Sprintf("package %s (%s) declares no inputs", use.Package, file)
		}
		return fmt.Sprintf("package %s (%s) declares %s", use.Package, file, use.Written)
	}
	for i, a := range uses {
		for _, b := range uses[i+1:] {
			if a.Bytes == b.Bytes {
				continue
			}
			pv.report(pv.pass.Files[0].Package, rAnnotationFault, "the verified packages of this build declare different inputs: %s, and %s; "+
				"a reader that the proofs of one take to end, or to yield at most its amount, can reach the proofs of the other. "+
				"Declare the same inputs in both trust files, or none in either, or run laas with -vego.trusted naming one file", said(a), said(b))
			return
		}
	}
}

// inputsReport renders the section of the trust report on the declaration
// that inputs end.
func inputsReport(uses []InputsUse, relative func(string) string) string {
	byFile := map[string][]InputsUse{}
	for _, use := range uses {
		if use.Bytes != "" {
			byFile[use.File] = append(byFile[use.File], use)
		}
	}
	if len(byFile) == 0 {
		return ""
	}
	var b strings.Builder
	fmt.Fprintf(&b, "Inputs declared to end: %d\n", len(byFile))
	for _, file := range slices.Sorted(maps.Keys(byFile)) {
		listed := byFile[file]
		slices.SortFunc(listed, func(a, b InputsUse) int { return strings.Compare(a.Package, b.Package) })
		first := listed[0]
		fmt.Fprintf(&b, "  %s:%d\n", relative(file), first.Line)
		fmt.Fprintf(&b, "    claims:  through any one reader of a file, a pipe, a terminal, a socket, or standard input that the program reads, "+
			"and of a reader handed to it where ends is required, at most %s (%s bytes) arrive before Read returns an error, and a Read into "+
			"a buffer that is not empty returns a byte or an error; a regular file the program reads reports with Stat a size of at most that; "+
			"a directory it lists holds at most that many entries while it lists it; the program does not write, through one open file, a file it reads through another; "+
			"os.Stdout and os.Stderr do not hold the file os.Stdin holds; no code that is not verified makes a reader yield again bytes already read "+
			"from its source, through any value, while a verified function runs, except through a call of an entry that lists rewinds\n", first.Written, first.Bytes)
		fmt.Fprintf(&b, "    reason:  %s\n", first.Reason)
		var packages []string
		for _, use := range listed {
			packages = append(packages, use.Package)
		}
		fmt.Fprintf(&b, "    packages: %s\n", strings.Join(packages, ", "))
	}
	b.WriteString("\n")
	return b.String()
}

// Where ends and unread lie. For an interface value they are at the key of
// its states: unread in a region of its own at the row of that key, which
// every target and site that may change the states of the row forgets too
// (rowCells), and ends in a sequence that nothing writes, since that the
// declaration covers a reader does not change. For a *bufio.Reader and a
// *bufio.Scanner, whose methods read through what they keep and whose
// Reset could make them read from something else, both lie at the key of
// the pointer, in rows that every target and site that may change the
// struct forgets (readerTarget, readerSites). For a *os.File, ends lies in
// the sequence at the key of the pointer: every reader made from it shares
// whether it is covered, and none shares its budget (F5 of the design
// review of F39).
const (
	unreadRegion = "reader unread"
	endsRegion   = "reader ends"
)

var (
	unreadCell = cell{key: unreadRegion, sort: logic.Int}
	endsCell   = cell{key: endsRegion, sort: logic.Bool}
	// endsOfKeys is whether the declaration covers the reader at a key.
	endsOfKeys = logic.Const("reader ends of keys", logic.BoolSeq)
)

// rowCells returns the cells of the row of the states of an interface
// value that a target or a site covers: its states, and under the
// declaration that inputs end its unread too.
func (pv *pkgVerifier) rowCells() []cell {
	if pv.inputsOf() == nil {
		return []cell{stateCell}
	}
	return []cell{stateCell, unreadCell}
}

// rowRegions returns the regions the row of a target lies in.
func rowRegions(cells []cell) []cell {
	if len(cells) == 0 {
		return []cell{stateCell}
	}
	return cells
}

// inRowRegions reports whether a region is one the row of a target lies in.
func inRowRegions(cells []cell, key string) bool {
	return slices.ContainsFunc(rowRegions(cells), func(c cell) bool { return c.key == key })
}

// bufferedReader reports whether t is bufio.Reader or bufio.Scanner, the
// types whose pointers keep ends and unread at their key.
func bufferedReader(t types.Type) bool {
	named, ok := types.Unalias(t).(*types.Named)
	if !ok || named.Obj().Pkg() == nil || named.Obj().Pkg().Path() != "bufio" {
		return false
	}
	return named.Obj().Name() == "Reader" || named.Obj().Name() == "Scanner"
}

// readerTarget returns, under the declaration, for a target that is one
// struct value of a bufio.Reader or bufio.Scanner, the target of the rows
// of its ends and unread, which a call whose frame covers the struct
// changes (F6 of the design review of F39).
func (v *fnVerifier) readerTarget(t target) (target, bool) {
	if v.inputsOf() == nil || !t.single || t.base == nil || t.fp || t.row || !bufferedReader(t.base.t) {
		return target{}, false
	}
	rows := t
	rows.single, rows.base, rows.lo, rows.hi, rows.owned, rows.also = false, nil, nil, nil, nil, nil
	rows.cells, rows.row, rows.ref, rows.besideStruct = []cell{unreadCell, endsCell}, true, pkey(value{t.base.ref, t.base.at}), true
	return rows, true
}

// readerSites returns, under the declaration, for the site of a struct of
// a bufio.Reader or bufio.Scanner, the site of the rows of its ends and
// unread.
func (v *fnVerifier) readerSites(form shape, at site) []site {
	if v.inputsOf() == nil || form.row || form.fp || form.elem != nil || form.mapType != nil || form.typ == nil {
		return nil
	}
	object := form.typ
	if inner, isPointer := pointee(object); isPointer {
		object = inner
	}
	if !bufferedReader(object) {
		return nil
	}
	return []site{{cells: []cell{unreadCell, endsCell}, row: true, pointer: true, root: at.root, lo: at.lo}}
}

// readerGhost resolves ends(x) and unread(x) (F39, part B). Without the
// declaration that inputs end they are no words of the language, so a
// predicate of the name is what they mean, and with none the message says
// to declare inputs.
func (e *specEnv) readerGhost(name string, steps []logic.Step, word string, when logic.When) (*logic.Term, error) {
	what := spell(name, steps)
	decl := e.v.inputsOf()
	if decl == nil {
		return nil, &logic.NoState{Msg: fmt.Sprintf("%s(%s) speaks of a reader that ends, which is known only where the trust file declares that inputs end; "+
			"declare inputs in vego-trusted.yaml, or bound the number of reads", word, what)}
	}
	found, err := e.locateAt(name, steps, when, true)
	switch {
	case err != nil:
		return nil, err
	case found.constant != nil:
		return nil, fmt.Errorf("%s(%s): %s is a constant", word, what, what)
	}
	var ends, key *logic.Term
	var region bool
	object, viaPointer := pointee(found.typ)
	switch {
	case isIface(found.typ):
		key = skey(found.val[0])
		ends = logic.Select(endsOfKeys, key)
	case viaPointer && bufferedReader(object):
		e.v.notePointerKey(found.sink, found.val)
		key, region = pkey(found.val), true
		ends = e.v.fetch(found.sink, found.mem, []cell{endsCell}, key, logic.IntLit(0))[0]
	case viaPointer && isOSFile(object):
		if word == "unread" {
			return nil, fmt.Errorf("unread(%s): %s is a *os.File, whose reads have no budget of their own; read it through a bufio.Reader, a bufio.Scanner, "+
				"or as an io.Reader, whose unread is known", what, what)
		}
		e.v.notePointerKey(found.sink, found.val)
		return logic.Select(endsOfKeys, pkey(found.val)), nil
	default:
		// Not a reader: a predicate of the name, if there is one, is what
		// is meant (D2 of the design of F39).
		return nil, &logic.NoState{Msg: fmt.Sprintf("%s(%s): %s is a %s; ends and unread speak of an interface value, a *bufio.Reader, a *bufio.Scanner, "+
			"and, for ends, a *os.File", word, what, what, found.typ)}
	}
	if word == "ends" {
		return ends, nil
	}
	_ = region
	unread := e.v.fetch(found.sink, found.mem, []cell{unreadCell}, key, logic.IntLit(0))[0]
	if found.sink != nil && !hasBound(unread) {
		// What is known of the unread of a reader the declaration covers:
		// at least none, and at most the declared amount.
		found.sink.assume(logic.Implies(ends, logic.And(logic.Le(logic.IntLit(0), unread), logic.Le(unread, logic.BigLit(decl.bytes)))))
	}
	return unread, nil
}

// isOSFile reports whether t is os.File.
func isOSFile(t types.Type) bool {
	named, ok := types.Unalias(t).(*types.Named)
	return ok && named.Obj().Pkg() != nil && named.Obj().Pkg().Path() == "os" && named.Obj().Name() == "File"
}

// noteStream states, under the declaration that inputs end, what the claim
// says of the file a standard stream holds where it is read: os.Stdin
// holds a file, not nil, that the declaration covers, and os.Stdout and
// os.Stderr hold files it does not, so neither is the file os.Stdin holds.
func (v *fnVerifier) noteStream(st *state, variable *types.Var, val value) {
	if v.inputsOf() == nil || variable.Pkg() == nil || variable.Pkg().Path() != "os" || len(val) < 2 {
		return
	}
	ends, held := logic.Select(endsOfKeys, pkey(val)), logic.Ne(val[0], logic.RefLit(0))
	switch variable.Name() {
	case "Stdin":
		st.assume(logic.And(held, ends))
	case "Stdout", "Stderr":
		st.assume(logic.Implies(held, logic.Not(ends)))
	}
}

// noteConverted states, under the declaration that inputs end, whether the
// declaration covers a value verified code converted: one made from a
// *os.File is covered as the file is, and every other is not, since a
// reader that verified code makes ends by proof or by entry, never by the
// declaration.
func (v *fnVerifier) noteConverted(st *state, held *logic.Term, from types.Type, converted value) {
	if v.inputsOf() == nil {
		return
	}
	ends := logic.Select(endsOfKeys, skey(held))
	if object, isPointer := pointee(from); isPointer && isOSFile(object) {
		st.assume(logic.Iff(ends, logic.Select(endsOfKeys, pkey(converted))))
		return
	}
	st.assume(logic.Not(ends))
}

// fileWriters are the methods through which what a *os.File reads can be
// written or read again: a write, and a seek or a truncation, after which a
// read yields again what it yielded.
var fileWriters = map[string]bool{"Write": true, "WriteString": true, "WriteAt": true, "Truncate": true, "Seek": true, "ReadFrom": true}

// writesThrough reports whether a value of the interface type t can write
// what a file it holds reads: t has one of fileWriters.
func writesThrough(t types.Type) (string, bool) {
	iface, ok := t.Underlying().(*types.Interface)
	if !ok {
		return "", false
	}
	for method := range iface.Methods() {
		if fileWriters[method.Name()] {
			return method.Name(), true
		}
	}
	return "", false
}

// refuseFileWrite checks, under the declaration, that a value at key,
// through which code is about to write, is no reader the declaration
// covers: reading such a reader to its end while writing the same file
// through one value would not end, and the declaration does not cover
// what the program writes (F5 of the design review of F39, and N1). A
// *os.File may instead be nil, given as file, since every method of
// *os.File that writes returns ErrInvalid for a nil file and writes
// nothing (checkValid), and os.Stdout and os.Stderr are not known to hold
// a file; file is nil for an interface value, which the caller knows holds
// one.
func (v *fnVerifier) refuseFileWrite(st *state, guard []*logic.Term, file, key *logic.Term, pos token.Pos, how string) {
	if v.inputsOf() == nil {
		return
	}
	goal := logic.Not(logic.Select(endsOfKeys, key))
	if file != nil {
		goal = logic.Or(logic.Eq(file, logic.RefLit(0)), goal)
	}
	v.check(st, guard, goal, pos,
		"%s may write a file that is read under the declaration that inputs end; reading and writing one file through one value is not supported yet, "+
			"so open the file to write it apart, with os.Create, or, for a file or a reader a parameter holds that is not read to its end, "+
			"say so with // @Requires ~ends(f) of that parameter", how)
}

// checkWrittenFiles checks, at a call of a trusted function under the
// declaration, each *os.File it may write through: the receiver of a method
// of *os.File that writes, seeks, or truncates, and a *os.File that a
// project's entry lists under modifies.
func (v *fnVerifier) checkWrittenFiles(fn *funcInfo, name string, args map[*types.Var]value, st *state, guard []*logic.Term, pos token.Pos) {
	// The check of a method of a value converted to an interface runs its
	// method on the value, which the conversion checked (N1 (ii)).
	if v.inputsOf() == nil || fn.trust == nil || v.fn.methodOf != nil || v.fn.valueOf != nil {
		return
	}
	sig := fn.obj.Type().(*types.Signature)
	if recv := sig.Recv(); recv != nil && fileWriters[fn.obj.Name()] {
		if object, isPointer := pointee(recv.Type()); isPointer && isOSFile(object) && len(args[recv]) >= 2 {
			v.refuseFileWrite(st, guard, args[recv][0], pkey(args[recv]), pos, name)
			return
		}
	}
	if fn.trust.file != nil && fn.trust.file.shipped {
		return
	}
	for _, m := range fn.modifies {
		param := fn.paramNames[m.name]
		if param == nil || len(m.steps) > 0 {
			continue
		}
		if object, isPointer := pointee(param.Type()); isPointer && isOSFile(object) && len(args[param]) >= 2 {
			v.refuseFileWrite(st, guard, args[param][0], pkey(args[param]), pos, name+", which lists "+param.Name()+" under modifies,")
		}
	}
}

// noteAssertedFile states, under the declaration, that a *os.File taken out
// of an interface value by an assertion is covered as the value is: the
// file is what the value reads (F5 of the review of the facts of step 2).
func (v *fnVerifier) noteAssertedFile(st *state, x *logic.Term, from, target types.Type, held value, holds *logic.Term) {
	if v.inputsOf() == nil || isError(from) || len(held) < 2 {
		return
	}
	if object, isPointer := pointee(target); !isPointer || !isOSFile(object) {
		return
	}
	st.assume(logic.Implies(holds, logic.Iff(logic.Select(endsOfKeys, pkey(held)), logic.Select(endsOfKeys, skey(x)))))
}

// noteBody states, under the declaration, that the value read from a field
// a progresses declaration names, as the Body of a request, is a reader the
// declaration covers: the server made it, and verified code does not store
// into the field (F4 of the design review of F39). The Body of a response
// is not such a field.
func (v *fnVerifier) noteBody(st *state, e ast.Expr, val value) {
	if v.inputsOf() == nil || len(val) != 1 || !isIface(v.info.TypeOf(e)) || !v.progresses(e) {
		return
	}
	// A nil body holds nothing to read (F11 of the review of step 2).
	st.assume(logic.Implies(logic.Ne(val[0], logic.RefLit(0)), logic.Select(endsOfKeys, skey(val[0]))))
}

// inputsWord is the word of a shipped clause that stands for the bytes
// declared under inputs, as Memory stands for the memory declared, and
// readerWords the words of a clause that speaks of inputs that end.
var (
	inputsWord  = regexp.MustCompile(`\bInputs\b`)
	readerWords = regexp.MustCompile(`\bInputs\b|\b(ends|unread)\s*\(`)
)

// withInputs returns the formulas of a shipped entry with Inputs written
// as the bytes declared. An entry that names Inputs is one of a function
// that returns only for an input that ends, as os.ReadFile, so without the
// declaration it cannot be used, and the defect says what to do.
func (pv *pkgVerifier) withInputs(fn *funcInfo, entry *trustEntry, formulas []trustFormula) []trustFormula {
	// An entry whose requires or ensures name Inputs is of a function that
	// returns only for an input that ends, as os.ReadFile.
	if !entry.file.shipped || !slices.ContainsFunc(slices.Concat(entry.requires, entry.ensures), func(f trustFormula) bool { return inputsWord.MatchString(f.text) }) {
		return formulas
	}
	decl := pv.inputsOf()
	fn.inputsOnly = decl != nil
	if decl == nil {
		if !slices.ContainsFunc(fn.defects, func(d string) bool { return strings.Contains(d, "returns only for an input that ends") }) {
			fn.defect("%s returns only for an input that ends, which is known only where the trust file declares that inputs end; "+
				"declare inputs in vego-trusted.yaml, or read with a loop of a bounded number of reads", entry.key)
		}
		// The clauses that speak of inputs mean nothing here, and the entry
		// is not used: one defect says why, whichever clause is read first.
		return slices.DeleteFunc(slices.Clone(formulas), func(f trustFormula) bool { return readerWords.MatchString(f.text) })
	}
	out := make([]trustFormula, len(formulas))
	for i, f := range formulas {
		if !inputsWord.MatchString(f.text) {
			out[i] = f
			continue
		}
		text := inputsWord.ReplaceAllString(f.text, decl.bytes.String())
		node, err := logic.ParseFormula(text)
		if err != nil {
			panic("vego: internal error: a clause with Inputs cannot be read: " + err.Error())
		}
		out[i] = trustFormula{text, f.line, f.col, node}
	}
	return out
}

// withInputsText writes Inputs in the text of a declared clause as the
// bytes declared under inputs; an entry that names it is used only under
// that declaration (withInputs).
func (pv *pkgVerifier) withInputsText(text string) string {
	if decl := pv.inputsOf(); decl != nil {
		return inputsWord.ReplaceAllString(text, decl.bytes.String())
	}
	return text
}

// requiresEnds reports whether the Requires of a contract names ends of a
// parameter itself, as in ends(r).
func requiresEnds(fn *funcInfo, param *types.Var) bool {
	found := false
	var visit func(n *logic.Node)
	visit = func(n *logic.Node) {
		if n == nil || found {
			return
		}
		if n.Kind == logic.NCall && n.Name == "ends" && len(n.Kids) == 1 && n.Kids[0].Kind == logic.NIdent && fn.paramNames[n.Kids[0].Name] == param {
			found = true
			return
		}
		for _, kid := range n.Kids {
			visit(kid)
		}
	}
	for _, c := range fn.requires {
		visit(c.node)
	}
	return found
}

// endsPairs returns the pairs of parameters of a verified function that
// N2's assumption keeps apart: a reader the Requires says ends, and every
// other parameter that is an interface value, through which the function
// may write. Callers do not pass, beside a reader under ends, a writer that
// writes what it reads: not one value twice, which keys tell apart, and,
// from code that is not verified, not two values over one file or buffer.
func endsPairs(fn *funcInfo) [][2]*types.Var {
	var pairs [][2]*types.Var
	for _, r := range fn.params {
		if !isIface(r.Type()) || !requiresEnds(fn, r) {
			continue
		}
		for _, w := range fn.params {
			if w != r && isIface(w.Type()) && !isError(w.Type()) {
				pairs = append(pairs, [2]*types.Var{r, w})
			}
		}
	}
	return pairs
}

// noteEndsPairs states N2's assumption on entry to a verified function:
// the reader under ends and each other interface parameter are not one
// value, unless one of them is nil.
func (v *fnVerifier) noteEndsPairs(st *state) {
	fn := v.fn
	if v.inputsOf() == nil || fn.decl == nil || fn.spelled != nil {
		return
	}
	for _, pair := range endsPairs(fn) {
		r, w := v.entry[pair[0]], v.entry[pair[1]]
		if r == nil || w == nil {
			continue
		}
		st.assume(v.apartReaderWriter(r[0], w[0]))
	}
}

// apartReaderWriter says that two interface values are not one value at
// the key of the reader's budget, unless one is nil.
func (v *fnVerifier) apartReaderWriter(r, w *logic.Term) *logic.Term {
	return logic.Or(logic.Eq(r, logic.RefLit(0)), logic.Eq(w, logic.RefLit(0)), logic.Ne(skey(r), skey(w)))
}

// checkEndsPairs proves N2's assumption at a call of a verified function
// under the declaration: what is passed for its reader under ends and for
// each other interface parameter are not one value.
func (v *fnVerifier) checkEndsPairs(fn *funcInfo, name string, args map[*types.Var]value, st *state, guard []*logic.Term, pos token.Pos) {
	if v.inputsOf() == nil || fn.trust != nil || fn.valueOf != nil || fn.methodOf != nil {
		return
	}
	for _, pair := range endsPairs(fn) {
		r, w := args[pair[0]], args[pair[1]]
		if len(r) != 1 || len(w) != 1 {
			continue
		}
		v.check(st, guard, v.apartReaderWriter(r[0], w[0]), pos,
			"what is passed to %s as %s, a reader it requires to end, and as %s may be one value, and %s relies on %s not writing what %s reads; pass a writer apart from the reader",
			name, pair[0].Name(), pair[1].Name(), name, pair[1].Name(), pair[0].Name())
	}
}

// readRewinds reads the rewinds of an entry: the parameters, or the
// receiver of a method of an interface, through which the function may make
// a source yield again bytes already read from it, as a seek back or an
// UnreadByte does. Every other entry claims that it does not, of any source
// through any value (What a proof assumes). Under the declaration that
// inputs end an entry that rewinds cannot be used by verified code, whose
// budgets of what is left to read the call would make wrong: the defect
// stops a call of it, a deferred call, a call through a value of its type,
// a value made of it, and a conversion checked against it alike, since
// every use goes through usable (F17 of the review of step 5 of F39, as the
// orchestrator narrowed it).
func (pv *pkgVerifier) readRewinds(fn *funcInfo, entry *trustEntry) {
	var named []string
	for _, item := range entry.rewinds {
		if fn.paramNames[item.text] == nil && (fn.receiver == nil || fn.receiver.Name() != item.text) {
			fn.defect("its rewinds %q: %s is not a parameter", item.text, item.text)
			continue
		}
		named = append(named, item.text)
	}
	if len(named) > 0 && pv.inputsOf() != nil {
		fn.defect("it may make a reader yield again what it already yielded, through %s, as its rewinds says, "+
			"which verified code may not do under the declaration that inputs end; open the file again, which gives a new value with a budget of its own", strings.Join(named, " and "))
	}
}
