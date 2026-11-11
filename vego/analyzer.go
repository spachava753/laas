// Package vego is a deductive verifier for Go functions whose specifications
// are written in //@ comment annotations, following the VeGo paper (Masoudi
// and Dutchyn, "VeGo: A Lightweight Deductive Verification System for Go",
// arXiv:2608.22630).
//
// A function opts in by carrying at least one annotation. The verifier then
// executes the function symbolically, generates verification conditions for
// its contract, for loop invariants and termination, and for runtime safety
// (slice bounds, division by zero, reachable panics), and discharges them with
// the native deduction engine in the internal solver package. Every condition
// that cannot be proved is reported as a diagnostic.
package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"reflect"
	"regexp"
	"slices"
	"sort"
	"strings"
	"unicode"

	"github.com/spachava753/laas/vego/internal/logic"
	"golang.org/x/tools/go/analysis"
	"golang.org/x/tools/go/types/typeutil"
)

// Analyzer verifies annotated functions and reports every proof obligation it
// cannot discharge.
var Analyzer = newAnalyzer()

// refuseCache makes the analyzer decline to verify; see RefuseCachedRuns.
var refuseCache bool

// RefuseCachedRuns must be called by a driver whose results are cached by
// something that does not know about trust files, as go vet does with its
// -vettool. Such a cache would keep a proof, and the contract a package
// published from it, after the trusted contracts it rests on have changed.
// The analyzer then verifies nothing and reports every package that has
// annotations instead.
func RefuseCachedRuns() { refuseCache = true }

// newAnalyzer builds the analyzer with its flags. A run loads the trusted
// contracts, collects the annotations of the package, verifies every
// annotated function, applies the always-fails rule, and publishes the
// verified contracts and the trust the proofs rest on. For a caching driver
// it only reports that nothing was verified.
func newAnalyzer() *analysis.Analyzer {
	maxSteps, audit, trustPath := 0, false, ""
	analyzer := &analysis.Analyzer{
		Name: "vego",
		Doc: `verifies functions against their //@ specifications

vego proves that functions annotated with //@ Requires, //@ Ensures,
//@ Modifies, //@ Invariant, //@ Variant, //@ Measure, and //@ Assert comments
meet their contracts, terminate, write only what they say they write, and
cannot index out of bounds, follow a nil pointer, divide by zero, or reach a
panic. Functions without annotations are not analyzed. With the audit flag
it also reports postconditions weak enough for a degenerate implementation.`,
		URL: "https://github.com/spachava753/laas#vego",
	}
	analyzer.Flags.IntVar(
		&maxSteps,
		"max-steps",
		0,
		"arithmetic checks the solver may spend on one proof obligation (0 selects the default)",
	)
	analyzer.Flags.BoolVar(
		&audit,
		"audit",
		false,
		"also report postconditions that degenerate implementations satisfy",
	)
	analyzer.Flags.StringVar(
		&trustPath,
		"trusted",
		"",
		"file of trusted contracts to use instead of "+TrustFileName+" next to go.mod",
	)
	analyzer.ResultType = reflect.TypeFor[*Usage]()
	analyzer.FactTypes = []analysis.Fact{new(contractFact), new(predicatesFact), new(usageFact), new(invariantFact), new(sentinelFact)}
	analyzer.Run = func(pass *analysis.Pass) (any, error) {
		pv := &pkgVerifier{
			pass:          pass,
			info:          pass.TypesInfo,
			res:           logic.NewResolver(),
			funcs:         map[*types.Func]*funcInfo{},
			reported:      map[string]bool{},
			outcomes:      map[*funcInfo]*outcome{},
			trusted:       map[*types.Func]*funcInfo{},
			origins:       map[*ast.BlockStmt]*origins{},
			knownReturns:  map[*funcInfo]bool{},
			isParameter:   map[*types.Var]bool{},
			invariants:    map[*types.TypeName]*invariantSet{},
			foreignBroken: map[*types.Package]bool{},
			imported:      map[*types.Func]*funcInfo{},
			foreign:       map[*types.Package]*logic.Resolver{},
			plain:         logic.NewResolver(),
			trustSources:  map[*trustFile]*token.File{},
			maxSteps:      maxSteps,
		}
		if refuseCache {
			pv.usage = &Usage{}
			pv.collect()
			// A package without annotations has nothing to verify and
			// draws no report.
			for _, fn := range pv.order {
				if fn.annotated() {
					pv.report(fn.decl.Name.Pos(), "verification does not run under go vet, whose cache would keep "+
						"proofs after the trusted contracts they rest on have changed; run laas directly")
					break
				}
			}
			return pv.usage, nil
		}
		pv.loadTrust(trustPath)
		pv.collect()
		pv.checkInvariantsDeclared()
		pv.exportInvariants()
		for _, fn := range pv.order {
			if !fn.annotated() || fn.broken {
				continue
			}
			pv.verified(fn)
			if audit {
				pv.run(fn, (*fnVerifier).audit)
			}
		}
		pv.exportContracts(pv.reportAlwaysFailing())
		for variable := range pv.relied {
			pass.ExportObjectFact(variable, new(sentinelFact))
		}
		// The proofs of this package also rest on whatever the packages it
		// depends on took on trust.
		pass.ExportPackageFact(&usageFact{Usage: *pv.usage})
		total := &Usage{}
		total.add(pv.usage)
		for _, published := range pass.AllPackageFacts() {
			if dependency, ok := published.Fact.(*usageFact); ok && published.Package != pass.Pkg {
				total.add(&dependency.Usage)
			}
		}
		return total, nil
	}
	return analyzer
}

// clause is one annotation: a keyword followed by a formula, possibly
// continued over several comment lines.
type clause struct {
	kind string
	text string
	pos  token.Pos
	// misplaced is set, in place of a kind, for something that looks like
	// an annotation but is written where annotations are not read.
	misplaced string
	node      *logic.Node
	// res is set for a clause written in another package, which has its
	// own predicates.
	res *logic.Resolver
}

// funcInfo is a function declaration together with its bound annotations.
type funcInfo struct {
	decl        *ast.FuncDecl
	obj         *types.Func
	requires    []*clause
	ensures     []*clause
	measure     *clause
	body        []*clause // Invariant, Variant, and Assert clauses in source order
	params      []*types.Var
	results     []*types.Var
	paramNames  map[string]*types.Var
	resultNames map[string]int
	broken      bool // an annotation failed to parse; verification is skipped
	callees     []*funcInfo
	// modifies lists what the function may write, from its Modifies clauses.
	modifies []*modTarget
	// trust is set for a function whose contract comes from a trust file
	// instead of annotations; such a function is not verified.
	trust   *trustEntry
	defects []string  // what is wrong with a trusted or imported contract
	use     *EntryUse // the report entry of a trusted contract in use
	// imported is set for a function verified in another package, whose
	// contract was published by that package.
	imported *contractFact
	// failed is set when verifying the function reported a problem.
	failed bool
	// forces caches whether a trusted contract forces success for some
	// input; see forcesSuccess.
	forces *bool
}

func (f *funcInfo) annotated() bool {
	return len(f.requires)+len(f.ensures)+len(f.body)+len(f.modifies) > 0 || f.measure != nil
}

type pkgVerifier struct {
	pass     *analysis.Pass
	info     *types.Info
	res      *logic.Resolver
	funcs    map[*types.Func]*funcInfo
	order    []*funcInfo
	reported map[string]bool
	maxSteps int
	outcomes map[*funcInfo]*outcome
	// projectTrust is the project's file of trusted contracts, trusted the
	// contracts built from it and from the shipped ones, and usage what the
	// proofs of this package rely on.
	projectTrust *trustFile
	trusted      map[*types.Func]*funcInfo
	trustSources map[*trustFile]*token.File
	usage        *Usage
	// imported holds the contracts of functions verified in other
	// packages, and foreign the predicates of those packages.
	imported map[*types.Func]*funcInfo
	foreign  map[*types.Package]*logic.Resolver
	// plain resolves trusted contracts, which may use no predicates.
	plain *logic.Resolver
	// predicateTexts are the predicate definitions of this package, and
	// predicatesBroken is set when one of them could not be accepted.
	// foreignBroken holds the packages whose predicates could not be read.
	predicateTexts   []string
	predicatesBroken bool
	foreignBroken    map[*types.Package]bool
	// current is the function being verified, which a diagnostic counts
	// against.
	current *funcInfo
	// sentinels are the package-level error variables known to be non-nil,
	// and relied those among them a proof has used. unsettled holds the
	// ones that would be sentinels if no code of the package could run
	// before they are initialised, with what stands in the way.
	sentinels map[*types.Var]bool
	relied    map[*types.Var]bool
	unsettled map[*types.Var]string
	// origins caches what the variables of each function body are assigned,
	// knownReturns holds the functions that only return errors of known
	// origin, and isParameter the parameters of all functions.
	origins      map[*ast.BlockStmt]*origins
	knownReturns map[*funcInfo]bool
	isParameter  map[*types.Var]bool
	// invariants holds the invariants of struct types, nil for a type known
	// to have none.
	invariants map[*types.TypeName]*invariantSet
}

// report emits a diagnostic once per position and message. Symbolic execution
// visits a statement once per path, so the same failure can be found often.
func (pv *pkgVerifier) report(pos token.Pos, format string, args ...any) {
	if pv.current != nil {
		pv.current.failed = true
	}
	msg := "vego: " + fmt.Sprintf(format, args...)
	key := fmt.Sprintf("%d %s", pos, msg)
	if pv.reported[key] {
		return
	}
	pv.reported[key] = true
	pv.pass.Report(analysis.Diagnostic{Pos: pos, Message: msg})
}

var (
	annotationLine  = regexp.MustCompile(`^//\s*@(\s*)(.*)$`)
	blockAnnotation = regexp.MustCompile(`(?m)^(?:/\*)?[\s*]*@\s*(\w*)`)
	clauseKinds     = map[string]bool{
		"Requires": true, "Ensures": true, "Invariant": true, "Variant": true,
		"Measure": true, "Predicate": true, "Assert": true, "Modifies": true,
	}
	// plannedKinds are annotations of the VeGo paper that this implementation
	// does not support yet.
	plannedKinds = map[string]bool{"Preserves": true, "Immutable": true, "Cost": true, "Library": true}
)

// extractClauses splits a comment group into annotation clauses. A line that
// starts with a keyword opens a clause, and following annotation lines that do
// not start with a keyword continue it. Both the //@ form and the // @ form
// that gofmt produces inside doc comments are accepted, and a // inside an
// annotation line starts an ordinary comment.
//
// An @ followed by whitespace always marks an annotation, so an unknown word
// there is returned as a clause without a kind, to be reported, instead of
// being skipped: a misspelt keyword must not switch verification off. An @
// directly followed by an unknown word, as in "// @Summary", belongs to
// some other tool and is ignored, unless the word is a keyword but for its
// case or a letter or two. A keyword in a /* */ comment is reported too,
// since annotations are only read from // comments.
func extractClauses(group *ast.CommentGroup) []*clause {
	var clauses []*clause
	var current *clause
	for _, comment := range group.List {
		if strings.HasPrefix(comment.Text, "/*") {
			for _, block := range blockAnnotation.FindAllStringSubmatch(comment.Text, -1) {
				if nearKeyword(block[1]) {
					clauses = append(clauses, &clause{text: block[1], pos: comment.Pos(),
						misplaced: "annotations are only read from // comments, not from /* */ comments"})
					break
				}
			}
		}
		match := annotationLine.FindStringSubmatch(comment.Text)
		if match == nil {
			current = nil
			continue
		}
		line, _, _ := strings.Cut(match[2], "//")
		line = strings.TrimSpace(line)
		keyword := line
		if end := strings.IndexFunc(line, unicode.IsSpace); end >= 0 {
			keyword = line[:end]
		}
		switch {
		case clauseKinds[keyword] || plannedKinds[keyword]:
			current = &clause{kind: keyword, text: strings.TrimSpace(line[len(keyword):]), pos: comment.Pos()}
			clauses = append(clauses, current)
		case current != nil:
			current.text += " " + line
		case match[1] != "" || nearKeyword(keyword):
			clauses = append(clauses, &clause{text: keyword, pos: comment.Pos()})
		}
	}
	return clauses
}

// nearKeyword reports whether a word is an annotation keyword, or so close
// to one that it was most likely meant as one: the same but for case, or one
// or two letters away.
func nearKeyword(word string) bool {
	for keyword := range clauseKinds {
		if strings.EqualFold(word, keyword) || distance(word, keyword) <= 2 {
			return true
		}
	}
	return false
}

// distance returns how many letters have to be added, dropped, or replaced
// to turn one word into the other.
func distance(a, b string) int {
	row := make([]int, len(b)+1)
	for j := range row {
		row[j] = j
	}
	for i := 1; i <= len(a); i++ {
		diagonal := row[0]
		row[0] = i
		for j := 1; j <= len(b); j++ {
			above := row[j]
			if a[i-1] != b[j-1] {
				diagonal++
			}
			row[j] = min(diagonal, above+1, row[j-1]+1)
			diagonal = above
		}
	}
	return row[len(b)]
}

// collect records every function of the package, parses all annotations, and
// binds each clause to the function it specifies.
func (pv *pkgVerifier) collect() {
	var predicates []*logic.PredDecl
	predicateClauses := map[*logic.PredDecl]*clause{}
	for _, file := range pv.pass.Files {
		for _, decl := range file.Decls {
			if fd, ok := decl.(*ast.FuncDecl); ok {
				pv.addFunc(fd)
			}
		}
		for _, group := range file.Comments {
			for _, c := range extractClauses(group) {
				if c.misplaced != "" {
					pv.report(c.pos, "%s", c.misplaced)
					continue
				}
				if c.kind == "" {
					pv.report(c.pos, "unknown annotation %q; an annotation starts with one of "+
						"Requires, Ensures, Modifies, Invariant, Variant, Measure, Assert, Predicate", c.text)
					continue
				}
				if plannedKinds[c.kind] {
					pv.report(c.pos, "%s annotations are not supported yet", c.kind)
					continue
				}
				if name, ok := pv.typeDocumented(file, group); ok {
					pv.addInvariant(name, c)
					continue
				}
				owner := pv.place(file, group, c)
				if c.kind == "Predicate" {
					decl, err := logic.ParsePredicate(c.text)
					if err != nil {
						pv.report(c.pos, "syntax error in Predicate annotation: %v", err)
						pv.predicatesBroken = true
						continue
					}
					predicates = append(predicates, decl)
					predicateClauses[decl] = c
					pv.predicateTexts = append(pv.predicateTexts, c.text)
					continue
				}
				if c.kind == "Modifies" {
					targets, err := logic.ParseTargets(c.text)
					switch {
					case err != nil:
						pv.report(c.pos, "syntax error in Modifies annotation: %v", err)
						if owner != nil {
							owner.broken = true
						}
					case owner != nil:
						owner.modifies = append(owner.modifies, newModTargets(targets, c)...)
					}
					continue
				}
				node, err := logic.ParseFormula(c.text)
				if err != nil {
					pv.report(c.pos, "syntax error in %s annotation: %v", c.kind, err)
					if owner != nil {
						owner.broken = true
					}
					continue
				}
				c.node = node
			}
		}
	}
	for _, defineErr := range pv.res.Define(predicates) {
		pv.report(predicateClauses[defineErr.Decl].pos, "%v", defineErr.Err)
		// A predicate that could not be defined stands for nothing, so no
		// proof of this package that may have used it counts.
		pv.predicatesBroken = true
	}
	pv.findSentinels()
	pv.findKnownReturns()
	for _, fn := range pv.order {
		if fn.annotated() && pv.trustedContract(fn.obj) != nil {
			pv.report(fn.decl.Name.Pos(), "%s has //@ annotations and a trusted contract; "+
				"a function is either verified or trusted, not both", fn.obj.Name())
		}
	}
	for _, fn := range pv.order {
		sort.Slice(fn.body, func(i, j int) bool { return fn.body[i].pos < fn.body[j].pos })
		if fn.decl.Body == nil {
			continue
		}
		pv.checkPlacement(fn)
		ast.Inspect(fn.decl.Body, func(n ast.Node) bool {
			if call, ok := n.(*ast.CallExpr); ok {
				if callee := pv.funcs[typeutil.StaticCallee(pv.info, call)]; callee != nil {
					fn.callees = append(fn.callees, callee)
				}
			}
			return true
		})
	}
}

// addFunc records a function declaration with the names annotations may use
// for its parameters and results. Blank and unnamed parameters get no name;
// unnamed results are called result, or result1, result2, ... when there are
// several.
func (pv *pkgVerifier) addFunc(decl *ast.FuncDecl) {
	obj, ok := pv.info.Defs[decl.Name].(*types.Func)
	if !ok {
		return
	}
	fn := newFuncInfo(obj)
	fn.decl = decl
	pv.funcs[obj] = fn
	pv.order = append(pv.order, fn)
}

// newFuncInfo describes a function by its signature, with the names
// annotations and trusted contracts may use for its parameters and results.
// The receiver of a method is its first parameter.
func newFuncInfo(obj *types.Func) *funcInfo {
	fn := &funcInfo{obj: obj, paramNames: map[string]*types.Var{}, resultNames: map[string]int{}}
	sig := obj.Type().(*types.Signature)
	inputs := slices.Collect(sig.Params().Variables())
	if sig.Recv() != nil {
		inputs = append([]*types.Var{sig.Recv()}, inputs...)
	}
	for _, param := range inputs {
		fn.params = append(fn.params, param)
		// A blank or unnamed parameter cannot be referred to.
		if param.Name() != "" && param.Name() != "_" {
			fn.paramNames[param.Name()] = param
		}
	}
	for i := range sig.Results().Len() {
		result := sig.Results().At(i)
		fn.results = append(fn.results, result)
		if result.Name() != "" && result.Name() != "_" {
			fn.resultNames[result.Name()] = i
		}
	}
	// Unnamed results are called result, or result1, result2, ... when
	// there are several.
	for i := range sig.Results().Len() {
		name := fmt.Sprintf("result%d", i+1)
		if sig.Results().Len() == 1 {
			name = "result"
		}
		// A name the function itself gives to a result always wins.
		_, taken := fn.resultNames[name]
		if declared := sig.Results().At(i).Name(); (declared == "" || declared == "_") && !taken {
			fn.resultNames[name] = i
		}
	}
	return fn
}

// ambiguous reports whether an annotation of the function would read the
// name of a Go variable as something else: True, False, and nil are words of
// the annotation language, and result, or result1, result2, ..., is how an
// unnamed result is referred to.
//
// Only a name that an annotation of the function actually uses is in doubt.
func (fn *funcInfo) ambiguous(name string) bool {
	index, isResult := fn.resultNames[name]
	if name != "True" && name != "False" && name != "nil" && (!isResult || fn.results[index].Name() == name) {
		return false
	}
	used := slices.ContainsFunc(fn.modifies, func(m *modTarget) bool { return m.name == name })
	clauses := slices.Concat(fn.requires, fn.ensures, fn.body)
	if fn.measure != nil {
		clauses = append(clauses, fn.measure)
	}
	for _, c := range clauses {
		c.node.Walk(func(n *logic.Node) {
			switch {
			case n.Kind == logic.NBool:
				used = used || name == map[int64]string{0: "False", 1: "True"}[n.Val]
			case n.Kind == logic.NNil:
				used = used || name == "nil"
			case n.Kind == logic.NIdent:
				used = used || name == n.Name
			}
		})
	}
	return used
}

// contractOf returns the contract that calls to a function are checked
// against: its annotations when it is verified, otherwise its trusted
// contract. It returns nil for a function that has neither.
func (pv *pkgVerifier) contractOf(callee *types.Func) *funcInfo {
	if own := pv.funcs[callee]; own != nil && own.annotated() {
		return own
	}
	if imported := pv.importedContract(callee); imported != nil {
		if pv.trustedContract(callee) != nil {
			imported.defect("it is verified in its own package and also has a trusted contract")
		}
		return imported
	}
	return pv.trustedContract(callee)
}

// place binds a clause to a function and returns that function. Clauses inside
// a body annotate statements. Outside, a clause in a function's doc comment
// belongs to that function, and a detached Ensures clause belongs to the
// function that ends just before it.
func (pv *pkgVerifier) place(file *ast.File, group *ast.CommentGroup, c *clause) *funcInfo {
	var previous, next *ast.FuncDecl
	for _, decl := range file.Decls {
		fd, _ := decl.(*ast.FuncDecl)
		if decl.End() <= c.pos {
			previous = fd
			continue
		}
		if decl.Pos() > c.pos {
			next = fd
			break
		}
		if fd == nil || fd.Body == nil {
			break
		}
		fn := pv.funcs[pv.info.Defs[fd.Name].(*types.Func)]
		switch c.kind {
		case "Invariant", "Variant", "Assert":
			fn.body = append(fn.body, c)
		case "Predicate":
		default:
			pv.report(c.pos, "%s annotations belong outside the function body", c.kind)
			fn.broken = true
		}
		return fn
	}
	if c.kind == "Predicate" {
		return nil
	}
	var fn *funcInfo
	switch {
	case next != nil && next.Doc == group:
		fn = pv.funcs[pv.info.Defs[next.Name].(*types.Func)]
	case c.kind == "Ensures" && previous != nil:
		fn = pv.funcs[pv.info.Defs[previous.Name].(*types.Func)]
	default:
		pv.report(c.pos, "%s annotation is not attached to a function; "+
			"put it in the comment directly above the function", c.kind)
		return nil
	}
	switch c.kind {
	case "Modifies":
	case "Requires":
		fn.requires = append(fn.requires, c)
	case "Ensures":
		fn.ensures = append(fn.ensures, c)
	case "Measure":
		if fn.measure != nil {
			pv.report(c.pos, "function %s already has a Measure", fn.obj.Name())
		}
		fn.measure = c
	default:
		pv.report(c.pos, "%s annotations belong inside a function body", c.kind)
		fn.broken = true
	}
	return fn
}

// checkPlacement rejects body annotations that are not written between
// statements. Symbolic execution only meets annotations at statement
// boundaries, so one inside an expression or between the cases of a switch
// would otherwise never be checked.
func (pv *pkgVerifier) checkPlacement(fn *funcInfo) {
	for _, c := range fn.body {
		var innermost, parent ast.Node
		ast.Inspect(fn.decl.Body, func(n ast.Node) bool {
			if n == nil || c.pos < n.Pos() || c.pos >= n.End() {
				return false
			}
			innermost, parent = n, innermost
			return true
		})
		between := false
		switch n := innermost.(type) {
		case *ast.BlockStmt:
			switch parent.(type) {
			case *ast.SwitchStmt, *ast.TypeSwitchStmt, *ast.SelectStmt:
			default:
				between = true
			}
		case *ast.CaseClause:
			between = c.pos > n.Colon
		}
		if !between {
			pv.report(c.pos, "%s annotation must stand between statements, on a line of its own", c.kind)
			fn.broken = true
		}
	}
}

// reaches reports whether a call chain leads from one function to another.
func (pv *pkgVerifier) reaches(from, to *funcInfo) bool {
	seen := map[*funcInfo]bool{}
	var visit func(fn *funcInfo) bool
	visit = func(fn *funcInfo) bool {
		if fn == to {
			return true
		}
		if seen[fn] {
			return false
		}
		seen[fn] = true
		for _, callee := range fn.callees {
			if visit(callee) {
				return true
			}
		}
		return false
	}
	return visit(from)
}

func isBuiltin(info *types.Info, call *ast.CallExpr, name string) bool {
	id, ok := ast.Unparen(call.Fun).(*ast.Ident)
	if !ok {
		return false
	}
	builtin, ok := info.Uses[id].(*types.Builtin)
	return ok && builtin.Name() == name
}
