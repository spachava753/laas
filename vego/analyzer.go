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

func newAnalyzer() *analysis.Analyzer {
	maxSteps, audit := 0, false
	analyzer := &analysis.Analyzer{
		Name: "vego",
		Doc: `verifies functions against their //@ specifications

vego proves that functions annotated with //@ Requires, //@ Ensures,
//@ Invariant, //@ Variant, //@ Measure, and //@ Assert comments meet their
contracts, terminate, and cannot index out of bounds, divide by zero, or reach
a panic. Functions without annotations are not analyzed. With the audit flag
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
	analyzer.Run = func(pass *analysis.Pass) (any, error) {
		pv := &pkgVerifier{
			pass:     pass,
			info:     pass.TypesInfo,
			res:      logic.NewResolver(),
			funcs:    map[*types.Func]*funcInfo{},
			reported: map[string]bool{},
			outcomes: map[*funcInfo]*outcome{},
			mutated:  map[*types.Var]bool{},
			maxSteps: maxSteps,
		}
		pv.collect()
		for _, fn := range pv.order {
			if !fn.annotated() || fn.broken {
				continue
			}
			pv.verified(fn)
			if audit {
				pv.run(fn, (*fnVerifier).audit)
			}
		}
		return nil, nil
	}
	return analyzer
}

// clause is one annotation: a keyword followed by a formula, possibly
// continued over several comment lines.
type clause struct {
	kind string
	text string
	pos  token.Pos
	node *logic.Node
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
}

func (f *funcInfo) annotated() bool {
	return len(f.requires)+len(f.ensures)+len(f.body) > 0 || f.measure != nil
}

type pkgVerifier struct {
	pass     *analysis.Pass
	info     *types.Info
	res      *logic.Resolver
	funcs    map[*types.Func]*funcInfo
	order    []*funcInfo
	reported map[string]bool
	mutated  map[*types.Var]bool
	maxSteps int
	outcomes map[*funcInfo]*outcome
	// sentinels are the package-level error variables known to be non-nil.
	sentinels map[*types.Var]bool
}

// report emits a diagnostic once per position and message. Symbolic execution
// visits a statement once per path, so the same failure can be found often.
func (pv *pkgVerifier) report(pos token.Pos, format string, args ...any) {
	msg := "vego: " + fmt.Sprintf(format, args...)
	key := fmt.Sprintf("%d %s", pos, msg)
	if pv.reported[key] {
		return
	}
	pv.reported[key] = true
	pv.pass.Report(analysis.Diagnostic{Pos: pos, Message: msg})
}

var (
	annotationLine = regexp.MustCompile(`^//\s?@(\s*)(.*)$`)
	clauseKinds    = map[string]bool{
		"Requires": true, "Ensures": true, "Invariant": true, "Variant": true,
		"Measure": true, "Predicate": true, "Assert": true,
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
// some other tool and is ignored.
func extractClauses(group *ast.CommentGroup) []*clause {
	var clauses []*clause
	var current *clause
	for _, comment := range group.List {
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
		case match[1] != "":
			clauses = append(clauses, &clause{text: keyword, pos: comment.Pos()})
		}
	}
	return clauses
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
				if c.kind == "" {
					pv.report(c.pos, "unknown annotation %q; an annotation starts with one of "+
						"Requires, Ensures, Invariant, Variant, Measure, Assert, Predicate", c.text)
					continue
				}
				if plannedKinds[c.kind] {
					pv.report(c.pos, "%s annotations are not supported yet", c.kind)
					continue
				}
				owner := pv.place(file, group, c)
				if c.kind == "Predicate" {
					decl, err := logic.ParsePredicate(c.text)
					if err != nil {
						pv.report(c.pos, "syntax error in Predicate annotation: %v", err)
						continue
					}
					predicates = append(predicates, decl)
					predicateClauses[decl] = c
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
	}
	pv.analyzeMutation()
	pv.findSentinels()
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

func (pv *pkgVerifier) addFunc(decl *ast.FuncDecl) {
	obj, ok := pv.info.Defs[decl.Name].(*types.Func)
	if !ok {
		return
	}
	fn := &funcInfo{decl: decl, obj: obj, paramNames: map[string]*types.Var{}, resultNames: map[string]int{}}
	sig := obj.Type().(*types.Signature)
	for i := range sig.Params().Len() {
		param := sig.Params().At(i)
		fn.params = append(fn.params, param)
		fn.paramNames[param.Name()] = param
	}
	for i := range sig.Results().Len() {
		result := sig.Results().At(i)
		fn.results = append(fn.results, result)
		if result.Name() != "" {
			fn.resultNames[result.Name()] = i
		}
	}
	// Unnamed results are called result, or result1, result2, ... when
	// there are several.
	for i := range sig.Results().Len() {
		switch {
		case sig.Results().At(i).Name() != "":
		case sig.Results().Len() == 1:
			fn.resultNames["result"] = 0
		default:
			fn.resultNames[fmt.Sprintf("result%d", i+1)] = i
		}
	}
	pv.funcs[obj] = fn
	pv.order = append(pv.order, fn)
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

// analyzeMutation decides for every parameter whether its function may write
// through it. A parameter is read-only when it only occurs as the operand of
// len, as the sequence of a range loop, indexed for reading, or passed to a
// function of this package that treats the matching parameter as read-only.
// The last rule is a least fixed point over the call graph.
func (pv *pkgVerifier) analyzeMutation() {
	passedTo := map[*types.Var][]*types.Var{}
	for _, fn := range pv.order {
		if fn.decl.Body == nil {
			for _, param := range fn.params {
				pv.mutated[param] = true
			}
			continue
		}
		harmless := map[*ast.Ident]bool{}
		read := func(e ast.Expr) *types.Var {
			id, ok := ast.Unparen(e).(*ast.Ident)
			if !ok {
				return nil
			}
			harmless[id] = true
			variable, _ := pv.info.Uses[id].(*types.Var)
			return variable
		}
		var stack []ast.Node
		ast.Inspect(fn.decl.Body, func(n ast.Node) bool {
			if n == nil {
				stack = stack[:len(stack)-1]
				return true
			}
			switch n := n.(type) {
			case *ast.IndexExpr:
				if readOnlyUse(n, stack) {
					read(n.X)
				}
			case *ast.RangeStmt:
				read(n.X)
			case *ast.CallExpr:
				if isBuiltin(pv.info, n, "len") {
					read(n.Args[0])
				}
				callee := pv.funcs[typeutil.StaticCallee(pv.info, n)]
				for i, arg := range n.Args {
					if callee == nil || i >= len(callee.params) {
						break
					}
					if variable := read(arg); variable != nil {
						passedTo[variable] = append(passedTo[variable], callee.params[i])
					}
				}
			}
			stack = append(stack, n)
			return true
		})
		ast.Inspect(fn.decl.Body, func(n ast.Node) bool {
			if id, ok := n.(*ast.Ident); ok && !harmless[id] {
				if variable, ok := pv.info.Uses[id].(*types.Var); ok {
					pv.mutated[variable] = true
				}
			}
			return true
		})
	}
	for changed := true; changed; {
		changed = false
		for variable, targets := range passedTo {
			if !pv.mutated[variable] && slices.ContainsFunc(targets, func(t *types.Var) bool { return pv.mutated[t] }) {
				pv.mutated[variable], changed = true, true
			}
		}
	}
}

// readOnlyUse reports whether an element expression is only read. Every
// context that can write through it, or hand out its address, counts as a
// write: assignment and range targets, increments, the address operator, and
// selectors, which may call a pointer method on the element.
func readOnlyUse(element *ast.IndexExpr, ancestors []ast.Node) bool {
	var use ast.Node = element
	for i := len(ancestors) - 1; i >= 0; i-- {
		parent := ancestors[i]
		switch parent := parent.(type) {
		case *ast.ParenExpr:
			use = parent
			continue
		case *ast.AssignStmt:
			return !slices.Contains(parent.Lhs, use.(ast.Expr))
		case *ast.RangeStmt:
			return parent.Key != use && parent.Value != use
		case *ast.IncDecStmt, *ast.SelectorExpr, *ast.SliceExpr:
			return false
		case *ast.IndexExpr:
			return parent.X != use
		case *ast.UnaryExpr:
			return parent.Op != token.AND
		}
		return true
	}
	return true
}

// mutates reports whether a function may write to the elements of a slice
// parameter. Only functions that are themselves verified can be known to
// leave a slice alone; every other callee is assumed to write it.
func (pv *pkgVerifier) mutates(fn *funcInfo, param *types.Var) bool {
	return fn == nil || !fn.annotated() || fn.broken || pv.mutated[param]
}

func isBuiltin(info *types.Info, call *ast.CallExpr, name string) bool {
	id, ok := ast.Unparen(call.Fun).(*ast.Ident)
	if !ok {
		return false
	}
	builtin, ok := info.Uses[id].(*types.Builtin)
	return ok && builtin.Name() == name
}

// sortOf maps a Go type to the logical sort that models it.
func sortOf(t types.Type) (logic.Sort, bool) {
	if t == nil {
		return 0, false
	}
	basic := func(t types.Type) (logic.Sort, bool) {
		b, ok := t.Underlying().(*types.Basic)
		switch {
		case ok && b.Info()&types.IsInteger != 0 && b.Kind() != types.Uintptr:
			return logic.Int, true
		case ok && b.Info()&types.IsBoolean != 0:
			return logic.Bool, true
		case ok && b.Info()&types.IsFloat != 0:
			return logic.Float, true
		}
		return 0, false
	}
	switch {
	case types.Identical(t, types.Universe.Lookup("error").Type()):
		return logic.Err, true
	case isSlice(t):
		elem, ok := basic(t.Underlying().(*types.Slice).Elem())
		return logic.SeqOf(elem), ok
	case isString(t):
		return logic.IntSeq, true
	}
	return basic(t)
}
