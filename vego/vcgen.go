package vego

import (
	"errors"
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"maps"
	"slices"
	"strings"

	"github.com/spachava753/laas/vego/internal/logic"
	"github.com/spachava753/laas/vego/internal/solver"
	"golang.org/x/tools/go/types/typeutil"
)

// maxBranches bounds the number of conditional branches explored in one
// function, since every if statement doubles the number of paths.
const maxBranches = 4000

// state is the symbolic state on one execution path: the current value of
// every tracked variable and the facts known to hold.
type state struct {
	vals map[*types.Var]*logic.Term
	hyps []*logic.Term
}

func (st *state) clone() *state {
	return &state{vals: maps.Clone(st.vals), hyps: slices.Clone(st.hyps)}
}

func (st *state) assume(fact *logic.Term) {
	if fact.Op != logic.OpTrue {
		st.hyps = append(st.hyps, fact)
	}
}

// unsupported is panicked when a function uses a construct outside the
// verified fragment; abort when an error has already been reported.
type (
	unsupported struct {
		pos token.Pos
		msg string
	}
	abort struct{}
)

// ctrl holds the continuations of the innermost enclosing loop.
type ctrl struct {
	brk  func(*state)
	cont func(*state)
}

// loopSpec collects the annotations written directly above a loop.
type loopSpec struct {
	invariants []*clause
	variant    *clause
}

type fnVerifier struct {
	*pkgVerifier
	fn       *funcInfo
	entry    map[*types.Var]*logic.Term
	names    map[string]int
	branches int
	measure  *logic.Term
	// effectful is the one call of the current statement that may modify a
	// slice: a call that is a statement of its own, the whole right-hand side
	// of an assignment to plain variables, or the only returned expression.
	// Anywhere else such a call would run between the evaluation of other
	// operands, whose order the symbolic execution does not model.
	effectful *ast.CallExpr
}

// allowEffects marks e, when it is a call, as the call of the current
// statement that may modify slices.
func (v *fnVerifier) allowEffects(e ast.Expr) {
	v.effectful, _ = ast.Unparen(e).(*ast.CallExpr)
}

// run executes one task on a function, turning the panics that abandon a
// verification into diagnostics.
func (pv *pkgVerifier) run(fn *funcInfo, task func(v *fnVerifier)) {
	v := &fnVerifier{pkgVerifier: pv, fn: fn, entry: map[*types.Var]*logic.Term{}, names: map[string]int{}}
	defer func() {
		switch r := recover().(type) {
		case nil, abort:
		case unsupported:
			pv.report(r.pos, "cannot verify %s: %s", fn.obj.Name(), r.msg)
		default:
			panic(r)
		}
	}()
	task(v)
}

// enter builds the state on function entry: parameters hold arbitrary values
// that satisfy the precondition and results hold their zero values.
func (v *fnVerifier) enter() *state {
	fn := v.fn
	if fn.decl.Body == nil {
		v.unsupported(fn.decl.Pos(), "the function has no body")
	}
	if fn.decl.Recv != nil || fn.decl.Type.TypeParams != nil {
		v.unsupported(fn.decl.Pos(), "methods and generic functions are not supported yet")
	}
	st := &state{vals: map[*types.Var]*logic.Term{}}
	for _, param := range fn.params {
		sort, ok := sortOf(param.Type())
		if !ok {
			v.unsupported(param.Pos(), fmt.Sprintf("parameter %s has unsupported type %s", param.Name(), param.Type()))
		}
		st.vals[param] = logic.Const(param.Name(), sort)
		v.entry[param] = st.vals[param]
		st.assume(v.typeFact(st.vals[param], param.Type()))
	}
	for _, result := range fn.results {
		sort, ok := sortOf(result.Type())
		if !ok {
			v.unsupported(fn.decl.Pos(), fmt.Sprintf("result type %s is not supported", result.Type()))
		}
		st.vals[result] = zero(sort)
	}
	pre := &contractEnv{pv: v.pkgVerifier, fn: fn, args: v.entry}
	for _, c := range fn.requires {
		st.assume(v.formula(c, c.node, pre))
	}
	return st
}

// verify symbolically executes one annotated function from a state that
// satisfies its precondition and checks every obligation met on the way.
func (v *fnVerifier) verify() {
	fn, st := v.fn, v.enter()
	if fn.measure != nil {
		v.measure = v.intTerm(fn.measure, &contractEnv{pv: v.pkgVerifier, fn: fn, args: v.entry})
		v.check(st, nil, logic.Le(logic.IntLit(0), v.measure), fn.decl.Name.Pos(),
			"measure may be negative: %s", fn.measure.text)
	}
	body := fn.decl.Body
	v.seq(body.List, body.Lbrace, body.Rbrace, st, ctrl{}, func(end *state) {
		results := make([]*logic.Term, len(fn.results))
		for i, result := range fn.results {
			results[i] = end.vals[result]
		}
		v.atReturn(end, results, body.Rbrace)
	})
}

func (v *fnVerifier) unsupported(pos token.Pos, msg string) {
	panic(unsupported{pos, msg})
}

func zero(sort logic.Sort) *logic.Term {
	switch sort {
	case logic.Int:
		return logic.IntLit(0)
	case logic.Bool:
		return logic.False()
	case logic.Float:
		return logic.Const("float 0", logic.Float)
	case logic.Err:
		return logic.NilErr()
	}
	return logic.Fill(logic.IntLit(0), zero(sort.Elem()))
}

// fresh returns a new symbolic constant. The @ keeps generated names apart
// from Go identifiers.
func (v *fnVerifier) fresh(base string, sort logic.Sort) *logic.Term {
	v.names[base]++
	return logic.Const(fmt.Sprintf("%s@%d", base, v.names[base]), sort)
}

// contractEnv gives meaning to the names in a function contract: parameters
// denote the values passed in, primed slice parameters the contents on return,
// and result names the returned values.
type contractEnv struct {
	pv      *pkgVerifier
	fn      *funcInfo
	args    map[*types.Var]*logic.Term
	post    map[*types.Var]*logic.Term // nil where primes are not allowed
	results []*logic.Term              // nil where results are not allowed
}

func (e *contractEnv) Var(name string, primed bool) (*logic.Term, error) {
	if param, ok := e.fn.paramNames[name]; ok {
		if !primed {
			return e.args[param], nil
		}
		if e.post == nil {
			return nil, fmt.Errorf("%s' describes the state on return and is only allowed in Ensures", name)
		}
		if !isSlice(param.Type()) {
			return nil, fmt.Errorf("%s is passed by value, so only its entry value %s is visible to callers", name, name)
		}
		return e.post[param], nil
	}
	if index, ok := e.fn.resultNames[name]; ok && !primed {
		if e.results == nil {
			return nil, fmt.Errorf("result %s can only be used in Ensures", name)
		}
		return e.results[index], nil
	}
	return e.pv.constantNamed(e.pv.pass.Pkg.Scope().Lookup(name), name)
}

func (e *contractEnv) Old(name string) (*logic.Term, error) {
	if param, ok := e.fn.paramNames[name]; ok {
		return e.args[param], nil
	}
	return nil, fmt.Errorf("old(%s): %s is not a parameter", name, name)
}

// bodyEnv gives meaning to the names in an annotation inside a function body:
// each name denotes the current value of the variable visible at pos.
type bodyEnv struct {
	v   *fnVerifier
	st  *state
	pos token.Pos
}

func (e *bodyEnv) Var(name string, primed bool) (*logic.Term, error) {
	if primed {
		return nil, fmt.Errorf("%s' is only allowed in Ensures; inside a body %s already denotes the current value", name, name)
	}
	scope := e.v.pass.Pkg.Scope().Innermost(e.pos)
	if scope == nil {
		return nil, fmt.Errorf("unknown name %s", name)
	}
	_, obj := scope.LookupParent(name, e.pos)
	if variable, ok := obj.(*types.Var); ok {
		if value := e.st.vals[variable]; value != nil {
			return value, nil
		}
		return nil, fmt.Errorf("%s cannot be used in annotations: its type %s is not supported", name, variable.Type())
	}
	return e.v.constantNamed(obj, name)
}

func (e *bodyEnv) Old(name string) (*logic.Term, error) {
	if param, ok := e.v.fn.paramNames[name]; ok {
		return e.v.entry[param], nil
	}
	return nil, fmt.Errorf("old(%s): %s is not a parameter", name, name)
}

// formula resolves a parsed annotation against an environment. Errors are
// reported at the annotation and abandon the verification of the function.
func (v *fnVerifier) formula(c *clause, node *logic.Node, env logic.Env) *logic.Term {
	t, err := v.res.Formula(node, env)
	if err != nil {
		v.report(c.pos, "in %s annotation: %v", c.kind, err)
		panic(abort{})
	}
	return t
}

func (v *fnVerifier) intTerm(c *clause, env logic.Env) *logic.Term {
	t, err := v.res.IntTerm(c.node, env)
	if err != nil {
		v.report(c.pos, "in %s annotation: %v", c.kind, err)
		panic(abort{})
	}
	return t
}

// check tries to prove a goal on the current path, under an optional guard
// for conditionally evaluated expressions, and reports a diagnostic when the
// proof fails. The goal is assumed afterwards either way so that one failure
// is reported once instead of cascading.
func (v *fnVerifier) check(st *state, guard []*logic.Term, goal *logic.Term, pos token.Pos, format string, args ...any) {
	opts := solver.Options{Preds: v.res.Preds, MaxSteps: v.maxSteps}
	for _, conjunct := range logic.Conjuncts(goal) {
		if conjunct.Op == logic.OpTrue {
			continue
		}
		if solver.Prove(append(slices.Clip(st.hyps), guard...), conjunct, opts) != solver.Proved {
			v.report(pos, format, args...)
		}
		st.assume(logic.Implies(logic.And(guard...), conjunct))
	}
}

// checkClause checks every conjunct of an annotation separately so that the
// diagnostic can quote the part that failed.
func (v *fnVerifier) checkClause(c *clause, env logic.Env, st *state, guard []*logic.Term, pos token.Pos, what string) {
	for _, node := range c.node.Conjuncts() {
		text := strings.Join(strings.Fields(c.text[node.Start:node.End]), " ")
		v.check(st, guard, v.formula(c, node, env), pos, "%s: %s", what, text)
	}
}

// seq executes a statement list. Annotations between two statements are
// handled before the later one: assertions are checked in place and loop
// annotations are handed to the loop that follows them.
func (v *fnVerifier) seq(list []ast.Stmt, from, to token.Pos, st *state, c ctrl, k func(*state)) {
	spec := &loopSpec{}
	until := to
	if len(list) > 0 {
		until = list[0].Pos()
	}
	for _, clause := range v.fn.body {
		if clause.pos < from || clause.pos >= until {
			continue
		}
		switch clause.kind {
		case "Assert":
			v.checkClause(clause, &bodyEnv{v, st, clause.pos}, st, nil, clause.pos, "assertion may not hold")
		case "Invariant":
			spec.invariants = append(spec.invariants, clause)
		default:
			if spec.variant != nil {
				v.report(clause.pos, "loop already has a Variant; give it exactly one")
				continue
			}
			spec.variant = clause
		}
	}
	var loop ast.Stmt
	if len(list) > 0 {
		switch list[0].(type) {
		case *ast.ForStmt, *ast.RangeStmt:
			loop = list[0]
		}
	}
	if loop == nil {
		for _, clause := range append(slices.Clip(spec.invariants), spec.variant) {
			if clause != nil {
				v.report(clause.pos, "%s annotation must be directly above a for loop", clause.kind)
			}
		}
	}
	if len(list) == 0 {
		k(st)
		return
	}
	rest := func(next *state) { v.seq(list[1:], list[0].End(), to, next, c, k) }
	switch s := list[0].(type) {
	case *ast.ForStmt:
		v.forStmt(s, spec, st, rest)
	case *ast.RangeStmt:
		v.rangeStmt(s, spec, st, rest)
	default:
		v.stmt(s, st, c, rest)
	}
}

// stmt executes one statement and passes every resulting state to k.
// Statements that leave the current block (return, break, continue, panic)
// do not call k.
func (v *fnVerifier) stmt(s ast.Stmt, st *state, c ctrl, k func(*state)) {
	switch s := s.(type) {
	case *ast.EmptyStmt:
	case *ast.BlockStmt:
		v.seq(s.List, s.Lbrace, s.Rbrace, st, c, k)
		return
	case *ast.ExprStmt:
		call, ok := ast.Unparen(s.X).(*ast.CallExpr)
		if !ok {
			v.unsupported(s.Pos(), "this expression statement is not supported")
		}
		if isBuiltin(v.info, call, "panic") {
			v.check(st, nil, logic.False(), s.Pos(), "panic may be reachable")
			return
		}
		v.allowEffects(call)
		v.call(call, st, nil)
	case *ast.AssignStmt:
		v.assign(s, st)
	case *ast.IncDecStmt:
		delta := logic.IntLit(1)
		if s.Tok == token.DEC {
			delta = logic.IntLit(-1)
		}
		target := v.lvalue(s.X, st)
		value := v.read(target, st)
		if value.Sort == logic.Float {
			value = v.opaque(s.Tok, value)
		} else {
			value = logic.Add(value, delta)
			v.checkFits(st, nil, value, v.info.TypeOf(s.X), s.Pos(), operation(s.Tok))
		}
		v.set(target, value, st)
	case *ast.DeclStmt:
		v.declare(s, st)
	case *ast.IfStmt:
		v.ifStmt(s, st, c, k)
		return
	case *ast.SwitchStmt:
		v.switchStmt(s, st, c, k)
		return
	case *ast.ReturnStmt:
		v.returnStmt(s, st)
		return
	case *ast.BranchStmt:
		switch {
		case s.Label == nil && s.Tok == token.BREAK && c.brk != nil:
			c.brk(st)
		case s.Label == nil && s.Tok == token.CONTINUE && c.cont != nil:
			c.cont(st)
		default:
			v.unsupported(s.Pos(), "goto, fallthrough, and labeled branches are not supported")
		}
		return
	default:
		kind := strings.TrimSuffix(strings.TrimPrefix(fmt.Sprintf("%T", s), "*ast."), "Stmt")
		v.unsupported(s.Pos(), strings.ToLower(kind)+" statements are not supported yet")
	}
	k(st)
}

// branch counts one more fork in the path exploration.
func (v *fnVerifier) branch(pos token.Pos) {
	v.branches++
	if v.branches > maxBranches {
		v.unsupported(pos, "the function has too many paths to explore")
	}
}

// switchStmt executes a switch as the chain of tests Go performs: cases are
// tried top to bottom, a case expression is only evaluated when all earlier
// ones failed, and the default clause runs when none matches.
func (v *fnVerifier) switchStmt(s *ast.SwitchStmt, st *state, c ctrl, k func(*state)) {
	if s.Init != nil {
		v.stmt(s.Init, st, c, func(*state) {})
	}
	var tag *logic.Term
	if s.Tag != nil {
		tag = v.expr(s.Tag, st, nil)
	}
	inner := ctrl{brk: k, cont: c.cont}
	var failed []*logic.Term
	var fallback *ast.CaseClause
	for _, clause := range s.Body.List {
		clause := clause.(*ast.CaseClause)
		if clause.List == nil {
			fallback = clause
			continue
		}
		var alternatives []*logic.Term
		for _, e := range clause.List {
			guard := append(slices.Clip(failed), logic.Not(logic.Or(alternatives...)))
			var value *logic.Term
			switch {
			case tag == nil:
				value = v.expr(e, st, guard)
			case v.isNil(e) && tag.Sort == logic.Err:
				value = logic.IsNil(tag)
			default:
				// A case matches when Go's == holds, which for floats,
				// strings, and errors is not plain equality of terms.
				value = v.binary(token.EQL, tag, v.expr(e, st, guard), v.info.TypeOf(s.Tag), e.Pos(), st, guard)
			}
			alternatives = append(alternatives, value)
		}
		matched := logic.Or(alternatives...)
		v.branch(clause.Pos())
		taken := st.clone()
		taken.assume(logic.And(append(slices.Clip(failed), matched)...))
		v.seq(clause.Body, clause.Colon, clause.End(), taken, inner, k)
		failed = append(failed, logic.Not(matched))
	}
	st.assume(logic.And(failed...))
	if fallback == nil {
		k(st)
		return
	}
	v.seq(fallback.Body, fallback.Colon, fallback.End(), st, inner, k)
}

func (v *fnVerifier) ifStmt(s *ast.IfStmt, st *state, c ctrl, k func(*state)) {
	v.branch(s.Pos())
	if s.Init != nil {
		v.stmt(s.Init, st, c, func(*state) {})
	}
	cond := v.expr(s.Cond, st, nil)
	taken, skipped := st.clone(), st.clone()
	taken.assume(cond)
	skipped.assume(logic.Not(cond))
	v.seq(s.Body.List, s.Body.Lbrace, s.Body.Rbrace, taken, c, k)
	if s.Else == nil {
		k(skipped)
		return
	}
	v.stmt(s.Else, skipped, c, k)
}

// lvalue is an assignment target: a whole variable, or one element of a slice
// variable when index is set. A nil variable stands for the blank identifier.
type lvalue struct {
	variable *types.Var
	index    *logic.Term
	pos      token.Pos
}

// lvalue resolves an assignment target and checks the bounds of an element
// target.
func (v *fnVerifier) lvalue(e ast.Expr, st *state) lvalue {
	e = ast.Unparen(e)
	target := lvalue{pos: e.Pos()}
	if indexed, ok := e.(*ast.IndexExpr); ok {
		target.index = v.expr(indexed.Index, st, nil)
		e = ast.Unparen(indexed.X)
	}
	id, ok := e.(*ast.Ident)
	if !ok {
		v.unsupported(e.Pos(), "only variables and slice elements can be assigned")
	}
	if id.Name == "_" {
		return target
	}
	target.variable, ok = v.info.ObjectOf(id).(*types.Var)
	if !ok || target.variable.Parent() == v.pass.Pkg.Scope() {
		v.unsupported(e.Pos(), fmt.Sprintf("%s is not a local variable", id.Name))
	}
	if target.index != nil {
		v.checkIndex(st, nil, v.value(id, st), target.index, target.pos)
	}
	return target
}

// read returns the current value of an assignment target without evaluating
// its index expression a second time.
func (v *fnVerifier) read(target lvalue, st *state) *logic.Term {
	current := st.vals[target.variable]
	if current == nil {
		v.unsupported(target.pos, "this operand cannot be read and updated in place")
	}
	if target.index == nil {
		return current
	}
	element := logic.Select(current, target.index)
	st.assume(v.typeFact(element, target.variable.Type().Underlying().(*types.Slice).Elem()))
	return element
}

// set performs an assignment in the symbolic state.
func (v *fnVerifier) set(target lvalue, value *logic.Term, st *state) {
	variable := target.variable
	switch {
	case variable == nil:
	case target.index != nil:
		st.vals[variable] = logic.Store(st.vals[variable], target.index, value)
	default:
		sort, ok := sortOf(variable.Type())
		if !ok || value == nil || sort != value.Sort {
			v.unsupported(target.pos, fmt.Sprintf("variable %s has unsupported type %s", variable.Name(), variable.Type()))
		}
		if _, isParam := v.entry[variable]; isParam && isSlice(variable.Type()) {
			v.unsupported(target.pos, fmt.Sprintf(
				"slice parameter %s is reassigned; callers could no longer be told what happened to their slice",
				variable.Name()))
		}
		st.vals[variable] = value
		if sort.IsSeq() {
			st.assume(v.typeFact(value, variable.Type()))
		}
	}
}

// assign executes an assignment. Index operands on the left and the
// right-hand sides are evaluated first, and only then are the targets updated,
// in order. The relative order of those evaluations only matters when one of
// them modifies a slice, which is ruled out below.
func (v *fnVerifier) assign(s *ast.AssignStmt, st *state) {
	targets := make([]lvalue, len(s.Lhs))
	replaced, indexed := map[*types.Var]bool{}, map[*types.Var]bool{}
	for i, lhs := range s.Lhs {
		targets[i] = v.lvalue(lhs, st)
		if targets[i].index != nil {
			indexed[targets[i].variable] = true
		} else if targets[i].variable != nil {
			replaced[targets[i].variable] = true
		}
	}
	for variable := range replaced {
		if indexed[variable] {
			v.unsupported(s.Pos(), fmt.Sprintf(
				"%s is replaced and indexed in one assignment; the element would be written to the old backing array",
				variable.Name()))
		}
	}
	// Go does not fix the order between reading the operands of a target
	// such as a[a[0]] and calling a function on the right, so a call that
	// modifies a slice is allowed only when every target is a plain variable.
	v.effectful = nil
	if len(s.Rhs) == 1 && len(indexed) == 0 && (s.Tok == token.ASSIGN || s.Tok == token.DEFINE) {
		v.allowEffects(s.Rhs[0])
	}
	var values []*logic.Term
	switch {
	case s.Tok != token.ASSIGN && s.Tok != token.DEFINE:
		op := map[token.Token]token.Token{
			token.ADD_ASSIGN: token.ADD, token.SUB_ASSIGN: token.SUB, token.MUL_ASSIGN: token.MUL,
			token.QUO_ASSIGN: token.QUO, token.REM_ASSIGN: token.REM,
		}[s.Tok]
		current, operand := v.read(targets[0], st), v.expr(s.Rhs[0], st, nil)
		values = []*logic.Term{v.binary(op, current, operand, v.info.TypeOf(s.Lhs[0]), s.TokPos, st, nil)}
	case len(s.Rhs) == 1 && len(s.Lhs) > 1:
		values = v.callResults(s.Rhs[0], st)
	default:
		for i, rhs := range s.Rhs {
			values = append(values, v.rhs(targets[i], rhs, st))
		}
	}
	for i, target := range targets {
		v.set(target, values[i], st)
	}
}

func (v *fnVerifier) callResults(e ast.Expr, st *state) []*logic.Term {
	call, ok := ast.Unparen(e).(*ast.CallExpr)
	if !ok {
		v.unsupported(e.Pos(), "multi-value expressions other than function calls are not supported")
	}
	return v.call(call, st, nil)
}

// rhs evaluates the right-hand side of an assignment to target. Slices are
// modelled as values, so an assignment that would make two variables share
// one backing array is rejected instead of being modelled wrongly.
func (v *fnVerifier) rhs(target lvalue, e ast.Expr, st *state) *logic.Term {
	want := v.info.TypeOf(e)
	if target.variable != nil && target.index == nil {
		want = target.variable.Type()
	}
	sort, ok := sortOf(want)
	if !ok || !isSlice(want) {
		return v.exprAs(e, want, st, nil)
	}
	if id, ok := ast.Unparen(e).(*ast.Ident); ok && id.Name != "nil" {
		v.unsupported(e.Pos(), fmt.Sprintf(
			"assigning slice %s to another variable would make two variables share one backing array", id.Name))
	}
	return v.slice(target.variable, sort, e, st)
}

// slice evaluates a sequence-valued expression: a string expression, or a
// slice expression that produces fresh storage, which is nil, make, a
// composite literal, a call, or x = append(x, ...) on a local x.
func (v *fnVerifier) slice(target *types.Var, sort logic.Sort, e ast.Expr, st *state) *logic.Term {
	empty := zero(sort)
	if text := v.text(e, st); text != nil {
		return text
	}
	switch e := ast.Unparen(e).(type) {
	case *ast.Ident:
		if e.Name == "nil" {
			return empty
		}
		return v.value(e, st)
	case *ast.CompositeLit:
		result := empty
		for _, element := range e.Elts {
			if _, keyed := element.(*ast.KeyValueExpr); keyed {
				v.unsupported(element.Pos(), "keyed slice literals are not supported")
			}
			result = logic.Push(result, v.expr(element, st, nil))
		}
		return result
	case *ast.CallExpr:
		switch {
		case isBuiltin(v.info, e, "make"):
			if len(e.Args) < 2 {
				v.unsupported(e.Pos(), "make needs a length")
			}
			length := v.expr(e.Args[1], st, nil)
			v.check(st, nil, logic.Le(logic.IntLit(0), length), e.Args[1].Pos(), "make length may be negative")
			v.checkFits(st, nil, length, types.Typ[types.Int], e.Args[1].Pos(), "make length")
			if len(e.Args) == 3 {
				capacity := v.expr(e.Args[2], st, nil)
				v.check(st, nil, logic.Le(length, capacity), e.Args[2].Pos(), "make capacity may be less than the length")
				v.checkFits(st, nil, capacity, types.Typ[types.Int], e.Args[2].Pos(), "make capacity")
			}
			return logic.Fill(length, zero(sort.Elem()))
		case isBuiltin(v.info, e, "append"):
			base, ok := ast.Unparen(e.Args[0]).(*ast.Ident)
			_, isParam := v.entry[target]
			if !ok || target == nil || v.info.ObjectOf(base) != target || isParam || e.Ellipsis.IsValid() {
				v.unsupported(e.Pos(), "append is only supported in the form x = append(x, values...) on a local slice x")
			}
			result := v.value(base, st)
			for _, element := range e.Args[1:] {
				result = logic.Push(result, v.expr(element, st, nil))
			}
			// The grown length must be proved to fit. Assuming it, as for
			// other slices, would contradict a length already at the limit
			// and make everything after the append provable.
			v.checkFits(st, nil, logic.Len(result), types.Typ[types.Int], e.Pos(), "append length")
			return result
		}
		results := v.call(e, st, nil)
		if len(results) == 1 && results[0] != nil {
			return results[0]
		}
	}
	v.unsupported(e.Pos(), "this slice expression is not supported (sub-slicing and aliasing are not modelled yet)")
	return nil
}

// declare executes a local var declaration: variables without an initial
// value get the zero value of their type, the others are assigned like an
// ordinary assignment. Local constants need no state.
func (v *fnVerifier) declare(s *ast.DeclStmt, st *state) {
	decl := s.Decl.(*ast.GenDecl)
	if decl.Tok == token.CONST {
		return
	}
	if decl.Tok != token.VAR {
		v.unsupported(s.Pos(), "local type declarations are not supported")
	}
	for _, spec := range decl.Specs {
		spec := spec.(*ast.ValueSpec)
		targets := make([]lvalue, len(spec.Names))
		for i, name := range spec.Names {
			targets[i] = v.lvalue(name, st)
		}
		var values []*logic.Term
		switch {
		case len(spec.Values) == 0:
			for _, name := range spec.Names {
				sort, ok := sortOf(v.info.TypeOf(name))
				if !ok {
					v.unsupported(name.Pos(), fmt.Sprintf("variable %s has unsupported type %s", name.Name, v.info.TypeOf(name)))
				}
				values = append(values, zero(sort))
			}
		case len(spec.Values) == 1 && len(spec.Names) > 1:
			v.allowEffects(spec.Values[0])
			values = v.callResults(spec.Values[0], st)
		default:
			if len(spec.Values) == 1 {
				v.allowEffects(spec.Values[0])
			}
			for i, value := range spec.Values {
				values = append(values, v.rhs(targets[i], value, st))
			}
		}
		for i, target := range targets {
			v.set(target, values[i], st)
		}
	}
}

// modified computes the variables a loop may assign as a whole and the slices
// whose elements it may write, either directly or through a call.
func (v *fnVerifier) modified(nodes ...ast.Node) (whole, elements map[*types.Var]bool) {
	whole, elements = map[*types.Var]bool{}, map[*types.Var]bool{}
	mark := func(e ast.Expr, set map[*types.Var]bool) {
		if e == nil {
			return
		}
		if indexed, ok := ast.Unparen(e).(*ast.IndexExpr); ok {
			e, set = indexed.X, elements
		}
		if id, ok := ast.Unparen(e).(*ast.Ident); ok {
			if variable, ok := v.info.ObjectOf(id).(*types.Var); ok {
				set[variable] = true
			}
		}
	}
	for _, node := range nodes {
		if node == nil {
			continue
		}
		ast.Inspect(node, func(n ast.Node) bool {
			switch n := n.(type) {
			case *ast.AssignStmt:
				for _, lhs := range n.Lhs {
					mark(lhs, whole)
				}
			case *ast.IncDecStmt:
				mark(n.X, whole)
			case *ast.RangeStmt:
				mark(n.Key, whole)
				mark(n.Value, whole)
			case *ast.CallExpr:
				if _, builtin := v.info.Uses[calleeIdent(n)].(*types.Builtin); builtin {
					break
				}
				callee := v.funcs[typeutil.StaticCallee(v.info, n)]
				for i, arg := range n.Args {
					if callee != nil && i < len(callee.params) && !v.mutates(callee, callee.params[i]) {
						continue
					}
					if isSlice(v.info.TypeOf(arg)) {
						mark(arg, elements)
					}
				}
			}
			return true
		})
	}
	return whole, elements
}

func calleeIdent(call *ast.CallExpr) *ast.Ident {
	id, _ := ast.Unparen(call.Fun).(*ast.Ident)
	return id
}

// havoc forgets everything about the variables a loop modifies by giving them
// fresh values, which stand for their values at an arbitrary iteration. A
// slice whose elements are written but which is never reassigned keeps its
// length.
func (v *fnVerifier) havoc(st *state, whole, elements map[*types.Var]bool) {
	var variables []*types.Var
	for variable := range st.vals {
		if whole[variable] || elements[variable] {
			variables = append(variables, variable)
		}
	}
	slices.SortFunc(variables, func(a, b *types.Var) int { return int(a.Pos() - b.Pos()) })
	for _, variable := range variables {
		previous := st.vals[variable]
		st.vals[variable] = v.fresh(variable.Name(), previous.Sort)
		st.assume(v.typeFact(st.vals[variable], variable.Type()))
		if previous.Sort.IsSeq() && !whole[variable] {
			st.assume(logic.Eq(logic.Len(st.vals[variable]), logic.Len(previous)))
		}
	}
}

// loopShape describes a for or range loop to the shared loop rule.
type loopShape struct {
	pos   token.Pos
	body  *ast.BlockStmt
	post  ast.Stmt
	spec  *loopSpec
	whole map[*types.Var]bool
	elems map[*types.Var]bool
	// step yields the counter of the next iteration when it is not simply
	// one more, as when ranging over the characters of a string.
	step   func(st *state, counter *logic.Term) *logic.Term
	cond   func(st *state) *logic.Term // for loops: evaluates the condition
	always bool                        // the loop has no condition and is only left by break
	// Range loops run a fixed number of iterations; bind stores the iteration
	// counter and the current element in the loop variables.
	limit *logic.Term
	bind  func(st *state, counter *logic.Term)
}

// loop verifies a loop by induction. The invariants are checked on entry.
// Then an arbitrary iteration is examined: the modified variables are
// havocked, the invariants are assumed, and the body must re-establish the
// invariants and decrease the variant. Code after the loop continues from the
// havocked state in which the condition is false, or from a break.
func (v *fnVerifier) loop(shape loopShape, st *state, k func(*state)) {
	at := shape.body.Lbrace + 1
	spec := shape.spec
	env := func(st *state) logic.Env { return &bodyEnv{v, st, at} }
	checkInvariants := func(st *state, what string) {
		for _, c := range spec.invariants {
			v.checkClause(c, env(st), st, nil, shape.pos, what)
		}
	}
	var counter *logic.Term
	entry := st.clone()
	if shape.limit != nil {
		shape.bind(entry, logic.IntLit(0))
	}
	checkInvariants(entry, "loop invariant may not hold on entry")

	head := st.clone()
	v.havoc(head, shape.whole, shape.elems)
	if shape.limit != nil {
		counter = v.fresh("iteration", logic.Int)
		head.assume(logic.Le(logic.IntLit(0), counter))
		head.assume(logic.Le(counter, shape.limit))
		shape.bind(head, counter)
	}
	for _, c := range spec.invariants {
		head.assume(v.formula(c, c.node, env(head)))
	}
	var cond *logic.Term
	if shape.limit != nil {
		cond = logic.Lt(counter, shape.limit)
	} else {
		cond = shape.cond(head)
	}
	if !shape.always {
		exit := head.clone()
		exit.assume(logic.Not(cond))
		k(exit)
	}
	head.assume(cond)
	var before *logic.Term
	if spec.variant != nil {
		before = v.intTerm(spec.variant, env(head))
		v.check(head, nil, logic.Le(logic.IntLit(0), before), shape.pos,
			"loop variant may be negative: %s", spec.variant.text)
	}
	after := func(end *state) {
		if shape.post != nil {
			v.stmt(shape.post, end, ctrl{}, func(*state) {})
		}
		if shape.limit != nil {
			next := logic.Add(counter, logic.IntLit(1))
			if shape.step != nil {
				next = shape.step(end, counter)
			}
			shape.bind(end, next)
		}
		checkInvariants(end, "loop invariant may not be preserved")
		if before != nil {
			v.check(end, nil, logic.Lt(v.intTerm(spec.variant, env(end)), before), shape.pos,
				"loop variant may not decrease: %s", spec.variant.text)
		}
	}
	v.seq(shape.body.List, shape.body.Lbrace, shape.body.Rbrace, head, ctrl{brk: k, cont: after}, after)
}

func (v *fnVerifier) forStmt(s *ast.ForStmt, spec *loopSpec, st *state, k func(*state)) {
	if s.Init != nil {
		v.stmt(s.Init, st, ctrl{}, func(*state) {})
	}
	if spec.variant == nil {
		v.report(s.Pos(), "loop needs a //@ Variant annotation to prove that it terminates")
	}
	shape := loopShape{pos: s.Pos(), body: s.Body, post: s.Post, spec: spec, always: s.Cond == nil}
	shape.whole, shape.elems = v.modified(s.Body, s.Post)
	shape.cond = func(st *state) *logic.Term {
		if s.Cond == nil {
			return logic.True()
		}
		return v.expr(s.Cond, st, nil)
	}
	v.loop(shape, st, k)
}

// rangeStmt verifies "for i := range n" and "for i, x := range A" as counted
// loops. The iteration count is fixed on entry, so termination needs no
// variant, and the facts 0 <= i <= limit are part of the invariant for free.
func (v *fnVerifier) rangeStmt(s *ast.RangeStmt, spec *loopSpec, st *state, k func(*state)) {
	shape := loopShape{pos: s.Pos(), body: s.Body, spec: spec}
	shape.whole, shape.elems = v.modified(s.Body)
	var sequence *types.Var
	sort, ok := sortOf(v.info.TypeOf(s.X))
	switch {
	case ok && sort == logic.Int:
		count := v.expr(s.X, st, nil)
		shape.limit = logic.Ite(logic.Le(logic.IntLit(0), count), count, logic.IntLit(0))
	case ok && sort.IsSeq():
		id, isIdent := ast.Unparen(s.X).(*ast.Ident)
		if !isIdent {
			v.unsupported(s.X.Pos(), "range is only supported over a slice variable or an integer")
		}
		sequence = v.info.ObjectOf(id).(*types.Var)
		shape.limit = logic.Len(v.value(id, st))
	default:
		v.unsupported(s.X.Pos(), fmt.Sprintf("range over %s is not supported", v.info.TypeOf(s.X)))
	}
	if s.Tok == token.ASSIGN || shape.whole[sequence] {
		v.unsupported(s.Pos(), "range loops must declare their variables with := and must not reassign the ranged slice")
	}
	variable := func(e ast.Expr) *types.Var {
		if id, ok := e.(*ast.Ident); ok && id.Name != "_" {
			return v.info.Defs[id].(*types.Var)
		}
		return nil
	}
	key, value := variable(s.Key), variable(s.Value)
	shape.bind = func(st *state, counter *logic.Term) {
		if key != nil {
			st.vals[key] = counter
		}
		if value != nil {
			st.vals[value] = logic.Select(st.vals[sequence], counter)
			st.assume(v.typeFact(st.vals[value], value.Type()))
		}
	}
	if isString(v.info.TypeOf(s.X)) {
		// Ranging over a string decodes UTF-8: each iteration yields some
		// character and moves on by the one to four bytes it occupies,
		// never past the end. Which character, and how many bytes, is not
		// modelled.
		shape.step = func(st *state, counter *logic.Term) *logic.Term {
			next := v.fresh("offset", logic.Int)
			st.assume(logic.And(logic.Lt(counter, next), logic.Le(next, logic.Add(counter, logic.IntLit(4))), logic.Le(next, shape.limit)))
			return next
		}
		shape.bind = func(st *state, counter *logic.Term) {
			if key != nil {
				st.vals[key] = counter
			}
			if value != nil {
				st.vals[value] = v.fresh("char", logic.Int)
				st.assume(v.typeFact(st.vals[value], value.Type()))
			}
		}
	}
	v.loop(shape, st, k)
}

// returnStmt evaluates the returned values and checks the postcondition. A
// slice may be returned only when the caller gets the sole reference to its
// backing array, so parameters and repeated variables are rejected.
func (v *fnVerifier) returnStmt(s *ast.ReturnStmt, st *state) {
	results := make([]*logic.Term, len(v.fn.results))
	if len(s.Results) == 1 {
		v.allowEffects(s.Results[0])
	}
	returned := map[*types.Var]bool{}
	switch {
	case len(s.Results) == 0:
		for i, result := range v.fn.results {
			results[i] = st.vals[result]
		}
	case len(s.Results) == 1 && len(results) > 1:
		results = v.callResults(s.Results[0], st)
	default:
		for i, e := range s.Results {
			results[i] = v.exprAs(e, v.fn.results[i].Type(), st, nil)
			id, ok := ast.Unparen(e).(*ast.Ident)
			variable, _ := v.info.ObjectOf(id).(*types.Var)
			if !ok || variable == nil || !isSlice(v.fn.results[i].Type()) {
				continue
			}
			if v.entry[variable] != nil {
				v.unsupported(e.Pos(), fmt.Sprintf(
					"returning slice parameter %s would give the caller two names for one backing array", id.Name))
			}
			if returned[variable] {
				v.unsupported(e.Pos(), fmt.Sprintf(
					"slice %s is returned twice, which would give the caller two names for one backing array", id.Name))
			}
			returned[variable] = true
		}
	}
	v.atReturn(st, results, s.Pos())
}

// atReturn checks the postcondition in a final state.
func (v *fnVerifier) atReturn(st *state, results []*logic.Term, pos token.Pos) {
	post := map[*types.Var]*logic.Term{}
	for _, param := range v.fn.params {
		post[param] = st.vals[param]
	}
	env := &contractEnv{pv: v.pkgVerifier, fn: v.fn, args: v.entry, post: post, results: results}
	for _, c := range v.fn.ensures {
		v.checkClause(c, env, st, nil, pos, "postcondition may not hold")
	}
}

// value returns the current value of a variable.
func (v *fnVerifier) value(id *ast.Ident, st *state) *logic.Term {
	variable, _ := v.info.ObjectOf(id).(*types.Var)
	if value := st.vals[variable]; value != nil {
		return value
	}
	if v.sentinels[variable] {
		sentinel := logic.Const("var "+variable.Name(), logic.Err)
		st.assume(logic.Not(logic.IsNil(sentinel)))
		return sentinel
	}
	v.unsupported(id.Pos(), id.Name+" is not a local variable of a supported type")
	return nil
}

func (v *fnVerifier) checkIndex(st *state, guard []*logic.Term, seq, index *logic.Term, pos token.Pos) {
	v.check(st, guard, logic.Le(logic.IntLit(0), index), pos, "index may be negative")
	v.check(st, guard, logic.Lt(index, logic.Len(seq)), pos, "index may be out of range")
}

// expr evaluates an expression to a term, checking on the way that it cannot
// panic. guard holds the conditions under which the expression is evaluated
// at all, which matters on the right of && and ||.
func (v *fnVerifier) expr(e ast.Expr, st *state, guard []*logic.Term) *logic.Term {
	sort, ok := sortOf(v.info.TypeOf(e))
	if !ok {
		v.unsupported(e.Pos(), fmt.Sprintf("expressions of type %s are not supported", v.info.TypeOf(e)))
	}
	if tv := v.info.Types[e]; tv.Value != nil {
		return v.constant(tv.Value, sort, e, st)
	}
	if sort.IsSeq() {
		return v.slice(nil, sort, e, st)
	}
	switch e := e.(type) {
	case *ast.ParenExpr:
		return v.expr(e.X, st, guard)
	case *ast.Ident:
		return v.value(e, st)
	case *ast.UnaryExpr:
		operand := v.expr(e.X, st, guard)
		switch e.Op {
		case token.SUB:
			if operand.Sort == logic.Float {
				return v.opaque(e.Op, operand)
			}
			v.checkFits(st, guard, logic.Neg(operand), v.info.TypeOf(e), e.Pos(), "negation")
			return logic.Neg(operand)
		case token.ADD:
			return operand
		case token.NOT:
			return logic.Not(operand)
		}
	case *ast.BinaryExpr:
		// Whether an error is nil is the one thing known about it.
		if nilX, nilY := v.isNil(e.X), v.isNil(e.Y); (nilX || nilY) && (e.Op == token.EQL || e.Op == token.NEQ) {
			other := e.X
			if nilX {
				other = e.Y
			}
			value := v.expr(other, st, guard)
			if value.Sort != logic.Err {
				v.unsupported(e.Pos(), "only errors can be compared with nil")
			}
			if e.Op == token.NEQ {
				return logic.Not(logic.IsNil(value))
			}
			return logic.IsNil(value)
		}
		left := v.expr(e.X, st, guard)
		switch e.Op {
		case token.LAND:
			return logic.And(left, v.expr(e.Y, st, append(slices.Clip(guard), left)))
		case token.LOR:
			return logic.Or(left, v.expr(e.Y, st, append(slices.Clip(guard), logic.Not(left))))
		}
		return v.binary(e.Op, left, v.expr(e.Y, st, guard), v.info.TypeOf(e), e.OpPos, st, guard)
	case *ast.IndexExpr:
		id, ok := ast.Unparen(e.X).(*ast.Ident)
		if !ok {
			v.unsupported(e.X.Pos(), "only slice variables can be indexed")
		}
		seq, index := v.value(id, st), v.expr(e.Index, st, guard)
		v.checkIndex(st, guard, seq, index, e.Pos())
		element := logic.Select(seq, index)
		st.assume(logic.Implies(logic.And(guard...), v.typeFact(element, v.info.TypeOf(e))))
		return element
	case *ast.CallExpr:
		return v.callExpr(e, st, guard)
	}
	v.unsupported(e.Pos(), "this expression is not supported")
	return nil
}

func (v *fnVerifier) callExpr(e *ast.CallExpr, st *state, guard []*logic.Term) *logic.Term {
	switch {
	case isBuiltin(v.info, e, "len"):
		return logic.Len(v.expr(e.Args[0], st, guard))
	case isBuiltin(v.info, e, "min"), isBuiltin(v.info, e, "max"):
		result := v.expr(e.Args[0], st, guard)
		for _, arg := range e.Args[1:] {
			other := v.expr(arg, st, guard)
			smaller := logic.Le(result, other)
			if calleeIdent(e).Name == "max" {
				smaller = logic.Le(other, result)
			}
			result = logic.Ite(smaller, result, other)
		}
		return result
	case v.info.Types[e.Fun].IsType():
		value, target := v.expr(e.Args[0], st, guard), v.info.TypeOf(e)
		sort, _ := sortOf(target)
		if value.Sort == logic.Float || sort == logic.Float {
			// Nothing is known about a float, so nothing is known about
			// what it converts to or from, beyond the type of the result.
			converted := v.fresh("converted", sort)
			st.assume(v.typeFact(converted, target))
			return converted
		}
		v.check(st, guard, v.typeFact(value, target), e.Pos(),
			"conversion may not fit %s", types.TypeString(target, nil))
		return value
	}
	results := v.call(e, st, guard)
	if len(results) != 1 || results[0] == nil {
		v.unsupported(e.Pos(), "this call does not produce a single supported value")
	}
	return results[0]
}

// binary builds the term for a binary operator applied to two evaluated
// operands. Division and remainder first have to show a non-zero divisor.
func (v *fnVerifier) binary(op token.Token, x, y *logic.Term, t types.Type, pos token.Pos, st *state, guard []*logic.Term) *logic.Term {
	switch {
	case x.Sort == logic.Float || x.Sort == logic.Err:
		return v.opaque(op, x)
	case x.Sort.IsSeq() && op == token.ADD:
		joined := logic.Concat(x, y)
		v.checkFits(st, guard, logic.Len(joined), types.Typ[types.Int], pos, "string length")
		return joined
	case x.Sort.IsSeq() && (op == token.EQL || op == token.NEQ):
		same := logic.SeqEq(x, y, logic.Bound(v.fresh("k#", logic.Int).Name, logic.Int))
		if op == token.NEQ {
			return logic.Not(same)
		}
		return same
	case x.Sort.IsSeq():
		return v.opaque(op, x)
	}
	switch op {
	case token.ADD, token.SUB, token.MUL:
		result := logic.Add(x, y)
		switch op {
		case token.SUB:
			result = logic.Sub(x, y)
		case token.MUL:
			result = logic.Mul(x, y)
		}
		v.checkFits(st, guard, result, t, pos, operation(op))
		return result
	case token.QUO, token.REM:
		v.check(st, guard, logic.Ne(y, logic.IntLit(0)), pos, "possible division by zero")
		if op == token.REM {
			return logic.Mod(x, y)
		}
		// The only quotient that does not fit is the least value over -1.
		if least, _, ok := v.intRange(t); ok && least.Sign() < 0 {
			wraps := logic.And(logic.Eq(x, logic.BigLit(least)), logic.Eq(y, logic.IntLit(-1)))
			v.check(st, guard, logic.Not(wraps), pos, "division may overflow %s", types.TypeString(t, nil))
		}
		return logic.Div(x, y)
	case token.EQL:
		return logic.Eq(x, y)
	case token.NEQ:
		return logic.Ne(x, y)
	case token.LSS:
		return logic.Lt(x, y)
	case token.LEQ:
		return logic.Le(x, y)
	case token.GTR:
		return logic.Lt(y, x)
	case token.GEQ:
		return logic.Le(y, x)
	}
	v.unsupported(pos, fmt.Sprintf("operator %s is not supported", op))
	return nil
}

// call verifies a call modularly: the callee's precondition must hold, its
// measure must decrease when the call is recursive, the slices it may write
// are havocked, and its postcondition is assumed. The callee's body is never
// inspected, so an unannotated callee tells the caller nothing.
func (v *fnVerifier) call(call *ast.CallExpr, st *state, guard []*logic.Term) []*logic.Term {
	callee, _ := typeutil.Callee(v.info, call).(*types.Func)
	if callee == nil {
		v.unsupported(call.Pos(), "only calls to named functions are supported")
	}
	if errorConstructor(callee) {
		return []*logic.Term{v.newError(call, st, guard)}
	}
	sig := callee.Type().(*types.Signature)
	if sig.Recv() != nil || sig.Variadic() || sig.TypeParams() != nil {
		v.unsupported(call.Pos(), "calls to methods, variadic functions, and generic functions are not supported yet")
	}
	fn := v.funcs[callee]
	if fn != nil && fn.broken {
		v.unsupported(call.Pos(), callee.Name()+" has an annotation that could not be understood, so its contract is unknown")
	}
	args := map[*types.Var]*logic.Term{}
	post := map[*types.Var]*logic.Term{}
	passed := map[*types.Var]int{}
	var written []func()
	for i, arg := range call.Args {
		param := sig.Params().At(i)
		value := v.exprAs(arg, param.Type(), st, guard)
		args[param], post[param] = value, value
		if !isSlice(param.Type()) {
			continue
		}
		// A slice argument is either a variable, whose contents the call may
		// change, or an expression that builds a temporary slice.
		var variable *types.Var
		if id, ok := ast.Unparen(arg).(*ast.Ident); ok {
			variable, _ = v.info.ObjectOf(id).(*types.Var)
			passed[variable]++
		}
		if !v.mutates(fn, param) {
			continue
		}
		passed[variable] += len(call.Args)
		if call != v.effectful || len(guard) > 0 {
			v.unsupported(call.Pos(), fmt.Sprintf(
				"%s may modify the slice passed as %s, so the call must be a statement of its own "+
					"or the whole right-hand side of an assignment to variables", callee.Name(), param.Name()))
		}
		written = append(written, func() {
			post[param] = v.fresh(param.Name(), value.Sort)
			st.assume(logic.Eq(logic.Len(post[param]), logic.Len(value)))
			if variable != nil {
				st.vals[variable] = post[param]
			}
		})
	}
	for variable, uses := range passed {
		if variable != nil && uses > len(call.Args)+1 {
			v.unsupported(call.Pos(), fmt.Sprintf(
				"slice %s is passed more than once to a function that may modify it", variable.Name()))
		}
	}
	if fn != nil {
		pre := &contractEnv{pv: v.pkgVerifier, fn: fn, args: args}
		for _, c := range fn.requires {
			v.checkClause(c, pre, st, guard, call.Pos(), "precondition of "+callee.Name()+" may not hold")
		}
		v.checkRecursion(fn, pre, st, guard, call)
	}
	for _, write := range written {
		write()
	}
	results := make([]*logic.Term, sig.Results().Len())
	for i := range results {
		sort, ok := sortOf(sig.Results().At(i).Type())
		if !ok {
			continue
		}
		if isSlice(sig.Results().At(i).Type()) && (fn == nil || !fn.annotated()) {
			v.unsupported(call.Pos(), fmt.Sprintf(
				"%s returns a slice but is not verified, so the slice might share storage with another one",
				callee.Name()))
		}
		results[i] = v.fresh(callee.Name(), sort)
		st.assume(v.typeFact(results[i], sig.Results().At(i).Type()))
	}
	if fn != nil {
		env := &contractEnv{pv: v.pkgVerifier, fn: fn, args: args, post: post, results: results}
		for _, c := range fn.ensures {
			st.assume(logic.Implies(logic.And(guard...), v.calleeFormula(c, env)))
		}
	}
	return results
}

// calleeFormula resolves a callee's postcondition at a call site. A result of
// an unsupported type has no term, so a clause that mentions it is skipped.
func (v *fnVerifier) calleeFormula(c *clause, env *contractEnv) *logic.Term {
	t, err := v.res.Formula(c.node, &partialEnv{env})
	switch {
	case errors.Is(err, errNoValue):
		return logic.True()
	case err != nil:
		v.report(c.pos, "in %s annotation: %v", c.kind, err)
		panic(abort{})
	}
	return t
}

var errNoValue = errors.New("value of unsupported type")

// partialEnv wraps a contract environment in which some results are missing.
type partialEnv struct{ *contractEnv }

func (e *partialEnv) Var(name string, primed bool) (*logic.Term, error) {
	t, err := e.contractEnv.Var(name, primed)
	if err == nil && t == nil {
		return nil, errNoValue
	}
	return t, err
}

// checkRecursion requires a decreasing measure for every call that can lead
// back to the function under verification.
func (v *fnVerifier) checkRecursion(callee *funcInfo, pre *contractEnv, st *state, guard []*logic.Term, call *ast.CallExpr) {
	if !v.reaches(callee, v.fn) {
		return
	}
	for _, fn := range []*funcInfo{v.fn, callee} {
		if fn.measure == nil {
			v.report(call.Pos(), "recursive call needs a //@ Measure annotation on %s to prove termination", fn.obj.Name())
			return
		}
	}
	measure := v.intTerm(callee.measure, pre)
	v.check(st, guard, logic.Lt(measure, v.measure), call.Pos(),
		"measure may not decrease in recursive call: %s", callee.measure.text)
}
