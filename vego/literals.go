package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"maps"
	"path/filepath"
	"slices"
	"strings"

	"github.com/spachava753/laas/vego/internal/logic"
)

// A function literal is verified where it is used, and only where every use
// can be seen: called where it is written, deferred where it is written, or
// bound by its declaration to a local variable whose every use is a call.
// Such a literal never leaves the function, so a call of it means what its
// body does at that point, in the state there. The body is executed at each
// call as part of the function around it, with no contract: the variables
// it captures are those of the function, shared and read at the time it
// runs, and everything the function is held to applies to the body too.
//
// A body may end in more than one state, and a call inside an expression
// must leave one. The end states are joined: a new constant says which way
// through the body was taken, the facts each way added hold on condition
// of it, and whatever differs between the ends is a choice on it.

// literalUses classifies the function literals of a body. It returns the
// variables bound to a literal that is used in place, and for each literal
// or use that is not in place the reason, by position. A literal is in
// place when it is the function of a call, or the value a declaration
// gives a new local variable whose every use is the function of a call.
func literalUses(info *types.Info, body ast.Node) (bound map[*types.Var]*ast.FuncLit, refused map[token.Pos]string) {
	bound, refused = map[*types.Var]*ast.FuncLit{}, map[token.Pos]string{}
	called := map[*ast.Ident]bool{}
	var stack []ast.Node
	// parent returns the node around the one on top of the stack, looking
	// through parentheses.
	parent := func() ast.Node {
		for i := len(stack) - 2; i >= 0; i-- {
			if _, paren := stack[i].(*ast.ParenExpr); !paren {
				return stack[i]
			}
		}
		return nil
	}
	ast.Inspect(body, func(n ast.Node) bool {
		if n == nil {
			stack = stack[:len(stack)-1]
			return true
		}
		stack = append(stack, n)
		if call, ok := n.(*ast.CallExpr); ok {
			if id, isIdent := ast.Unparen(call.Fun).(*ast.Ident); isIdent {
				called[id] = true
			}
		}
		lit, ok := n.(*ast.FuncLit)
		if !ok {
			return true
		}
		switch p := parent().(type) {
		case *ast.CallExpr:
			if ast.Unparen(p.Fun) == lit {
				return true
			}
		case *ast.AssignStmt:
			if p.Tok != token.DEFINE || len(p.Lhs) != len(p.Rhs) {
				break
			}
			for i, rhs := range p.Rhs {
				id, isIdent := p.Lhs[i].(*ast.Ident)
				if variable, isVar := info.Defs[id].(*types.Var); ast.Unparen(rhs) == lit && isIdent && isVar {
					bound[variable] = lit
					return true
				}
			}
		case *ast.ValueSpec:
			if len(p.Names) != len(p.Values) {
				break
			}
			for i, value := range p.Values {
				if variable, isVar := info.Defs[p.Names[i]].(*types.Var); ast.Unparen(value) == lit && isVar {
					bound[variable] = lit
					return true
				}
			}
		}
		refused[lit.Pos()] = "a function literal is supported only where it is called or deferred, or as the value " +
			"that declares a new variable which is only ever called; this one is used as a value"
		return true
	})
	// Every use of a bound variable must call it; one that is used any other
	// way is not in place.
	if len(bound) == 0 {
		return bound, refused
	}
	var misused []*types.Var
	ast.Inspect(body, func(n ast.Node) bool {
		id, ok := n.(*ast.Ident)
		if !ok {
			return true
		}
		if variable, isVar := info.Uses[id].(*types.Var); isVar && bound[variable] != nil && !called[id] {
			refused[id.Pos()] = fmt.Sprintf("%s holds a function literal and is used here other than by calling it; "+
				"a variable that holds a function literal is supported only when it is never assigned again and only called", id.Name)
			misused = append(misused, variable)
		}
		return true
	})
	for _, variable := range misused {
		delete(bound, variable)
	}
	return bound, refused
}

// literalOf returns the literal a call calls in place, or nil.
func (v *fnVerifier) literalOf(call *ast.CallExpr) *ast.FuncLit {
	switch fun := ast.Unparen(call.Fun).(type) {
	case *ast.FuncLit:
		return fun
	case *ast.Ident:
		if variable, ok := v.info.Uses[fun].(*types.Var); ok {
			return v.boundLits[variable]
		}
	}
	return nil
}

// isBoundLiteral reports whether an expression names a variable bound to a
// literal used in place. Such a variable has no value: every use of it is a
// call, which runs the literal.
func (v *fnVerifier) isBoundLiteral(e ast.Expr) bool {
	id, ok := ast.Unparen(e).(*ast.Ident)
	if !ok {
		return false
	}
	variable, _ := v.info.ObjectOf(id).(*types.Var)
	return variable != nil && v.boundLits[variable] != nil
}

// classifyLiterals finds the literals of the function being verified and
// refuses those that are not used in place, those whose signature is not
// supported, and, for now, those that assign a variable of the function
// around them.
func (v *fnVerifier) classifyLiterals() {
	body := v.fn.decl.Body
	bound, refused := literalUses(v.info, body)
	if len(refused) > 0 {
		first := slices.Min(slices.Collect(maps.Keys(refused)))
		v.unsupported(first, refused[first])
	}
	v.boundLits = bound
	ast.Inspect(body, func(n ast.Node) bool {
		lit, ok := n.(*ast.FuncLit)
		if !ok {
			return true
		}
		sig := v.info.TypeOf(lit).(*types.Signature)
		if sig.Variadic() {
			v.unsupported(lit.Pos(), "variadic function literals are not supported yet")
		}
		for _, tuple := range []*types.Tuple{sig.Params(), sig.Results()} {
			for variable := range tuple.Variables() {
				if _, modelled := layoutOf(variable.Type()); !modelled {
					v.unsupported(lit.Pos(), fmt.Sprintf("this function literal takes or returns a %s, which is not supported", variable.Type()))
				}
			}
		}
		// Assigning a captured variable is not supported yet.
		ast.Inspect(lit.Body, func(inner ast.Node) bool {
			var targets []ast.Expr
			switch s := inner.(type) {
			case *ast.AssignStmt:
				targets = s.Lhs
			case *ast.IncDecStmt:
				targets = []ast.Expr{s.X}
			case *ast.RangeStmt:
				if s.Tok == token.ASSIGN {
					targets = []ast.Expr{s.Key, s.Value}
				}
			}
			for _, target := range targets {
				variable := v.assignedLocal(target)
				if variable != nil && !v.boxed[variable] && (variable.Pos() < lit.Pos() || variable.Pos() >= lit.End()) {
					v.unsupported(target.Pos(), fmt.Sprintf("the function literal assigns %s, a variable of the function around it, "+
						"which is not supported yet", variable.Name()))
				}
			}
			return true
		})
		return true
	})
}

// assignedLocal returns the local variable an assignment target is, or is a
// field of without a pointer in between, if there is one.
func (v *fnVerifier) assignedLocal(e ast.Expr) *types.Var {
	for e != nil {
		switch x := ast.Unparen(e).(type) {
		case *ast.Ident:
			variable, ok := v.info.ObjectOf(x).(*types.Var)
			if !ok || variable.IsField() || variable.Pkg() == nil || variable.Parent() == variable.Pkg().Scope() {
				return nil
			}
			return variable
		case *ast.SelectorExpr:
			if _, viaPointer := pointee(v.info.TypeOf(x.X)); viaPointer {
				return nil
			}
			selection := v.info.Selections[x]
			if selection == nil || selection.Kind() != types.FieldVal || hopsPointer(v.info.TypeOf(x.X), selection.Index()) {
				return nil
			}
			e = x.X
		default:
			return nil
		}
	}
	return nil
}

// litFrame is a literal whose body is being executed: its signature, the
// states in which it returned with their results, the deferred calls of the
// frame around it, and that frame.
type litFrame struct {
	lit      *ast.FuncLit
	sig      *types.Signature
	ends     []litEnd
	deferred []deferredCall
	outer    *litFrame
}

// litEnd is a state in which a literal returned, with its results.
type litEnd struct {
	st      *state
	results []value
}

// inlineSite is where a literal being executed was called: the position of
// the call, or of the return at which a deferred literal runs.
type inlineSite struct {
	pos  token.Pos
	what string
}

// callLiteral verifies a call of a literal used in place. Its arguments are
// evaluated before it, as for any call; the call is an event of the unit
// that may change memory.
func (v *fnVerifier) callLiteral(call *ast.CallExpr, lit *ast.FuncLit, st *state, guard []*logic.Term) []value {
	sig := v.info.TypeOf(lit).(*types.Signature)
	u := v.unit
	operands := u.pushCeiling()
	if len(call.Args) != sig.Params().Len() {
		v.unsupported(call.Pos(), "a call with several results as the arguments of another call is not supported yet")
	}
	args := make([]value, len(call.Args))
	for i, arg := range call.Args {
		args[i] = v.evalAs(arg, sig.Params().At(i).Type(), st, guard)
	}
	u.reach(operands)
	before := st.mem
	results := v.inline(lit, args, st, guard, inlineSite{call.Pos(), "called"})
	name := "the function literal"
	if id, ok := ast.Unparen(call.Fun).(*ast.Ident); ok {
		name = id.Name
	}
	u.calls = append(u.calls, unitCall{name: name, pos: call.Pos()})
	if changed(before, st.mem) {
		u.wrote(st, "the call to "+name)
	}
	u.event()
	return results
}

// changed reports whether two memories differ in some region.
func changed(a, b memory) bool {
	if len(a) != len(b) {
		return true
	}
	for key, region := range a {
		if b[key] != region {
			return true
		}
	}
	return false
}

// inline executes the body of a literal on given arguments, in the state at
// the call, and leaves in that state what holds once the literal has
// returned. guard holds the conditions under which the call runs at all;
// where they fail, nothing changes.
func (v *fnVerifier) inline(lit *ast.FuncLit, args []value, st *state, guard []*logic.Term, site inlineSite) []value {
	if v.inlining[lit] {
		v.unsupported(site.pos, "the function literal calls itself, which cannot be verified where it is written")
	}
	v.inlining[lit] = true
	defer delete(v.inlining, lit)
	// The statements of the body are evaluated in units of their own; the
	// unit of the call waits until the body has run.
	suspended := v.unit
	v.unit = nil
	defer func() { v.unit = suspended }()
	v.sites = append(v.sites, site)
	defer func() { v.sites = v.sites[:len(v.sites)-1] }()

	sig := v.info.TypeOf(lit).(*types.Signature)
	frame := &litFrame{lit: lit, sig: sig, deferred: st.deferred, outer: v.lit}
	v.lit = frame
	defer func() { v.lit = frame.outer }()
	run := st.clone()
	run.deferred = nil
	if len(guard) > 0 {
		run.assume(logic.And(guard...))
	}
	for i := range sig.Params().Len() {
		v.bind(run, sig.Params().At(i), args[i])
	}
	for result := range sig.Results().Variables() {
		v.bind(run, result, zeroValue(result.Type()))
	}
	v.seq(lit.Body.List, lit.Body.Lbrace, lit.Body.Rbrace, run, ctrl{}, func(end *state) {
		v.returned(end, nil, lit.Body.Rbrace)
	})
	ends := frame.ends
	if len(guard) > 0 {
		// Where the call does not run, the state is as it was. Its results
		// are not used there.
		skipped := st.clone()
		skipped.assume(logic.Not(logic.And(guard...)))
		results := make([]value, sig.Results().Len())
		for i := range results {
			results[i] = zeroValue(sig.Results().At(i).Type())
		}
		ends = append(ends, litEnd{skipped, results})
	}
	return v.join(st, ends, sig)
}

// returned ends the frame being executed in a state, with the results the
// return gives, or nil for those its result variables hold: the results
// are assigned, the calls the frame put off run, last one first, and the
// results are read back, since a deferred call may change a result that
// lives in memory. For the function itself the postcondition is then
// checked; a literal hands the state to its call.
func (v *fnVerifier) returned(st *state, results []value, pos token.Pos) {
	vars := v.fn.results
	if v.lit != nil {
		vars = slices.Collect(v.lit.sig.Results().Variables())
	}
	if results == nil {
		results = make([]value, len(vars))
		for i, result := range vars {
			results[i] = v.current(st, result)
		}
	}
	for i, result := range vars {
		held := st.vals[result]
		switch {
		case results[i] == nil:
		case v.boxed[result] && held != nil:
			v.put(st, v.cellsOf(result.Type()), held[0], held[1], results[i])
		case !v.boxed[result]:
			st.vals[result] = results[i]
		}
	}
	for _, put := range slices.Backward(st.deferred) {
		// A deferred call is a statement of its own, so it may modify
		// memory; what it returns is dropped.
		v.invoke(put.call, put.fn, put.args, st, nil)
	}
	st.deferred = nil
	for i, result := range vars {
		if results[i] != nil && st.vals[result] != nil {
			results[i] = v.current(st, result)
		}
	}
	if v.lit == nil {
		v.atReturn(st, results, pos)
		return
	}
	st.deferred = v.lit.deferred
	v.lit.ends = append(v.lit.ends, litEnd{st, results})
}

// join leaves in st, the state at a call of a literal, what holds after the
// call, given the states in which the body returned. Every one of them
// began as a copy of st and only added facts to it.
//
// With one end, that end is the state after the call. With several, a new
// constant path says which end was reached: the facts each end added hold
// when path names it, and every variable, region of memory, result, and
// bound of memory that differs between the ends is a choice on path. With
// none, the call never returns, and nothing after it is reached.
//
// The variables of the literal itself are dropped: nothing after the call
// can name them.
func (v *fnVerifier) join(st *state, ends []litEnd, sig *types.Signature) []value {
	known := len(st.hyps)
	for _, end := range ends {
		if len(end.st.hyps) < known || (known > 0 && end.st.hyps[known-1] != st.hyps[known-1]) {
			panic("vego: internal error: the state in which a function literal returned is not an extension of the state at its call")
		}
	}
	keep := func(vals map[*types.Var]value) map[*types.Var]value {
		kept := make(map[*types.Var]value, len(st.vals))
		for variable := range st.vals {
			kept[variable] = vals[variable]
		}
		return kept
	}
	switch len(ends) {
	case 0:
		st.assume(logic.False())
		results := make([]value, sig.Results().Len())
		for i := range results {
			results[i] = zeroValue(sig.Results().At(i).Type())
		}
		return results
	case 1:
		end := ends[0].st
		st.vals, st.mem, st.brk, st.hyps, st.chosen, st.noted = keep(end.vals), end.mem, end.brk, end.hyps, end.chosen, end.noted
		return ends[0].results
	}
	path := v.fresh("path", logic.Int)
	which := make([]*logic.Term, len(ends))
	facts := []*logic.Term{logic.Le(logic.IntLit(0), path), logic.Lt(path, logic.IntLit(int64(len(ends))))}
	var given []*logic.Term
	for i, end := range ends {
		which[i] = logic.Eq(path, logic.IntLit(int64(i)))
		added := end.st.hyps[known:]
		given = append(given, added...)
		facts = append(facts, logic.Implies(which[i], logic.And(added...)))
	}
	// choose returns the term that is the i-th of terms when path is i.
	choose := func(terms []*logic.Term) *logic.Term {
		if !slices.ContainsFunc(terms, func(t *logic.Term) bool { return t != terms[0] }) {
			return terms[0]
		}
		given = append(given, terms...)
		chosen := terms[len(terms)-1]
		for i := len(terms) - 2; i >= 0; i-- {
			chosen = logic.Ite(which[i], terms[i], chosen)
		}
		return chosen
	}
	chooseValue := func(of func(end litEnd) value) value {
		first := of(ends[0])
		if first == nil {
			return nil
		}
		joined := make(value, len(first))
		for j := range first {
			terms := make([]*logic.Term, len(ends))
			for i, end := range ends {
				terms[i] = of(end)[j]
			}
			joined[j] = choose(terms)
		}
		return joined
	}
	vals := map[*types.Var]value{}
	for variable := range st.vals {
		vals[variable] = chooseValue(func(end litEnd) value { return end.st.vals[variable] })
	}
	mem := memory{}
	regions := map[string]logic.Sort{}
	for _, end := range ends {
		for key, region := range end.st.mem {
			regions[key] = region.Sort
		}
	}
	for _, key := range slices.Sorted(maps.Keys(regions)) {
		terms := make([]*logic.Term, len(ends))
		for i, end := range ends {
			terms[i] = end.st.mem.region(key, regions[key])
		}
		mem[key] = choose(terms)
	}
	brks := make([]*logic.Term, len(ends))
	for i, end := range ends {
		brks[i] = end.st.brk
	}
	results := make([]value, sig.Results().Len())
	for k := range results {
		results[k] = chooseValue(func(end litEnd) value { return end.results[k] })
	}
	st.vals, st.mem, st.brk = vals, mem, choose(brks)
	for _, fact := range facts {
		st.assume(fact)
	}
	// What the ends depended on decides path; see tieFailures.
	joined := forward{given: given, produced: []string{path.Name}, facts: facts}
	for _, taken := range st.chosen {
		joined.path = append(joined.path, taken.cond)
	}
	v.forwards = append(v.forwards, joined)
	return results
}

// report emits a diagnostic. One found while the body of a literal is
// executed says through which calls it was reached, since the body is
// verified at each of them.
func (v *fnVerifier) report(pos token.Pos, format string, args ...any) {
	if len(v.sites) > 0 {
		var through []string
		for _, site := range v.sites {
			at := v.pass.Fset.Position(site.pos)
			through = append(through, fmt.Sprintf("in the function literal %s at %s:%d:%d", site.what, filepath.Base(at.Filename), at.Line, at.Column))
		}
		format, args = format+"%s", append(slices.Clip(args), ", "+strings.Join(through, ", "))
	}
	v.pkgVerifier.report(pos, format, args...)
}
