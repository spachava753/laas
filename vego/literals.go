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
	"golang.org/x/tools/go/types/typeutil"
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
		// Any other literal is a value. It is made where it is converted
		// to a function type, which is checked there; see functionValue.
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
			misused = append(misused, variable)
			// A variable declared with a function type of its own holds
			// the literal as a value of that type, which is checked where
			// it is declared.
			if !types.Identical(variable.Type(), info.TypeOf(bound[variable])) {
				return true
			}
			refused[id.Pos()] = fmt.Sprintf("%s holds a function literal and is used here other than by calling it; "+
				"a variable that holds a function literal is supported only when it is never assigned again and only called. "+
				"To use the literal as a value, declare the variable with a function type that has a contract, as in var %s T = func...; "+
				"to hand it to a trusted function that calls it, write the literal where it is handed over", id.Name, id.Name)
		}
		return true
	})
	for _, variable := range misused {
		delete(bound, variable)
	}
	return bound, refused
}

// recoverRefused says why a call of recover cannot be verified. In a
// verified function nothing panics, so recover could be given the value
// nil, but it returns an interface, and checking it against nil needs
// interfaces.
const recoverRefused = "recover is not supported: it returns an interface, and those are not supported yet; " +
	"recover in a function that is not verified"

// literalOf returns the literal a call calls in place, or nil.
func (v *fnVerifier) literalOf(call *ast.CallExpr) *ast.FuncLit {
	return calledLiteral(v.info, v.boundLits, call)
}

// calledLiteral returns the function literal a call runs, written there or
// bound to a variable in place, as literalUses binds them in bound, or nil.
// Such a call is not a call through a value: the literal's body runs where
// it is called, and the contract of its type plays no part.
func calledLiteral(info *types.Info, bound map[*types.Var]*ast.FuncLit, call *ast.CallExpr) *ast.FuncLit {
	switch fun := ast.Unparen(call.Fun).(type) {
	case *ast.FuncLit:
		return fun
	case *ast.Ident:
		if variable, ok := info.Uses[fun].(*types.Var); ok {
			return bound[variable]
		}
	}
	return nil
}

// throughValue says whether a call that runs no literal is a call through
// an interface value, of the method returned, or through a function value.
// Every place that tells calls apart decides it here, after calledLiteral,
// so that none of them takes one kind of call for another.
func throughValue(info *types.Info, call *ast.CallExpr) (method *types.Func, value bool) {
	callee, _ := typeutil.Callee(info, call).(*types.Func)
	switch {
	case callee == nil && isFunc(info.TypeOf(call.Fun)) && !info.Types[call.Fun].IsBuiltin() && !info.Types[call.Fun].IsType():
		return nil, true
	case isIfaceMethod(callee):
		return callee, false
	}
	return nil, false
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

// classifyLiterals finds the literals of the function being verified,
// refuses those that are not used in place and those whose signature is not
// supported, and collects the variables that a literal assigns and that
// are declared outside it.
func (v *fnVerifier) classifyLiterals() {
	body := v.fn.decl.Body
	v.captured = map[*types.Var]int{}
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
		// A variable of the function around the literal that the literal
		// assigns can change at a call of the literal; see captured.
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
					if _, known := v.captured[variable]; !known {
						v.captured[variable] = len(v.captured)
					}
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
	text string
}

// site describes, for a diagnostic, where a literal is called.
func (v *fnVerifier) site(pos token.Pos, format string, args ...any) inlineSite {
	return inlineSite{pos, fmt.Sprintf(format, args...)}
}

// placeOf gives a position as a diagnostic about a literal names it.
func (v *fnVerifier) placeOf(pos token.Pos) string {
	at := v.pass.Fset.Position(pos)
	return fmt.Sprintf("%s:%d:%d", filepath.Base(at.Filename), at.Line, at.Column)
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
	before := v.snapshot(st)
	results := v.inline(lit, args, st, guard, v.site(call.Pos(), "in the function literal called at %s", v.placeOf(call.Pos())))
	name := "the function literal"
	if id, ok := ast.Unparen(call.Fun).(*ast.Ident); ok {
		name = id.Name
	}
	u.calls = append(u.calls, unitCall{name: name, pos: call.Pos()})
	if changed(before, v.snapshot(st)) {
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
	// Where the frame ends, for a diagnostic about a literal it put off.
	end := "the return at " + v.placeOf(pos)
	if body := v.fn.decl.Body; (v.lit == nil && pos == body.Rbrace) || (v.lit != nil && pos == v.lit.lit.Body.Rbrace) {
		end = "the end of the function at " + v.placeOf(pos)
		if v.lit != nil {
			end = "the end of the function literal at " + v.placeOf(pos)
		}
	}
	for _, put := range slices.Backward(st.deferred) {
		// A deferred call is a statement of its own, so it may modify
		// memory; what it returns is dropped.
		if put.lit != nil {
			v.inline(put.lit, put.litArgs, st, nil, v.site(pos, "in the function literal deferred at %s and run at %s", v.placeOf(put.call.Pos()), end))
			continue
		}
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
// constant path says which end was reached, and the facts each end added
// hold when path names it. Every variable, result, and bound of memory that
// differs between the ends becomes a new constant, equal to what that end
// has when path names it; every region of memory that differs becomes a
// new constant too, which table relates to the region of each end at the
// references read, as it does for a region a loop forgot. Nothing a join
// makes holds more than the name of what an earlier join made, so a chain
// of calls makes terms no larger than one call does. With no end, the call
// never returns, and nothing after it is reached.
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
	index := len(v.forwards)
	which := make([]*logic.Term, len(ends))
	facts := []*logic.Term{logic.Le(logic.IntLit(0), path), logic.Lt(path, logic.IntLit(int64(len(ends))))}
	produced := []string{path.Name}
	var given []*logic.Term
	for i, end := range ends {
		which[i] = logic.Eq(path, logic.IntLit(int64(i)))
		added := end.st.hyps[known:]
		given = append(given, added...)
		facts = append(facts, logic.Implies(which[i], logic.And(added...)))
	}
	// choose returns a constant that is the i-th of terms when path is i,
	// or the term all of them are.
	choose := func(base string, terms []*logic.Term) *logic.Term {
		if !slices.ContainsFunc(terms, func(t *logic.Term) bool { return t != terms[0] }) {
			return terms[0]
		}
		checkJoinSize(terms)
		given = append(given, terms...)
		joined := v.fresh(base, terms[0].Sort)
		produced = append(produced, joined.Name)
		for i, t := range terms {
			same := v.same(joined, t)
			if t.Sort == logic.Bool {
				same = logic.Iff(joined, t)
			}
			facts = append(facts, logic.Implies(which[i], same))
		}
		return joined
	}
	chooseValue := func(base string, of func(end litEnd) value) value {
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
			joined[j] = choose(base, terms)
		}
		return joined
	}
	vals := map[*types.Var]value{}
	for _, variable := range slices.SortedFunc(maps.Keys(st.vals), func(a, b *types.Var) int { return int(a.Pos() - b.Pos()) }) {
		vals[variable] = chooseValue(variable.Name(), func(end litEnd) value { return end.st.vals[variable] })
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
		if !slices.ContainsFunc(terms, func(t *logic.Term) bool { return t != terms[0] }) {
			mem[key] = terms[0]
			continue
		}
		checkJoinSize(terms)
		joined := v.fresh("mem^"+key, regions[key])
		produced = append(produced, joined.Name)
		v.joins[joined.Name] = &joinedRegion{which: which, alternatives: terms, forward: index}
		mem[key] = joined
	}
	brks := make([]*logic.Term, len(ends))
	for i, end := range ends {
		brks[i] = end.st.brk
	}
	results := make([]value, sig.Results().Len())
	for k := range results {
		results[k] = chooseValue("result", func(end litEnd) value { return end.results[k] })
	}
	st.vals, st.mem, st.brk = vals, mem, choose("brk", brks)
	for _, fact := range facts {
		st.assume(fact)
	}
	// What the ends depended on decides path and what was chosen with it;
	// see tieFailures.
	joined := forward{given: given, produced: produced, facts: facts}
	for _, taken := range st.chosen {
		joined.path = append(joined.path, taken.cond)
	}
	if len(v.forwards) != index {
		panic("vego: internal error: a call was recorded while the ends of a function literal were joined")
	}
	v.forwards = append(v.forwards, joined)
	return results
}

// joinedRegion is a region of memory that a join made: which condition on
// path picks each end, the region each end had, and the index in forwards
// of the join, whose facts gain what is stated of the region where it is
// read, so that tieFailures can follow what the region depends on.
type joinedRegion struct {
	which        []*logic.Term
	alternatives []*logic.Term
	forward      int
}

// joinedAt states, for one reference, that a joined region holds there what
// the region of the end that was reached holds.
func (v *fnVerifier) joinedAt(now *logic.Term, joined *joinedRegion, ref *logic.Term) *logic.Term {
	var facts []*logic.Term
	flat := !now.Sort.Elem().IsSeq()
	index := v.bound("k")
	for i, alternative := range joined.alternatives {
		if flat {
			facts = append(facts, logic.Implies(joined.which[i], v.same(logic.Select(now, ref), logic.Select(alternative, ref))))
			continue
		}
		row, other := logic.Select(now, ref), logic.Select(alternative, ref)
		facts = append(facts, logic.Implies(joined.which[i], logic.And(logic.Eq(logic.Len(row), logic.Len(other)),
			logic.Forall(index, v.same(logic.Select(row, index), logic.Select(other, index))))))
	}
	return logic.And(facts...)
}

// report emits a diagnostic. One found while the body of a literal is
// executed says through which calls it was reached, since the body is
// verified at each of them.
func (v *fnVerifier) report(pos token.Pos, format string, args ...any) {
	if len(v.sites) > 0 {
		var through []string
		for _, site := range v.sites {
			through = append(through, site.text)
		}
		format, args = format+"%s", append(slices.Clip(args), ", "+strings.Join(through, ", "))
	}
	v.pkgVerifier.report(pos, format, args...)
}
