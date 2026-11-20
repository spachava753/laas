package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"slices"
	"strings"

	"github.com/spachava753/laas/vego/internal/logic"
	"github.com/spachava753/laas/vego/internal/solver"
	"golang.org/x/tools/go/types/typeutil"
)

// maxBranches bounds the number of conditional branches explored in one
// function, since every if statement doubles the number of paths.
const maxBranches = 4000

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
	fn *funcInfo
	// converting counts, for each expression that Go converts to an
	// interface type, the evaluations of it under way that check the
	// conversion; see converted.
	converting map[ast.Expr]int
	// held records, for each expression converted to an interface, the
	// value it had as it was converted, for the bound on what formatting
	// it writes; see fmtsize.go.
	held map[ast.Expr]value
	// heldReceiver is set in the check of a method made into a function
	// value or a method of an interface value: the receiver of the method,
	// which the contract of what it is made into cannot name, and
	// heldRemedy what a write behind it calls for instead; see madeAs.
	heldReceiver *types.Var
	heldRemedy   string
	// entry holds the values of the parameters on entry, entryBrk the number
	// below which everything that existed on entry lies, and inputs the names
	// of the constants that stand for the state on entry.
	entry    map[*types.Var]value
	entryBrk *logic.Term
	inputs   map[string]bool
	// bitTerms holds the unknowns that stand for powers of two and for the
	// bitwise and of two operands, by what they stand for, and lowZeros how
	// many low bits of such an unknown are known to be zero; see bits.go.
	bitTerms map[string]*logic.Term
	lowZeros map[string]uint
	// bitOrigins holds, by the term, how the result of a bitwise operator
	// was made.
	bitOrigins map[string]bitOrigin
	// looped holds the defer statements that lie inside a loop of their
	// own frame, the function or a literal.
	looped map[*ast.DeferStmt]bool
	// boundLits holds the variables bound to a literal used in place, lit the
	// literal whose body is being executed, inlining the literals being
	// executed, and sites the calls through which they were reached; see
	// literals.go.
	boundLits map[*types.Var]*ast.FuncLit
	lit       *litFrame
	inlining  map[*ast.FuncLit]bool
	sites     []inlineSite
	// captured holds, with a number of its own, every variable that a
	// function literal assigns and that is declared outside it, and that
	// does not live in memory. A call of the literal can change it, so
	// within a unit it is read like memory; see snapshot.
	captured map[*types.Var]int
	// boxed holds the variables of the function that live in memory because
	// their address is taken. Such a variable holds a pointer to the struct
	// that is its value.
	boxed map[*types.Var]bool
	// frame is what the Modifies clauses allow the function to write, and
	// used marks the entries some write could not do without.
	frame []target
	used  []bool
	// forbidden holds what the trusted functions running the code being
	// executed may write themselves, which that code may not; and handing
	// the functions handed over at the call being applied. See
	// callbacks.go.
	forbidden []forbidden
	handing   map[*types.Var]*handOver
	// layers holds, by the name of the constant that stands for a forgotten
	// region, what is still known of the region.
	layers map[string]*layer
	// joins holds, by the name of the constant that stands for it, each
	// region a join of the ends of a function literal made.
	joins    map[string]*joinedRegion
	names    map[string]int
	branches int
	measure  *logic.Term
	// originBody, when set, is the body of the declared function whose
	// origins of errors a function value made in it is judged by; see
	// bodyOrigins.
	originBody *ast.BlockStmt
	// unsplit is set while a statement is executed before which nothing
	// can be put, the post statement of a for loop and the init statement
	// of an else if; see unit.sometimes. elseIfs holds, by the position of
	// their keyword, the if statements that follow an else.
	unsplit bool
	elseIfs map[token.Pos]bool
	// unit is the evaluation of the operands of the statement being
	// executed, in which reads of memory are recorded so that their order
	// relative to the calls that write memory can be checked; see order.go.
	unit *unit
	// tracksFailure is set while a function that returns an error is
	// verified, whose report under the always-fails rule reads what
	// noteFailureSource and tieFailures find; nothing else does.
	tracksFailure bool
	// outside records that execution reached a call whose failure no
	// contract predicts; reached holds the verified callees returning an
	// error that execution reached, which may turn out to be excused.
	outside bool
	reached map[*funcInfo]bool
	// sources holds the calls reached so far whose failure nothing
	// predicts, and failures the returns of an error. A source only counts
	// if the function fails because of it; see tieFailures. made lists the
	// names of the constants made so far, in order, and forgotten holds, by
	// the name of the unknown that stands for it, each error variable the
	// loop entered last made unknown.
	made      []string
	sources   []failureSource
	failures  []failure
	successes []failure
	forgotten map[string]forgottenPart
	// left holds what the iterations of loops left in such variables.
	left []leftover
	// forwards holds every call made, for tieFailures.
	forwards []forward
	// lenient is set when only the contract of a function is examined, not
	// its body: parameters and results of types vego does not model are
	// then left without a value instead of being an error.
	lenient bool
	// typing holds the facts that state what the types of the parameters
	// guarantee, which mention every parameter whether or not the contract
	// does.
	typing map[*logic.Term]bool
	// misreadAs, when set, receives an annotation that cannot be resolved,
	// in place of the diagnostic at the annotation.
	misreadAs func(c *clause, err error)
	// distinct holds the errors met that differ from each other: those
	// made in the body and those of sentinels. background holds the facts
	// noted so far that speak of inputs alone and are true of every input,
	// by their text in backgroundSeen; see fact.
	distinct []*logic.Term
	// opaqueErrors holds the opaque error variables met, and madeHere the
	// errors made in the body; see noteOpaque.
	opaqueErrors, madeHere []*logic.Term
	background             []*logic.Term
	backgroundSeen         map[string]bool
	// trees holds the errors met whose tree is known, and isTargets the
	// targets of is met outside quantifiers, by their text in targetSeen;
	// see noteTree and noteIs.
	trees      []errorTree
	isTargets  []*logic.Term
	targetSeen map[string]bool
}

// run executes one task on a function, turning the panics that abandon a
// verification into diagnostics.
func (pv *pkgVerifier) run(fn *funcInfo, task func(v *fnVerifier)) {
	v := pv.newVerifier(fn)
	defer pv.costing(fn)()
	defer func() {
		switch r := recover().(type) {
		case nil, abort:
		case unsupported:
			pv.report(r.pos, "cannot verify %s: %s", fn.obj.Name(), r.msg)
		case logic.TooLarge:
			at := fn.obj.Pos()
			if fn.decl != nil {
				at = fn.decl.Name.Pos()
			}
			pv.report(at, "cannot verify %s: a formula built to verify it has grown beyond %d nodes, "+
				"which is the limit; split the function, or the expressions in it, into smaller ones", fn.obj.Name(), logic.MaxSize)
		default:
			panic(r)
		}
	}()
	task(v)
}

// newVerifier returns a verifier for one function, with nothing known yet.
func (pv *pkgVerifier) newVerifier(fn *funcInfo) *fnVerifier {
	return &fnVerifier{
		pkgVerifier: pv, fn: fn, entry: map[*types.Var]value{}, names: map[string]int{},
		reached: map[*funcInfo]bool{}, bitTerms: map[string]*logic.Term{}, lowZeros: map[string]uint{}, bitOrigins: map[string]bitOrigin{}, forgotten: map[string]forgottenPart{}, inputs: map[string]bool{}, layers: map[string]*layer{}, typing: map[*logic.Term]bool{},
		backgroundSeen: map[string]bool{}, targetSeen: map[string]bool{}, inlining: map[*ast.FuncLit]bool{}, joins: map[string]*joinedRegion{},
		converting: map[ast.Expr]int{},
		held:       map[ast.Expr]value{},
	}
}

// bodyOrigins returns what the variables of the function being verified are
// assigned, from the body of the declared function it is part of: a
// function value made there is verified on its own, but the variables it
// captures are assigned around it.
func (v *fnVerifier) bodyOrigins() *origins {
	body := v.originBody
	if body == nil && v.fn.decl != nil {
		body = v.fn.decl.Body
	}
	if body == nil {
		return &origins{sources: map[*types.Var][]source{}, unknown: map[*types.Var]bool{}}
	}
	return v.originsOf(body)
}

// enter builds the state on function entry: parameters hold arbitrary values
// that satisfy the precondition, slice parameters with the same element type
// share no element, and results hold their zero values.
func (v *fnVerifier) enter() *state {
	fn := v.fn
	st := &state{vals: map[*types.Var]value{}, mem: memory{}, brk: logic.Const("brk", logic.Ref), noted: map[string]bool{}}
	v.entryBrk = st.brk
	v.inputs[st.brk.Name] = true
	st.assume(logic.Le(logic.IntLit(1), st.brk))
	for i, param := range fn.params {
		leaves, ok := layoutOf(param.Type())
		if !ok && v.lenient {
			continue
		}
		if !ok {
			v.unsupported(param.Pos(), fmt.Sprintf("parameter %s has unsupported type %s%s", param.Name(), param.Type(), unsupportedHint(param.Type())))
		}
		// Every parameter is its own unknown, including blank ones, which
		// all share the name "_".
		name := param.Name()
		if name == "" || name == "_" {
			name = fmt.Sprintf("_@%d", i)
		}
		// The $ keeps the names of parameters apart from the names the
		// verifier uses itself, such as that of the bound of memory.
		name = "$" + name
		val := make(value, len(leaves))
		for j, lf := range leaves {
			val[j] = logic.Const(name+lf.path, lf.sort)
			v.inputs[val[j].Name] = true
		}
		st.vals[param], v.entry[param] = val, val
		typed := v.wellFormed(val, param.Type(), st.brk)
		v.typing[typed] = true
		st.assume(typed)
	}
	if fn.receiver != nil {
		// The receiver of the contract of an interface method is an
		// interface value like a parameter.
		val := value{logic.Const("$"+fn.receiver.Name(), logic.Ref)}
		v.inputs[val[0].Name] = true
		st.vals[fn.receiver], v.entry[fn.receiver] = val, val
		typed := v.wellFormed(val, fn.receiver.Type(), st.brk)
		v.typing[typed] = true
		st.assume(typed)
	}
	for _, pair := range overlapping(fn) {
		if v.entry[pair[0]] != nil && v.entry[pair[1]] != nil {
			st.assume(v.separate(v.entry[pair[0]], v.entry[pair[1]], pair[0].Type()))
		}
	}
	// Interface parameters with states that are not nil have homes of
	// their own, which every caller has shown.
	for _, pair := range v.sharing(fn) {
		if v.entry[pair[0]] != nil && v.entry[pair[1]] != nil {
			st.assume(apartHomes(v.entry[pair[0]][0], v.entry[pair[1]][0]))
		}
	}
	// Every caller has proved the invariants of what it passes.
	for _, param := range fn.params {
		if v.entry[param] != nil {
			v.assumeInvariants(st, nil, memory{}, v.entry[param], param.Type())
		}
	}
	for _, result := range fn.results {
		_, ok := layoutOf(result.Type())
		if !ok && v.lenient {
			continue
		}
		if !ok {
			v.unsupported(fn.obj.Pos(), fmt.Sprintf("result type %s is not supported%s", result.Type(), unsupportedHint(result.Type())))
		}
		st.vals[result] = zeroValue(result.Type())
	}
	pre := &specEnv{v: v, sink: st, fn: fn, args: v.entry, now: memory{}}
	for _, c := range fn.requires {
		st.assume(v.formula(c, c.node, pre))
	}
	v.frame = v.targets(fn, v.entry, st, memory{})
	v.used = make([]bool, len(v.frame))
	return st
}

// findLooped returns, for every defer statement of a body, whether it lies
// inside a loop of its own frame, the function or a literal.
func findLooped(body *ast.BlockStmt) map[*ast.DeferStmt]bool {
	looped := map[*ast.DeferStmt]bool{}
	var scan func(root ast.Node, inLoop bool)
	scan = func(root ast.Node, inLoop bool) {
		ast.Inspect(root, func(n ast.Node) bool {
			switch n := n.(type) {
			case *ast.FuncLit:
				if n != root {
					scan(n.Body, false)
					return false
				}
			case *ast.ForStmt, *ast.RangeStmt:
				if n != root && !inLoop {
					scan(n, true)
					return false
				}
			case *ast.DeferStmt:
				looped[n] = inLoop
			}
			return true
		})
	}
	scan(body, false)
	return looped
}

// findBoxed returns the variables whose address a function body takes: with
// &x or &x.f, or by calling a method with a pointer receiver on x or x.f,
// or using such a method as a value, as in x.M. Such a variable is kept in memory, in an allocation of its own that is
// created where the variable is declared, so that a pointer to it is like
// any other pointer: a write through the pointer changes the variable, and
// a write to the variable is seen through the pointer.
func (v *fnVerifier) findBoxed(body *ast.BlockStmt) map[*types.Var]bool {
	boxed := map[*types.Var]bool{}
	ast.Inspect(body, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.UnaryExpr:
			if root := v.localRoot(n.X); n.Op == token.AND && root != nil {
				boxed[root] = true
			}
		case *ast.SelectorExpr:
			// A call of a method with a pointer receiver, and a method
			// value of one, take the address of the receiver.
			sel := n
			selection := v.info.Selections[sel]
			if selection == nil || selection.Kind() != types.MethodVal {
				break
			}
			recv := selection.Obj().Type().(*types.Signature).Recv()
			if _, wantPointer := recv.Type().Underlying().(*types.Pointer); !wantPointer {
				break
			}
			// The method may be promoted from an embedded struct, whose
			// address is then the one taken; a pointer on the way there
			// means that it is not part of the variable.
			t, path := v.info.TypeOf(sel.X), selection.Index()
			for _, index := range path[:len(path)-1] {
				object, isStruct := t.Underlying().(*types.Struct)
				if !isStruct {
					return true
				}
				t = object.Field(index).Type()
			}
			if _, isStruct := t.Underlying().(*types.Struct); !isStruct {
				break
			}
			if root := v.localRoot(sel.X); root != nil {
				boxed[root] = true
			}
		}
		return true
	})
	return boxed
}

// localRoot returns the local variable of a modelled struct type that an
// expression is, or is a field of, without a pointer in between.
func (v *fnVerifier) localRoot(e ast.Expr) *types.Var {
	for {
		switch x := ast.Unparen(e).(type) {
		case *ast.Ident:
			variable, ok := v.info.ObjectOf(x).(*types.Var)
			if !ok || variable.IsField() || variable.Parent() == v.pass.Pkg.Scope() || variable.Pkg() != v.pass.Pkg {
				return nil
			}
			_, isStruct := variable.Type().Underlying().(*types.Struct)
			if _, modelled := layoutOf(variable.Type()); !isStruct || !modelled {
				return nil
			}
			return variable
		case *ast.SelectorExpr:
			selection := v.info.Selections[x]
			if selection == nil || selection.Kind() != types.FieldVal {
				return nil
			}
			t := v.info.TypeOf(x.X)
			for _, index := range selection.Index() {
				object, isStruct := t.Underlying().(*types.Struct)
				if !isStruct {
					return nil
				}
				t = object.Field(index).Type()
			}
			e = x.X
		default:
			return nil
		}
	}
}

// bind gives a variable that is being created its first value. One that
// lives in memory gets a new allocation, so each execution of a declaration
// creates a variable of its own.
func (v *fnVerifier) bind(st *state, variable *types.Var, val value) {
	checkGrowth(val)
	if v.boxed[variable] {
		val = v.newObject(st, variable.Type(), val)
	}
	st.vals[variable] = val
}

// current returns the value a variable has, or nil if it has none.
func (v *fnVerifier) current(st *state, variable *types.Var) value {
	val := st.vals[variable]
	if val != nil && v.boxed[variable] {
		return v.pointedIn(st, st.mem, variable.Type(), val)
	}
	return val
}

// verify symbolically executes one annotated function from a state that
// satisfies its precondition and checks every obligation met on the way.
// Afterwards every entry of its Modifies clauses must have been needed, so
// that the clauses cannot promise callers less than the function keeps.
func (v *fnVerifier) verify() {
	fn := v.fn
	if fn.decl.Body == nil {
		v.unsupported(fn.decl.Pos(), "the function has no body")
	}
	sig := fn.obj.Type().(*types.Signature)
	if sig.TypeParams() != nil || sig.RecvTypeParams() != nil {
		v.unsupported(fn.decl.Pos(), "generic functions are not supported yet")
	}
	v.checkCopies(fn.decl)
	// A variable whose name means something else in annotations would be
	// read as that other thing, silently.
	ast.Inspect(fn.decl, func(n ast.Node) bool {
		if id, ok := n.(*ast.Ident); ok {
			variable, isVar := v.info.Defs[id].(*types.Var)
			local := !slices.Contains(fn.params, variable) && !slices.Contains(fn.results, variable)
			if isVar && !variable.IsField() && fn.ambiguous(id.Name, local) {
				v.unsupported(id.Pos(), fmt.Sprintf("the variable %s has a name that means something else in annotations; rename it", id.Name))
			}
		}
		return true
	})
	// A defer statement puts a call off until its own frame returns, the
	// function or the literal it is written in, so only a loop of that
	// frame repeats it.
	v.looped = findLooped(fn.decl.Body)
	v.boxed = v.findBoxed(fn.decl.Body)
	v.classifyLiterals()
	st := v.enter()
	for _, variable := range slices.Concat(fn.params, fn.results) {
		if v.boxed[variable] && st.vals[variable] != nil {
			v.bind(st, variable, st.vals[variable])
		}
	}
	// A precondition that nothing satisfies would make every claim about
	// the function provable.
	if v.quickly(st, nil, logic.False()) {
		v.report(fn.decl.Name.Pos(), "nothing can satisfy the Requires clauses of %s together with what the types of its parameters guarantee, "+
			"so verifying it would prove nothing", fn.obj.Name())
	}
	for _, refused := range v.entryOnly(st) {
		v.report(refused.clause.pos, "%s", refused.message(fn.obj.Name()))
	}
	if fn.measure != nil {
		v.measure = v.intTerm(fn.measure, &specEnv{v: v, sink: st, fn: fn, args: v.entry, now: memory{}})
		v.check(st, nil, logic.Le(logic.IntLit(0), v.measure), fn.decl.Name.Pos(),
			"variant of the function may be negative: %s", fn.measure.text)
	}
	body := fn.decl.Body
	v.seq(body.List, body.Lbrace, body.Rbrace, st, ctrl{}, func(end *state) {
		v.returned(end, nil, body.Rbrace)
	})
	// A conversion to an interface type of a value without an expression
	// of its own was not checked anywhere.
	if unplaced := v.findConversions().unplaced[fn.decl]; len(unplaced) > 0 {
		v.unsupported(unplaced[0], "Go converts a value to an interface type here, and which expression it converts could not be told, "+
			"as for one result of a call with several, so the conversion cannot be checked; assign the value to a variable of its own type first")
	}
	v.tieFailures()
	for i, t := range v.frame {
		// After a failure the state may hold a false assumption, under
		// which nothing is needed.
		if !v.used[i] && !fn.failed {
			v.report(t.clause.pos, "Modifies lists %s, but %s never needs to modify it; "+
				"a Modifies clause must list exactly what the function may write", t.text, fn.obj.Name())
		}
	}
}

func (v *fnVerifier) unsupported(pos token.Pos, msg string) {
	panic(unsupported{pos, msg})
}

// misread handles an annotation that cannot be resolved: it is reported at
// the annotation, and the verification of the function is abandoned.
func (v *fnVerifier) misread(c *clause, err error) {
	if v.misreadAs != nil {
		v.misreadAs(c, err)
	} else {
		v.report(c.pos, "in %s annotation: %v", c.kind, err)
	}
	panic(abort{})
}

// fresh returns a new symbolic constant. The @ keeps generated names apart
// from Go identifiers.
func (v *fnVerifier) fresh(base string, sort logic.Sort) *logic.Term {
	if strings.HasPrefix(base, transportMark) {
		panic("vego: internal error: a name is made in the namespace of renamed states")
	}
	v.names[base]++
	name := fmt.Sprintf("%s@%d", base, v.names[base])
	v.made = append(v.made, name)
	return logic.Const(name, sort)
}

// unknown returns a value of the given type about which nothing is known
// beyond what the type guarantees.
func (v *fnVerifier) unknown(base string, t types.Type, st *state) value {
	leaves, _ := layoutOf(t)
	val := make(value, len(leaves))
	for i, lf := range leaves {
		val[i] = v.fresh(base+lf.path, lf.sort)
	}
	st.assume(v.wellFormed(val, t, st.brk))
	return val
}

// formula resolves a parsed annotation against an environment. Errors are
// reported at the annotation and abandon the verification of the function.
func (v *fnVerifier) formula(c *clause, node *logic.Node, env logic.Env) *logic.Term {
	t, err := v.resolverOf(c).Formula(node, env)
	if err != nil {
		v.misread(c, err)
	}
	if spec, ok := env.(*specEnv); ok {
		v.noteIs(spec.sink, t)
	}
	return t
}

func (v *fnVerifier) intTerm(c *clause, env logic.Env) *logic.Term {
	t, err := v.resolverOf(c).IntTerm(c.node, env)
	if err != nil {
		v.misread(c, err)
	}
	return t
}

// check tries to prove a goal on the current path, under an optional guard
// for conditionally evaluated expressions, and reports a diagnostic when the
// proof fails. The goal is assumed afterwards either way so that one failure
// is reported once instead of cascading.
func (v *fnVerifier) check(st *state, guard []*logic.Term, goal *logic.Term, pos token.Pos, format string, args ...any) {
	for _, conjunct := range logic.Conjuncts(goal) {
		if conjunct.Op == logic.OpTrue {
			continue
		}
		done := v.at(pos)
		result := v.attempt(st, guard, conjunct)
		done()
		if result != solver.Proved {
			v.report(pos, "%s%s", fmt.Sprintf(format, args...), limitNote(result))
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
			v.checkClause(clause, v.bodyEnv(st, clause.pos), st, nil, clause.pos, "assertion may not hold")
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
	defer v.at(list[0].Pos())()
	rest := func(next *state) { v.seq(list[1:], list[0].End(), to, next, c, k) }
	switch s := list[0].(type) {
	case *ast.ForStmt:
		v.forStmt(s, spec, nil, st, rest)
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
		if isBuiltin(v.info, call, "delete") {
			v.deleteKey(call, st)
			break
		}
		v.evaluate(st, func() {
			defer v.begin()()
			v.call(call, st, nil)
		})
	case *ast.AssignStmt:
		v.assign(s, st, k)
		return
	case *ast.IncDecStmt:
		delta := logic.IntLit(1)
		if s.Tok == token.DEC {
			delta = logic.IntLit(-1)
		}
		var target lvalue
		var current *logic.Term
		v.evaluate(st, func() {
			target = v.lvalue(s.X, st, nil)
			current = v.loadRecorded(target, st, nil, 0)[0]
		})
		if current.Sort == logic.Float {
			current = v.opaque(s.Tok, current)
		} else {
			current = logic.Add(current, delta)
			v.checkFits(st, nil, current, v.info.TypeOf(s.X), s.Pos(), operation(s.Tok))
		}
		v.store(target, value{current}, st)
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
	case *ast.DeferStmt:
		v.deferStmt(s, st)
	case *ast.TypeSwitchStmt:
		v.unsupported(s.Pos(), ifaceAsserted)
	default:
		kind := strings.TrimSuffix(strings.TrimPrefix(fmt.Sprintf("%T", s), "*ast."), "Stmt")
		v.unsupported(s.Pos(), strings.ToLower(kind)+" statements are not supported yet")
	}
	k(st)
}

// deferStmt executes a defer statement: the function, the receiver, and the
// arguments are settled now, and the call is put off until the function
// returns; see atReturn. Only a call of a named function or method can be
// deferred, and not inside a loop, where the number of calls put off would
// not be known.
func (v *fnVerifier) deferStmt(s *ast.DeferStmt, st *state) {
	callee, _ := typeutil.Callee(v.info, s.Call).(*types.Func)
	lit := v.literalOf(s.Call)
	method, viaValue := throughValue(v.info, s.Call)
	switch {
	case v.looped[s]:
		v.unsupported(s.Pos(), "defer inside a loop is not supported: how many calls it puts off is not known")
	case lit != nil:
		// A literal is run at each return like any deferred call, with the
		// arguments it is given here; the variables it captures are read
		// when it runs.
		sig := v.info.TypeOf(lit).(*types.Signature)
		var args []value
		v.evaluate(st, func() {
			defer v.begin()()
			args = v.litArgs(s.Call, sig, st, nil)
		})
		st.deferred = append(slices.Clip(st.deferred), deferredCall{call: s.Call, lit: lit, litArgs: args})
		return
	case isBuiltin(v.info, s.Call, "recover"):
		v.unsupported(s.Pos(), recoverRefused)
	case viaValue:
		v.deferValue(s, st)
		return
	case method != nil:
		v.deferMethod(s, method, st)
		return
	case callee == nil:
		v.unsupported(s.Pos(), "only a call of a named function or method, of a function literal, or of a function value can be deferred; "+
			"built-in functions are not supported here")
	case errorConstructor(callee):
		v.unsupported(s.Pos(), "deferring a call that only makes an error is not supported")
	case isErrorsIs(callee):
		v.unsupported(s.Pos(), "deferring errors.Is is not supported: its result would be lost")
	}
	fn := v.contractFor(s.Call, callee)
	if len(fn.calls) > 0 {
		v.unsupported(s.Pos(), fmt.Sprintf("deferring a call of %s, which calls a function it is given, is not supported yet", callee.Name()))
	}
	// The deferred call itself runs later, so nothing here comes before it.
	var args map[*types.Var]value
	v.evaluate(st, func() {
		defer v.begin()()
		args = v.arguments(s.Call, callee, st, nil)
		_ = v.checkFormattedAlloc(st, nil, s.Call, fn, args)
	})
	st.deferred = append(slices.Clip(st.deferred), deferredCall{call: s.Call, fn: fn, args: args})
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
		// The initializer may continue in more than one state.
		init := s.Init
		v.stmt(init, st, c, func(next *state) {
			without := *s
			without.Init = nil
			v.switchStmt(&without, next, c, k)
		})
		return
	}
	var tag *logic.Term
	if s.Tag != nil {
		// Where the tag or a case is an interface and the other is not,
		// Go converts the other one to compare them. That is refused
		// before either is evaluated.
		for _, clause := range s.Body.List {
			for _, e := range clause.(*ast.CaseClause).List {
				tagType, caseType := v.info.TypeOf(s.Tag), v.info.TypeOf(e)
				switch {
				case v.isNil(e) || types.IsInterface(tagType) == types.IsInterface(caseType):
				case isError(tagType) || isError(caseType):
					v.bothErrors(s.Tag, e, e.Pos())
				default:
					v.unsupported(e.Pos(), ifaceCompared)
				}
			}
		}
		v.evaluate(st, func() { tag = v.expr(s.Tag, st, nil) })
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
			// Each case expression is evaluated on its own, after the
			// comparisons before it.
			v.evaluateSometimes(st, func() {
				switch {
				case tag == nil:
					value = v.expr(e, st, guard)
				case v.isNil(e) && tag.Sort == logic.Err:
					value = logic.IsNil(tag)
				case v.isNil(e) && tag.Sort == logic.Ref:
					value = logic.Eq(tag, logic.RefLit(0))
				case tag.Sort == logic.Err:
					value = v.errorsEqual(s.Tag, e, tag, v.expr(e, st, guard), e.Pos())
				case isIface(v.info.TypeOf(s.Tag)) || isIface(v.info.TypeOf(e)):
					v.unsupported(e.Pos(), ifaceCompared)
				default:
					// A case matches when Go's == holds, which for floats,
					// strings, and errors is not plain equality of terms.
					value = v.binary(token.EQL, tag, v.expr(e, st, guard), v.info.TypeOf(s.Tag), e.Pos(), st, guard)
				}
			})
			alternatives = append(alternatives, value)
		}
		matched := logic.Or(alternatives...)
		v.branch(clause.Pos())
		taken := st.clone()
		taken.decide(logic.And(append(slices.Clip(failed), matched)...))
		v.seq(clause.Body, clause.Colon, clause.End(), taken, inner, k)
		failed = append(failed, logic.Not(matched))
	}
	st.decide(logic.And(failed...))
	if fallback == nil {
		k(st)
		return
	}
	v.seq(fallback.Body, fallback.Colon, fallback.End(), st, inner, k)
}

func (v *fnVerifier) ifStmt(s *ast.IfStmt, st *state, c ctrl, k func(*state)) {
	elseIf := v.elseIfs[s.If]
	if s.Init != nil {
		// The initializer may continue in more than one state.
		v.unsplit = elseIf
		v.stmt(s.Init, st, c, func(next *state) {
			v.unsplit = false
			without := *s
			without.Init = nil
			v.ifStmt(&without, next, c, k)
		})
		v.unsplit = false
		return
	}
	v.branch(s.Pos())
	var cond *logic.Term
	evaluate := v.evaluate
	if elseIf {
		// The condition of an else if is evaluated only when the one
		// before it is false.
		evaluate = v.evaluateSometimes
	}
	evaluate(st, func() { cond = v.expr(s.Cond, st, nil) })
	taken, skipped := st.clone(), st.clone()
	taken.decide(cond)
	skipped.decide(logic.Not(cond))
	v.seq(s.Body.List, s.Body.Lbrace, s.Body.Rbrace, taken, c, k)
	if s.Else == nil {
		k(skipped)
		return
	}
	if next, ok := s.Else.(*ast.IfStmt); ok {
		if v.elseIfs == nil {
			v.elseIfs = map[token.Pos]bool{}
		}
		v.elseIfs[next.If] = true
	}
	v.stmt(s.Else, skipped, c, k)
}
