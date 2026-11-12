package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"maps"
	"math/big"
	"path/filepath"
	"slices"
	"strings"

	"github.com/spachava753/laas/vego/internal/logic"
	"github.com/spachava753/laas/vego/internal/solver"
	"golang.org/x/tools/go/types/typeutil"
)

// sentinelFact marks a package-level error variable that a proof of its
// package took to be non-nil, so that a package that assigns to it can be
// told.
type sentinelFact struct{}

func (*sentinelFact) AFact() {}

func (*sentinelFact) String() string { return "sentinel" }

// findSentinels records the package-level error variables that are known to
// be non-nil: those initialised with errors.New or fmt.Errorf and never
// assigned or addressed anywhere in the package, provided that no code of
// the package can run before they are initialised. For an exported variable
// this relies on other packages not assigning to it; one that is analysed
// and does is reported.
func (pv *pkgVerifier) findSentinels() {
	pv.sentinels = map[*types.Var]bool{}
	pv.unsettled = map[*types.Var]string{}
	pv.reassigned = map[*types.Var]bool{}
	pv.relied = map[*types.Var]bool{}
	for _, file := range pv.pass.Files {
		for _, decl := range file.Decls {
			gen, ok := decl.(*ast.GenDecl)
			if !ok || gen.Tok != token.VAR {
				continue
			}
			for _, spec := range gen.Specs {
				spec := spec.(*ast.ValueSpec)
				for i, name := range spec.Names {
					if len(spec.Values) != len(spec.Names) {
						break
					}
					call, isCall := ast.Unparen(spec.Values[i]).(*ast.CallExpr)
					variable, _ := pv.info.Defs[name].(*types.Var)
					if isCall && variable != nil && errorConstructor(typeutil.StaticCallee(pv.info, call)) {
						pv.sentinels[variable] = true
					}
				}
			}
		}
	}
	changed := func(e ast.Expr) {
		e = ast.Unparen(e)
		if sel, ok := e.(*ast.SelectorExpr); ok {
			e = sel.Sel
		}
		id, ok := e.(*ast.Ident)
		if !ok {
			return
		}
		variable, ok := pv.info.Uses[id].(*types.Var)
		if !ok {
			return
		}
		delete(pv.sentinels, variable)
		pv.reassigned[variable] = true
		// A proof in the variable's own package may rest on its value.
		if variable.Pkg() != nil && variable.Pkg() != pv.pass.Pkg && pv.pass.ImportObjectFact(variable, new(sentinelFact)) {
			pv.report(e.Pos(), "%s.%s may be changed here, but proofs in package %s rely on it being the error it was declared with",
				variable.Pkg().Name(), variable.Name(), variable.Pkg().Path())
		}
	}
	for _, file := range pv.pass.Files {
		ast.Inspect(file, func(n ast.Node) bool {
			switch n := n.(type) {
			case *ast.AssignStmt:
				for _, lhs := range n.Lhs {
					changed(lhs)
				}
			case *ast.UnaryExpr:
				if n.Op == token.AND {
					changed(n.X)
				}
			case *ast.RangeStmt:
				if n.Key != nil {
					changed(n.Key)
				}
				if n.Value != nil {
					changed(n.Value)
				}
			}
			return true
		})
	}
	if len(pv.sentinels) == 0 {
		return
	}
	if hidden := pv.hiddenInitCode(); hidden != "" {
		for variable := range pv.sentinels {
			pv.unsettled[variable] = hidden
		}
		clear(pv.sentinels)
	}
}

// hiddenInitCode looks for code that runs while the package-level variables
// are being initialised and that Go's ordering of initialisers does not see.
// Go initialises a variable after everything its initialiser refers to,
// following calls of named functions. A call of a function value or of an
// interface method, a goroutine, and a function of another package that is
// handed something of this package to call back are not followed, so through
// them a function of this package may run before a variable it reads has
// its value. It returns a description of the first such place, or "".
func (pv *pkgVerifier) hiddenInitCode() string {
	bodies := map[*types.Func]*ast.FuncDecl{}
	values := map[*types.Var]ast.Expr{}
	var initialisers []ast.Expr
	for _, file := range pv.pass.Files {
		for _, decl := range file.Decls {
			switch decl := decl.(type) {
			case *ast.FuncDecl:
				if fn, ok := pv.info.Defs[decl.Name].(*types.Func); ok {
					bodies[fn] = decl
				}
			case *ast.GenDecl:
				for _, spec := range decl.Specs {
					if spec, ok := spec.(*ast.ValueSpec); ok && decl.Tok == token.VAR {
						initialisers = append(initialisers, spec.Values...)
						for i, name := range spec.Names {
							if variable, ok := pv.info.Defs[name].(*types.Var); ok && len(spec.Values) > 0 {
								values[variable] = spec.Values[min(i, len(spec.Values)-1)]
							}
						}
					}
				}
			}
		}
	}
	at := func(pos token.Pos, what string) string {
		position := pv.pass.Fset.Position(pos)
		return fmt.Sprintf("%s at %s:%d", what, filepath.Base(position.Filename), position.Line)
	}
	// named returns the package-level variable or the function that an
	// expression names, if it names one.
	named := func(e ast.Expr) types.Object {
		e = ast.Unparen(e)
		if sel, ok := e.(*ast.SelectorExpr); ok && pv.info.Selections[sel] == nil {
			e = sel.Sel
		}
		id, ok := e.(*ast.Ident)
		if !ok {
			return nil
		}
		switch obj := pv.info.Uses[id].(type) {
		case *types.Func:
			return obj
		case *types.Var:
			if obj.Pkg() != nil && obj.Parent() == obj.Pkg().Scope() {
				return obj
			}
		}
		return nil
	}
	// These hold no code of this package: something whose type has no
	// room for any; a variable of another package and what a function of
	// another package returns, since code of this package gets into the
	// hands of another package only by being handed over, which is itself
	// looked for below; and a variable of this package that is never
	// assigned and was declared with such a value, as a sentinel is.
	visiting := map[*types.Var]bool{}
	var inert func(e ast.Expr) bool
	inert = func(e ast.Expr) bool {
		if pv.codeless(pv.info.TypeOf(e), map[types.Type]bool{}) {
			return true
		}
		if variable, ok := named(e).(*types.Var); ok {
			if variable.Pkg() != pv.pass.Pkg || pv.sentinels[variable] {
				return true
			}
			if values[variable] == nil || pv.reassigned[variable] || visiting[variable] {
				return false
			}
			visiting[variable] = true
			defer delete(visiting, variable)
			return inert(values[variable])
		}
		call, ok := ast.Unparen(e).(*ast.CallExpr)
		if !ok {
			return false
		}
		callee := typeutil.StaticCallee(pv.info, call)
		return callee != nil && callee.Pkg() != pv.pass.Pkg
	}
	seen := map[*types.Func]bool{}
	var scan func(root ast.Node) string
	scan = func(root ast.Node) string {
		found := ""
		ast.Inspect(root, func(n ast.Node) bool {
			if found != "" {
				return false
			}
			switch n := n.(type) {
			case *ast.FuncLit:
				// Writing a function down does not run it. Calling it, or
				// handing it to another package, is seen where that
				// happens.
				return false
			case *ast.GoStmt:
				found = at(n.Pos(), "a goroutine is started")
			case *ast.AssignStmt:
				// What is put into a variable of another package, or into
				// anything but a plain variable, which may be memory that
				// another package can reach, may be called from there.
				for i, lhs := range n.Lhs {
					value := n.Rhs[min(i, len(n.Rhs)-1)]
					_, plain := ast.Unparen(lhs).(*ast.Ident)
					variable, isVariable := named(lhs).(*types.Var)
					if (isVariable && variable.Pkg() != pv.pass.Pkg) || (!plain && !inert(value)) {
						found = at(lhs.Pos(), fmt.Sprintf("%s is assigned, which another package may read", types.ExprString(lhs)))
					}
				}
			case *ast.SendStmt:
				if !inert(n.Value) {
					found = at(n.Pos(), "something of this package is sent on a channel")
				}
			case *ast.RangeStmt:
				// A range clause assigns too.
				for _, target := range []ast.Expr{n.Key, n.Value} {
					if target == nil || n.Tok != token.ASSIGN {
						continue
					}
					_, plain := ast.Unparen(target).(*ast.Ident)
					variable, isVariable := named(target).(*types.Var)
					if (isVariable && variable.Pkg() != pv.pass.Pkg) || (!plain && !pv.codeless(pv.info.TypeOf(target), map[types.Type]bool{})) {
						found = at(target.Pos(), fmt.Sprintf("%s is assigned, which another package may read", types.ExprString(target)))
					}
				}
				// Ranging over a function calls it.
				if _, isFunc := pv.info.TypeOf(n.X).Underlying().(*types.Signature); !isFunc {
					break
				}
				ranged, _ := named(n.X).(*types.Func)
				decl := bodies[ranged]
				switch {
				case ranged == nil || decl == nil || decl.Body == nil:
					found = at(n.X.Pos(), "a function that is not a named function of this package is ranged over")
				case !seen[ranged]:
					seen[ranged] = true
					found = scan(decl.Body)
				}
			case *ast.CallExpr:
				// Some built-in functions pass on what they are given:
				// append and copy may write into an array that another
				// package holds, and panic hands its value to the runtime,
				// which asks it for a text. Those that only measure, make,
				// or remove things do not.
				id, _ := ast.Unparen(n.Fun).(*ast.Ident)
				if builtin, ok := pv.info.Uses[id].(*types.Builtin); ok && id != nil {
					keeps := []string{"len", "cap", "new", "make", "delete", "clear", "min", "max", "real", "imag", "complex", "print", "println", "recover"}
					if !slices.Contains(keeps, builtin.Name()) && slices.ContainsFunc(n.Args, func(arg ast.Expr) bool { return !inert(arg) }) {
						found = at(n.Pos(), fmt.Sprintf("something of this package is handed to %s", builtin.Name()))
					}
				}
				if tv := pv.info.Types[n.Fun]; tv.IsType() || tv.IsBuiltin() {
					break
				}
				callee := typeutil.StaticCallee(pv.info, n)
				switch {
				case callee == nil:
					// A function written out and called on the spot is
					// read like one that has a name.
					if literal, ok := ast.Unparen(n.Fun).(*ast.FuncLit); ok {
						found = scan(literal.Body)
						break
					}
					found = at(n.Pos(), "a function value or an interface method is called")
				case callee.Pkg() == pv.pass.Pkg:
					decl := bodies[callee.Origin()]
					switch {
					case decl == nil || decl.Body == nil:
						found = at(n.Pos(), callee.Name()+", whose body is not available, is called")
					case !seen[callee.Origin()]:
						seen[callee.Origin()] = true
						found = scan(decl.Body)
					}
				default:
					// A type argument can carry code too: the methods of a
					// type of this package.
					for _, argument := range pv.typeArguments(n) {
						if !pv.codeless(argument, map[types.Type]bool{}) {
							found = at(n.Pos(), fmt.Sprintf("the type %s is handed to %s.%s, which may call its methods",
								argument, callee.Pkg().Name(), callee.Name()))
						}
					}
					operands := slices.Clone(n.Args)
					if sel, ok := ast.Unparen(n.Fun).(*ast.SelectorExpr); ok && pv.info.Selections[sel] != nil {
						operands = append(operands, sel.X)
					}
					for _, operand := range operands {
						if !inert(operand) {
							found = at(operand.Pos(), fmt.Sprintf("%s is handed to %s.%s, which may call back into this package",
								types.ExprString(operand), callee.Pkg().Name(), callee.Name()))
							break
						}
					}
				}
			}
			return true
		})
		return found
	}
	for _, initialiser := range initialisers {
		if found := scan(initialiser); found != "" {
			return found
		}
	}
	return ""
}

// codeless reports whether no value of a type can hold code of this
// package: the type has no interface, function, or channel in it, however
// deep, and no type declared in this package, whose methods a value brings
// with it, also not as a type argument.
func (pv *pkgVerifier) codeless(t types.Type, seen map[types.Type]bool) bool {
	if t == nil {
		return false
	}
	if seen[t] {
		return true
	}
	seen[t] = true
	// A type declared here brings its methods, and a generic type of
	// another package those of the types it is instantiated with.
	if named, ok := types.Unalias(t).(*types.Named); ok {
		if named.Obj().Pkg() == pv.pass.Pkg {
			return false
		}
		for argument := range named.TypeArgs().Types() {
			if !pv.codeless(argument, seen) {
				return false
			}
		}
	}
	switch u := t.Underlying().(type) {
	case *types.Basic:
		return u.Kind() != types.UnsafePointer
	case *types.Pointer:
		return pv.codeless(u.Elem(), seen)
	case *types.Slice:
		return pv.codeless(u.Elem(), seen)
	case *types.Array:
		return pv.codeless(u.Elem(), seen)
	case *types.Map:
		return pv.codeless(u.Key(), seen) && pv.codeless(u.Elem(), seen)
	case *types.Struct:
		for field := range u.Fields() {
			if !pv.codeless(field.Type(), seen) {
				return false
			}
		}
		return true
	}
	return false
}

// typeArguments returns the type arguments a call instantiates its callee
// with, written out or inferred.
func (pv *pkgVerifier) typeArguments(call *ast.CallExpr) []types.Type {
	fun := ast.Unparen(call.Fun)
	switch indexed := fun.(type) {
	case *ast.IndexExpr:
		fun = indexed.X
	case *ast.IndexListExpr:
		fun = indexed.X
	}
	if sel, ok := fun.(*ast.SelectorExpr); ok {
		fun = sel.Sel
	}
	id, ok := fun.(*ast.Ident)
	if !ok {
		return nil
	}
	var arguments []types.Type
	for argument := range pv.info.Instances[id].TypeArgs.Types() {
		arguments = append(arguments, argument)
	}
	return arguments
}

// outcome is what verifying a function established about its failure,
// beyond the diagnostics it produced.
type outcome struct {
	// complete is set when verification ran to the end; the rest is only
	// meaningful then, and only for functions that return an error.
	complete bool
	// forces is set when the contract makes the function succeed for some
	// input.
	forces bool
	// outside is set when execution reached a call without a contract that
	// returns an error; reached holds the verified callees returning an
	// error that it reached.
	outside bool
	reached map[*funcInfo]bool
}

// verified verifies a function once and records the outcome.
func (pv *pkgVerifier) verified(fn *funcInfo) {
	if _, done := pv.outcomes[fn]; done {
		return
	}
	result := &outcome{}
	pv.outcomes[fn] = result
	pv.current = fn
	defer func() { pv.current = nil }()
	pv.run(fn, func(v *fnVerifier) {
		v.verify()
		if len(errorResults(fn)) > 0 {
			result.forces = v.forcesSuccess()
		}
		result.outside, result.reached, result.complete = v.outside, v.reached, true
	})
}

// reportAlwaysFailing rejects every contract that its function could meet
// by failing on every call. A postcondition of the form "err = nil -> ..."
// alone says what success looks like but never that success happens.
//
// A function is excused when it cannot promise success: its contract forces
// none, and it reaches a call whose failure no contract predicts, either
// directly or through a verified callee that is itself excused. The excused
// functions are the least fixed point of that rule, so a cycle of functions
// that only call each other excuses nobody, and the order of declarations
// does not matter.
func (pv *pkgVerifier) reportAlwaysFailing() map[*funcInfo]bool {
	excused := map[*funcInfo]bool{}
	candidate := func(fn *funcInfo) bool {
		result := pv.outcomes[fn]
		return result != nil && result.complete && len(errorResults(fn)) > 0 && !result.forces
	}
	for changed := true; changed; {
		changed = false
		for _, fn := range pv.order {
			if !candidate(fn) || excused[fn] {
				continue
			}
			through := slices.ContainsFunc(slices.Collect(maps.Keys(pv.outcomes[fn].reached)), func(callee *funcInfo) bool {
				return pv.outcomes[fn].reached[callee] && excused[callee]
			})
			if pv.outcomes[fn].outside || through {
				excused[fn], changed = true, true
			}
		}
	}
	for _, fn := range pv.order {
		if candidate(fn) && !excused[fn] {
			fn.failed = true
			pv.report(fn.decl.Name.Pos(), "the contract of %s would also be met by a function that always returns an error; "+
				"state when it succeeds with a clause such as \"condition -> err = nil\", "+
				"where the condition is about the inputs and some input satisfies it", fn.obj.Name())
		}
	}
	return excused
}

// trustForces reports whether a trusted contract forces success for some
// input. One that does not is a source of unpredictable failure: nothing
// says when the function succeeds.
func (pv *pkgVerifier) trustForces(fn *funcInfo) bool {
	if fn.forces != nil {
		return *fn.forces
	}
	forces := false
	fn.forces = &forces
	// The contract is examined on its own; parts of the signature of types
	// vego does not model take no part in it.
	pv.run(fn, func(v *fnVerifier) {
		v.lenient = true
		forces = v.forcesSuccess()
	})
	if fn.use != nil && len(errorResults(fn)) > 0 {
		fn.use.Unpredictable = !forces
	}
	return forces
}

// errorResults returns the indices of the results of type error.
func errorResults(fn *funcInfo) []int {
	var indices []int
	for i, result := range fn.results {
		if sort, ok := sortOf(result.Type()); ok && sort == logic.Err {
			indices = append(indices, i)
		}
	}
	return indices
}

// contractInstance resolves the contract on the state a function is entered
// in. It returns the facts of that state, which are what the precondition
// and the types of the parameters give; everything that then holds after
// any function meeting the contract has run, namely what the types of its
// outputs guarantee and the postcondition; and the terms standing for the
// error results.
func (v *fnVerifier) contractInstance(entry *state) (pre, post, failures []*logic.Term) {
	fn := v.fn
	st := entry.clone()
	for _, t := range v.frame {
		v.havoc(st, t)
	}
	st.brk = v.fresh("brk", logic.Ref)
	st.assume(logic.Le(entry.brk, st.brk))
	results := make([]value, len(fn.results))
	for i, result := range fn.results {
		if _, ok := layoutOf(result.Type()); ok {
			results[i] = v.unknown("out", result.Type(), st)
			st.assume(v.deepFacts(st.mem, results[i], result.Type(), st.brk))
		}
	}
	for _, param := range fn.params {
		if v.entry[param] != nil {
			typed := v.deepFacts(st.mem, v.entry[param], param.Type(), st.brk)
			v.typing[typed] = true
			st.assume(typed)
		}
	}
	env := &specEnv{v: v, sink: st, fn: fn, args: v.entry, results: results, now: memory{}, post: st.mem, before: entry.brk}
	for _, c := range fn.ensures {
		// A clause about a result that has no value in the logic says
		// nothing here.
		st.assume(v.calleeFormula(c, env))
	}
	// A verified function also keeps the invariants of what it hands back.
	if fn.trust == nil {
		for _, param := range fn.params {
			if v.entry[param] != nil {
				v.assumeInvariants(st, nil, st.mem, v.entry[param], param.Type())
			}
		}
		for i, result := range fn.results {
			if results[i] != nil {
				v.assumeInvariants(st, nil, st.mem, results[i], result.Type())
			}
		}
	}
	for _, index := range errorResults(fn) {
		failures = append(failures, results[index][0])
	}
	return entry.hyps, st.hyps, failures
}

// maxWitnesses bounds the inputs tried when looking for one on which a
// contract forces success.
const maxWitnesses = 3000

// forcesSuccess reports whether the contract makes the function succeed for
// some input: there is a concrete input that provably satisfies the
// precondition and for which every well-typed outcome that meets the
// postcondition has a nil error. Without such an input, an implementation
// that fails on every call may well satisfy the contract, whatever else the
// contract demands.
//
// The witness is searched among small inputs built from 0, 1, -1 and the
// numbers and strings the contract mentions. Finding none is reported, even
// though a witness outside that search may exist: the contract must then be
// stated so that its success condition is plainly satisfiable.
func (v *fnVerifier) forcesSuccess() bool {
	pre, post, failures := v.contractInstance(v.enter())
	opts := solver.Options{Preds: v.res.Preds, MaxSteps: v.maxSteps}
	// The sample error is the one sample that is not a literal; all that
	// is known of it is that it is not nil.
	known := []*logic.Term{logic.Not(logic.IsNil(someError))}
	forced := make([]bool, len(failures))
	v.someInput(post, func(input *witness) bool {
		if solver.Prove(known, logic.And(input.apply(pre)...), opts) != solver.Proved {
			return false
		}
		outcome := append(slices.Clip(known), input.apply(post)...)
		for i, failure := range failures {
			forced[i] = forced[i] || solver.Prove(outcome, logic.IsNil(input.apply([]*logic.Term{failure})[0]), opts) == solver.Proved
		}
		return !slices.Contains(forced, false)
	})
	return !slices.Contains(forced, false)
}

// someError is the sample value for an error that is not nil.
var someError = logic.Const("some error", logic.Err)

// canReach reports whether there is evidence that execution can arrive at
// the current point, given the facts that hold on the path to it. A path
// that is provably impossible cannot. Beyond that, the facts that speak
// about the inputs alone must be satisfied together by some concrete input;
// failing to refute them is not enough. Facts that depend on values the
// verifier treats as unknown, such as the result of an earlier call or the
// state after a loop, have no such witness and are taken as possible unless
// refuted, so this is an over-approximation for such paths.
func (v *fnVerifier) canReach(path []*logic.Term) bool {
	opts := solver.Options{Preds: v.res.Preds, MaxSteps: v.maxSteps}
	if solver.Prove(path, logic.False(), opts) == solver.Proved {
		return false
	}
	var inputsOnly func(t *logic.Term) bool
	inputsOnly = func(t *logic.Term) bool {
		if t.Op == logic.OpConst && t != logic.NilErr() && !v.inputs[t.Name] && !strings.HasPrefix(t.Name, entryRegion) {
			return false
		}
		return !slices.ContainsFunc(t.Args, func(arg *logic.Term) bool { return !inputsOnly(arg) })
	}
	// What must hold on the path is split into its necessary parts, so that
	// a condition on the inputs is found even inside a conjunction with
	// something unknown. Those parts must be proved for a concrete input,
	// and under the same input the path as a whole must not be refutable.
	var required []*logic.Term
	for _, fact := range path {
		for _, part := range necessary(fact) {
			if inputsOnly(part) {
				required = append(required, part)
			}
		}
	}
	known := []*logic.Term{logic.Not(logic.IsNil(someError))}
	return v.someInput(path, func(input *witness) bool {
		return solver.Prove(known, logic.And(input.apply(required)...), opts) == solver.Proved &&
			solver.Prove(append(slices.Clip(known), input.apply(path)...), logic.False(), opts) != solver.Proved
	})
}

// necessary splits a formula into formulas that must each hold whenever it
// does: the conjuncts of a conjunction, and what the negation of a
// disjunction or of an implication entails.
func necessary(t *logic.Term) []*logic.Term {
	var parts []*logic.Term
	switch {
	case t.Op == logic.OpAnd:
		for _, arg := range t.Args {
			parts = append(parts, necessary(arg)...)
		}
	case t.Op == logic.OpNot && t.Args[0].Op == logic.OpOr:
		for _, arg := range t.Args[0].Args {
			parts = append(parts, necessary(logic.Not(arg))...)
		}
	case t.Op == logic.OpNot && t.Args[0].Op == logic.OpImplies:
		parts = append(necessary(t.Args[0].Args[0]), necessary(logic.Not(t.Args[0].Args[1]))...)
	default:
		parts = []*logic.Term{t}
	}
	return parts
}

// witness is a concrete input: values for the constants that stand for the
// parameters, and contents for the memory they refer to. Applying it to a
// formula about the state on entry gives the formula for that one input.
type witness struct {
	consts map[string]*logic.Term
	memo   map[*logic.Term]*logic.Term
	// fixed holds the arrays whose sampled contents are a literal, which
	// the sample for single elements must then leave alone.
	fixed map[string]bool
}

// store sets one cell of a region of the sampled memory.
func (s *witness) store(key string, sort logic.Sort, ref, written *logic.Term) {
	name := entryRegion + key
	region, ok := s.consts[name]
	if !ok {
		region = logic.Const(name, sort)
	}
	s.consts[name] = logic.Store(region, ref, written)
}

// storeAt sets one position of one allocation in a region of the sampled
// memory.
func (s *witness) storeAt(c cell, ref, written *logic.Term) {
	name := entryRegion + c.key
	region, ok := s.consts[name]
	if !ok {
		region = logic.Const(name, logic.SeqOf(logic.SeqOf(c.sort)))
	}
	row := logic.Store(logic.Select(region, ref), logic.IntLit(c.off), written)
	s.consts[name] = logic.Store(region, ref, row)
}

// apply replaces the constants of the entry state by their sampled values.
func (s *witness) apply(terms []*logic.Term) []*logic.Term {
	var replace func(t *logic.Term) *logic.Term
	replace = func(t *logic.Term) *logic.Term {
		if t.Op == logic.OpConst {
			if replacement, ok := s.consts[t.Name]; ok {
				return replacement
			}
			return t
		}
		if len(t.Args) == 0 {
			return t
		}
		if done, ok := s.memo[t]; ok {
			return done
		}
		args := make([]*logic.Term, len(t.Args))
		changed := false
		for i, arg := range t.Args {
			args[i] = replace(arg)
			changed = changed || args[i] != arg
		}
		result := t
		switch {
		case changed && t.Op == logic.OpIsNil:
			// Whether the nil error is nil is decided where the term is
			// built.
			result = logic.IsNil(args[0])
		case changed:
			result = &logic.Term{Op: t.Op, Sort: t.Sort, Name: t.Name, Val: t.Val, Big: t.Big, Args: args}
		}
		s.memo[t] = result
		return result
	}
	replaced := make([]*logic.Term, len(terms))
	for i, t := range terms {
		replaced[i] = replace(t)
	}
	return replaced
}

// slot is one independent choice in a sample: each of its alternatives
// fills in part of the sample.
type slot []func(s *witness)

// sampler lists the slots for the inputs of a function.
type sampler struct {
	v        *fnVerifier
	slots    []slot
	numbers  []*big.Int
	literals []*logic.Term
	// mentioned holds the names of the constants that occur in the formulas
	// the samples are for, other than in what the types alone guarantee.
	mentioned map[string]bool
	// refs counts the objects and arrays the samples contain, each of which
	// gets a reference of its own.
	refs int64
}

// fitting returns the sample numbers that are values of an integer type.
func (b *sampler) fitting(t types.Type) []*logic.Term {
	var values []*logic.Term
	lo, hi, _ := b.v.intRange(t)
	for _, number := range b.numbers {
		if lo != nil && number.Cmp(lo) >= 0 && number.Cmp(hi) <= 0 {
			values = append(values, logic.BigLit(number))
		}
	}
	return values
}

// texts returns sample strings: short runs of one repeated byte, and the
// string literals the formulas mention.
func (b *sampler) texts() []*logic.Term {
	var values []*logic.Term
	bytes := b.fitting(types.Typ[types.Uint8])
	for _, length := range b.fitting(types.Typ[types.Int]) {
		if length.Value().Sign() < 0 || length.Value().Cmp(big.NewInt(64)) > 0 {
			continue
		}
		for _, element := range bytes[:min(len(bytes), 3)] {
			values = append(values, logic.Fill(length, element))
		}
	}
	// A literal the formulas mention may be a slice literal, whose elements
	// need not be bytes.
	opts := solver.Options{MaxSteps: b.v.maxSteps}
	for _, literal := range b.literals {
		if literal.Sort == logic.IntSeq && solver.Prove(nil, b.v.elementFacts(literal, types.Typ[types.Uint8]), opts) == solver.Proved {
			values = append(values, literal)
		}
	}
	return values
}

// binding says how the leaves of a sampled value are filled in, and under
// which name each is known to the formulas: the constant of a parameter, or
// the region of memory a field lives in.
type binding struct {
	set  func(s *witness, leaf int, term *logic.Term)
	name func(leaf int) string
}

// choose adds a slot. A slot for something the formulas never mention would
// multiply the samples without changing what any of them proves, so it keeps
// its first alternative only.
func (b *sampler) choose(alternatives slot, names ...string) {
	if !slices.ContainsFunc(names, func(name string) bool { return b.mentioned[name] }) {
		alternatives = alternatives[:min(len(alternatives), 1)]
	}
	b.slots = append(b.slots, alternatives)
}

// add creates the slots for a value of type t. A pointer is nil or refers to
// an object of its own, whose fields are sampled in turn; pointers inside
// that object stay nil, so that samples stay small. A value no sample exists
// for stays symbolic.
func (b *sampler) add(t types.Type, to binding, nested bool) {
	scalar := func(choices []*logic.Term) {
		var alternatives slot
		for _, choice := range choices {
			alternatives = append(alternatives, func(s *witness) { to.set(s, 0, choice) })
		}
		b.choose(alternatives, to.name(0))
	}
	object, isPointer := pointee(t)
	sort, single := sortOf(t)
	switch {
	case isPointer:
		// A pointer is nil or points to a struct in an allocation of its
		// own.
		pointTo := func(ref *logic.Term) func(s *witness) {
			return func(s *witness) {
				to.set(s, 0, ref)
				to.set(s, 1, logic.IntLit(0))
			}
		}
		if nested {
			b.slots = append(b.slots, slot{pointTo(logic.RefLit(0))})
			break
		}
		b.refs++
		ref := logic.RefLit(b.refs)
		b.choose(slot{pointTo(ref), pointTo(logic.RefLit(0))}, to.name(0))
		cells := b.v.cellsOf(object)
		b.add(object, binding{
			set:  func(s *witness, i int, term *logic.Term) { s.storeAt(cells[i], ref, term) },
			name: func(i int) string { return entryRegion + cells[i].key },
		}, true)
	case isSlice(t):
		b.addSlice(t, to)
	case isMap(t):
		b.addMap(t, to)
	case isString(t):
		scalar(b.texts())
	case single && sort == logic.Int:
		scalar(b.fitting(t))
	case single && sort == logic.Bool:
		scalar([]*logic.Term{logic.False(), logic.True()})
	case single && sort == logic.Err:
		scalar([]*logic.Term{logic.NilErr(), someError})
	case single:
		// A float has no concrete values in the logic.
	default:
		u, isStruct := t.Underlying().(*types.Struct)
		if !isStruct {
			return
		}
		for i := range u.NumFields() {
			lo, _, ok := fieldLeaves(t, i)
			if ok {
				b.add(u.Field(i).Type(), binding{
					set:  func(s *witness, j int, term *logic.Term) { to.set(s, lo+j, term) },
					name: func(j int) string { return to.name(lo + j) },
				}, nested)
			}
		}
	}
}

// addSlice creates the slots for a slice: one for its length, and one for
// each leaf of its elements, which every element of a sample shares. The
// slice gets an array of its own. For a slice of single values the literals
// the formulas mention are offered as contents too.
func (b *sampler) addSlice(t types.Type, to binding) {
	elem := elemType(t)
	leaves, ok := layoutOf(elem)
	if !ok {
		return
	}
	b.refs++
	ref := logic.RefLit(b.refs)
	cells := b.v.cellsOf(elem)
	// Slices of one element type share their regions, so what a literal
	// fixes is one array in a region.
	array := func(i int) string { return cells[i].key + "@" + ref.String() }
	names := []string{to.name(0), to.name(1), to.name(2), to.name(3)}
	for _, c := range cells {
		names = append(names, entryRegion+c.key)
	}
	sized := func(length *logic.Term, also func(s *witness)) func(s *witness) {
		return func(s *witness) {
			for i, part := range []*logic.Term{ref, logic.IntLit(0), length, length} {
				to.set(s, i, part)
			}
			also(s)
		}
	}
	var lengths slot
	for _, length := range b.fitting(types.Typ[types.Int]) {
		if length.Value().Sign() >= 0 && length.Value().Cmp(big.NewInt(64)) <= 0 {
			lengths = append(lengths, sized(length, func(*witness) {}))
		}
	}
	if sort, single := sortOf(elem); single {
		opts := solver.Options{MaxSteps: b.v.maxSteps}
		for _, literal := range b.literals {
			if literal.Sort == logic.SeqOf(sort) && solver.Prove(nil, b.v.elementFacts(literal, elem), opts) == solver.Proved {
				lengths = append(lengths, sized(logic.Len(literal), func(s *witness) {
					s.store(cells[0].key, logic.SeqOf(literal.Sort), ref, literal)
					s.fixed[array(0)] = true
				}))
			}
		}
	}
	b.choose(lengths, names...)
	for i, lf := range leaves {
		var elements []*logic.Term
		switch {
		case lf.part != partValue:
			// A slice or a pointer inside an element has no sample.
			continue
		case lf.sort == logic.Int:
			elements = b.fitting(lf.typ)
		case lf.sort == logic.Bool:
			elements = []*logic.Term{logic.False(), logic.True()}
		case lf.sort == logic.Err:
			elements = []*logic.Term{logic.NilErr(), someError}
		case lf.sort == logic.Ref:
			elements = []*logic.Term{logic.RefLit(0)}
		case lf.sort.IsSeq():
			elements = b.texts()
		}
		var fills slot
		for _, element := range elements[:min(len(elements), 3)] {
			fills = append(fills, func(s *witness) {
				if !s.fixed[array(i)] {
					// Every position holds the element, so the row serves
					// whatever length the slice has.
					row := logic.Fill(logic.IntLit(64), element)
					s.store(cells[i].key, logic.SeqOf(row.Sort), ref, row)
				}
			})
		}
		b.choose(fills, entryRegion+cells[i].key)
	}
}

// addMap creates the slot for a map: the nil map, or a map of its own with
// a single key. Values that are not a single number, boolean, or string get
// no sample beyond the nil map.
func (b *sampler) addMap(t types.Type, to binding) {
	keyType, elem := mapParts(t)
	b.refs++
	ref := logic.RefLit(b.refs)
	region := func(lf leaf) (string, logic.Sort) { return mapOwner(t) + lf.path, logic.SeqOf(logic.SeqOf(lf.sort)) }
	alternatives := slot{func(s *witness) { to.set(s, 0, logic.RefLit(0)) }}
	choices := func(of types.Type) []*logic.Term {
		sort, single := sortOf(of)
		switch {
		case isString(of):
			return b.texts()
		case single && sort == logic.Int:
			return b.fitting(of)
		case single && sort == logic.Bool:
			return []*logic.Term{logic.False(), logic.True()}
		}
		return nil
	}
	keys, held := choices(keyType), choices(elem)
	for _, key := range keys[:min(len(keys), 4)] {
		for _, val := range held[:min(len(held), 3)] {
			alternatives = append(alternatives, func(s *witness) {
				to.set(s, 0, ref)
				leaves, _ := layoutOf(elem)
				inMap := leaves[0]
				inMap.path = "#val"
				hasKey, hasSort := region(hasLeaf)
				valKey, valSort := region(inMap)
				s.store(mapOwner(t)+countLeaf.path, logic.SeqOf(logic.Int), ref, logic.IntLit(1))
				s.store(hasKey, hasSort, ref, logic.Store(logic.Fill(logic.IntLit(0), logic.False()), mapKey(key), logic.True()))
				s.store(valKey, valSort, ref, logic.Store(logic.Fill(logic.IntLit(0), zeroLeaf(leaves[0])), mapKey(key), val))
			})
		}
	}
	names := []string{to.name(0), entryRegion + mapOwner(t) + countLeaf.path, entryRegion + mapOwner(t) + hasLeaf.path}
	b.choose(alternatives, names...)
}

// someInput tries small concrete inputs until one is accepted, and reports
// whether one was. The inputs are built from 0, 1, -1, 2, 3 and the numbers
// and literals that occur in the given terms, which is where a witness for
// a condition over those terms is most likely to be found. A pointer is nil
// or refers to an object of its own, and a slice has an array of its own.
func (v *fnVerifier) someInput(terms []*logic.Term, accept func(input *witness) bool) bool {
	b := &sampler{
		v: v, mentioned: map[string]bool{},
		numbers: []*big.Int{big.NewInt(0), big.NewInt(1), big.NewInt(-1), big.NewInt(2), big.NewInt(3)},
	}
	seen := map[*logic.Term]bool{}
	var harvest func(t *logic.Term)
	harvest = func(t *logic.Term) {
		if seen[t] {
			return
		}
		seen[t] = true
		switch {
		case t.Op == logic.OpConst:
			b.mentioned[t.Name] = true
		case t.Op == logic.OpIntLit && t.Sort == logic.Int && t.Value().IsInt64() && len(b.numbers) < 12:
			for _, delta := range []int64{0, 1, -1} {
				b.numbers = append(b.numbers, new(big.Int).Add(t.Value(), big.NewInt(delta)))
			}
		case t.Op == logic.OpPush && len(b.literals) < 8:
			// A string or slice literal is a chain of appended elements.
			b.literals = append(b.literals, t)
			return
		}
		for _, arg := range t.Args {
			harvest(arg)
		}
	}
	for _, t := range terms {
		if !v.typing[t] {
			harvest(t)
		}
	}
	for _, param := range v.fn.params {
		entry := v.entry[param]
		if entry != nil {
			b.add(param.Type(), binding{
				set:  func(s *witness, i int, term *logic.Term) { s.consts[entry[i].Name] = term },
				name: func(i int) string { return entry[i].Name },
			}, false)
		}
	}
	total := 1
	for _, alternatives := range b.slots {
		total = min(total*max(len(alternatives), 1), maxWitnesses)
	}
	for n := range total {
		input := &witness{consts: map[string]*logic.Term{}, memo: map[*logic.Term]*logic.Term{}, fixed: map[string]bool{}}
		// Everything a sample contains exists.
		input.consts[v.entryBrk.Name] = logic.RefLit(b.refs + 1)
		rest := n
		for _, alternatives := range b.slots {
			if len(alternatives) == 0 {
				continue
			}
			alternatives[rest%len(alternatives)](input)
			rest /= len(alternatives)
		}
		if accept(input) {
			return true
		}
	}
	return false
}
