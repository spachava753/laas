package vego

import (
	"go/ast"
	"go/token"
	"go/types"
	"maps"
	"math/big"
	"slices"
	"strings"

	"github.com/spachava753/laas/vego/internal/logic"
	"github.com/spachava753/laas/vego/internal/solver"
	"golang.org/x/tools/go/types/typeutil"
)

// findSentinels records the package-level error variables that are known to
// be non-nil: those initialised with errors.New or fmt.Errorf and never
// assigned or addressed anywhere in the package. For an exported variable
// this relies on other packages not assigning to it.
func (pv *pkgVerifier) findSentinels() {
	pv.sentinels = map[*types.Var]bool{}
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
		if id, ok := ast.Unparen(e).(*ast.Ident); ok {
			if variable, ok := pv.info.Uses[id].(*types.Var); ok {
				delete(pv.sentinels, variable)
			}
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
	case isPointer && nested:
		b.slots = append(b.slots, slot{func(s *witness) { to.set(s, 0, logic.RefLit(0)) }})
	case isPointer:
		b.refs++
		ref := logic.RefLit(b.refs)
		b.choose(slot{func(s *witness) { to.set(s, 0, ref) }, func(s *witness) { to.set(s, 0, logic.RefLit(0)) }}, to.name(0))
		fields, _ := layoutOf(object)
		b.add(object, binding{
			set: func(s *witness, i int, term *logic.Term) {
				s.store(typeKey(object)+fields[i].path, logic.SeqOf(fields[i].sort), ref, term)
			},
			name: func(i int) string { return entryRegion + typeKey(object) + fields[i].path },
		}, true)
	case isSlice(t):
		b.addSlice(t, to)
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
	region := func(lf leaf) string { return "[]" + typeKey(elem) + lf.path }
	// Slices of one element type share their regions, so what a literal
	// fixes is one array in a region.
	array := func(lf leaf) string { return region(lf) + "@" + ref.String() }
	names := []string{to.name(0), to.name(1), to.name(2), to.name(3)}
	for _, lf := range leaves {
		names = append(names, entryRegion+region(lf))
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
					s.store(region(leaves[0]), logic.SeqOf(literal.Sort), ref, literal)
					s.fixed[array(leaves[0])] = true
				}))
			}
		}
	}
	b.choose(lengths, names...)
	for _, lf := range leaves {
		var elements []*logic.Term
		switch {
		case lf.part != partValue:
			// A slice inside an element has no sample.
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
				if !s.fixed[array(lf)] {
					// Every position holds the element, so the row serves
					// whatever length the slice has.
					row := logic.Fill(logic.IntLit(64), element)
					s.store(region(lf), logic.SeqOf(row.Sort), ref, row)
				}
			})
		}
		b.choose(fills, entryRegion+region(lf))
	}
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
