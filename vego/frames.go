package vego

import (
	"fmt"
	"go/token"
	"go/types"
	"maps"
	"reflect"
	"slices"
	"strings"

	"github.com/spachava753/laas/vego/internal/logic"
	"github.com/spachava753/laas/vego/internal/solver"
)

// A frame proves that the invariants of a value still hold by showing that
// nothing they read has changed since a point of the path where they held,
// in place of proving their clauses again. Z3 fails to align two readings
// of one quantified formula even where no write came between them, while
// the question whether each value a clause reads is the same in two
// memories is ground once Z3 names the quantifiers' variables. A frame
// states no fact: it only changes how a goal is asked, and when it fails
// the clauses are proved as before. Two invariants carry it.
//
// K: an entry (keptEntry) of a state says that in every execution reaching
// that state along its path, the invariants of a struct type held of a
// value, under the nil guards of the path to it, in the memory the entry
// holds. An entry is made only where those invariants are assumed with no
// condition of evaluation around them, on the path of the state, and a
// state passes its entries on only to the states that continue its path.
//
// F: a clause is resolved through an environment, and every term of it is
// a function of what the environment returns and of bound variables. A
// frame resolves the clause once through a frameEnv, which reads each name
// in the memory of the entry and in the memory of the goal and records that
// the two results are the same; a quantifier's domain is read before its
// variable is bound, so its results are compared for every value of the
// variable, and the body's under the domain. If every recorded pair is
// equal, the clause reads in the goal's memory what it read in the
// entry's, so it holds there too. A method of an environment the frame
// does not pair would let a read go unseen, so frameEnv implements every
// interface the resolver asks of an environment (TestFrameEnvComplete).

// frameMark starts every name a frame makes; see fnVerifier.fresh.
const frameMark = "%frame "

// frameEffort is the resource limit of a frame's question, half of
// the default. A frame that holds is proved in a fraction of it; one that
// does not costs this much before the clauses are proved as before.
const frameEffort = 2_000_000

// keptEntry is a point of a path where the invariants of a struct type
// held of a value: one step of invariantSteps, in a memory of the path.
type keptEntry struct {
	set   *invariantSet
	val   value
	t     types.Type
	guard []*logic.Term
	mem   memory
}

// validFound is what a valid(x) read at the top level of a formula
// stands for: the steps of invariantSteps, in the memory they are read in.
type validFound struct {
	steps []invariantStep
	mem   memory
	// terms holds, for each step and each of its clauses, the conjunct
	// valid(x) is made of.
	terms [][]*logic.Term
}

// frameNamespace is what a frame makes while it is asked: the names, which
// nothing outside it sees, and the regions of an epoch it read first,
// which are made again, the same, when the function reads them.
type frameNamespace struct {
	count        int
	materialized []string
}

// keep records that the invariants of a step hold in mem on the path of
// st; see K above.
func (st *state) keep(step invariantStep, mem memory) {
	st.kept = append(st.kept, &keptEntry{set: step.set, val: step.val, t: step.t, guard: step.guard, mem: maps.Clone(mem)})
}

// keptFor returns the entry a frame for a step is asked from: of the same
// invariants and a value of the same type, one whose value is the same
// term if there is one, and otherwise the latest.
func (st *state) keptFor(step invariantStep) *keptEntry {
	var found *keptEntry
	for i := len(st.kept) - 1; i >= 0; i-- {
		e := st.kept[i]
		if e.set != step.set || !types.Identical(e.t, step.t) {
			continue
		}
		if sameTerms(e.val, step.val) {
			return e
		}
		if found == nil {
			found = e
		}
	}
	return found
}

// sameTerms reports whether two values are the same terms.
func sameTerms(a, b value) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i].String() != b[i].String() {
			return false
		}
	}
	return true
}

// framer is one frame being asked: the state that receives what its reads
// learn, which only its question sees, and the pairs it records, one list
// for the formula's top level and one for each quantifier being read.
type framer struct {
	v       *fnVerifier
	scratch *state
	levels  [][]*logic.Term
	// vars holds the variables of each quantifier being read.
	vars [][]*logic.Term
	// differ is set when some pair is not the same term on both sides.
	differ bool
	// failed is set when the two readings did not go alike, or a form the
	// frame does not pair was read; the frame then does not hold.
	failed bool
}

// pair records that what the goal's memory gives for a name must be what
// the entry's gave.
func (f *framer) pair(now, then *logic.Term) {
	if now.Sort != then.Sort {
		f.failed = true
		return
	}
	if now.String() != then.String() {
		f.differ = true
	}
	same := f.exactly(now, then)
	if same == nil {
		f.failed = true
		return
	}
	// A quantifier over the keys of a map reads its domain, has(m, k),
	// before it binds k, which is then a variable of no level open here:
	// the pair must hold for every k.
	open := map[string]bool{}
	for _, level := range f.vars {
		for _, v := range level {
			open[v.Name] = true
		}
	}
	var loose []*logic.Term
	walkBound(same, func(name string) {
		if !open[name] && !slices.ContainsFunc(loose, func(t *logic.Term) bool { return t.Name == name }) {
			sort, _ := boundSortOk(same, name)
			loose = append(loose, logic.Bound(name, sort))
		}
	})
	for _, b := range loose {
		same = logic.Forall(b, same)
	}
	top := len(f.levels) - 1
	f.levels[top] = append(f.levels[top], same)
}

// exactly states that two results are the same: a pointer by its
// allocation and its position, nil ones too, since a read through it reads
// there; a function or interface value by its reference. It returns nil
// for two results of different shapes.
func (f *framer) exactly(now, then *logic.Term) *logic.Term {
	switch {
	case now.Op == logic.OpPair || then.Op == logic.OpPair:
		if now.Op != then.Op || len(now.Args) != len(then.Args) {
			return nil
		}
		var parts []*logic.Term
		for i := range now.Args {
			parts = append(parts, logic.Eq(now.Args[i], then.Args[i]))
		}
		return logic.And(parts...)
	case now.Op == logic.OpFuncVal || now.Op == logic.OpIfaceVal || then.Op == logic.OpFuncVal || then.Op == logic.OpIfaceVal:
		if now.Op != then.Op {
			return nil
		}
		return logic.Eq(now.Args[0], then.Args[0])
	case now.Sort == logic.Bool:
		return logic.Iff(now, then)
	}
	return f.v.same(now, then)
}

// boundSortOk returns the sort of the bound variable of a name in a term.
func boundSortOk(t *logic.Term, name string) (logic.Sort, bool) {
	if t.Op == logic.OpBound && t.Name == name {
		return t.Sort, true
	}
	for _, arg := range t.Args {
		if sort, ok := boundSortOk(arg, name); ok {
			return sort, true
		}
	}
	return 0, false
}

// closed returns the facts that mention no bound variable left free: a
// fact a read learned under a variable that no quantifier of the frame
// binds is left out, which only weakens the premises.
func closed(facts []*logic.Term) []*logic.Term {
	var kept []*logic.Term
	for _, fact := range facts {
		free := false
		walkBound(fact, func(string) { free = true })
		if !free {
			kept = append(kept, fact)
		}
	}
	return kept
}

// frameEnv reads a clause in two memories at once for a framer: then in
// the entry's, now in the goal's. It returns what then reads, so that the
// clause it builds is the entry's, and records each pair. It embeds
// nothing: every method of every interface the resolver asks of an
// environment is written out here, so that one added later fails to
// build until the frame takes a position on it.
type frameEnv struct {
	f         *framer
	then, now *specEnv
}

var (
	_ logic.Env      = (*frameEnv)(nil)
	_ logic.Applier  = (*frameEnv)(nil)
	_ logic.Gatherer = (*frameEnv)(nil)
)

// alike records the pair of two results, or that the readings went apart.
func (e *frameEnv) alike(then, now *logic.Term, errThen, errNow error) (*logic.Term, error) {
	switch {
	case errThen != nil || errNow != nil:
		if errThen == nil || errNow == nil || errThen.Error() != errNow.Error() {
			e.f.failed = true
		}
		return then, errThen
	case then == nil || now == nil:
		if then != now {
			e.f.failed = true
		}
		return then, nil
	}
	e.f.pair(now, then)
	return then, nil
}

func (e *frameEnv) Path(root string, steps []logic.Step, when logic.When) (*logic.Term, error) {
	then, errThen := e.then.Path(root, steps, when)
	now, errNow := e.now.Path(root, steps, when)
	return e.alike(then, now, errThen, errNow)
}

// Relation pairs fresh, within, and apart like any read. valid inside a
// clause is not paired in this step: the frame does not hold.
func (e *frameEnv) Relation(name string, paths []logic.Path) (*logic.Term, error) {
	if name == "valid" {
		e.f.failed = true
	}
	then, errThen := e.then.Relation(name, paths)
	now, errNow := e.now.Relation(name, paths)
	return e.alike(then, now, errThen, errNow)
}

func (e *frameEnv) Qualified(path, name string, steps []logic.Step, when logic.When) (*logic.Term, error) {
	then, errThen := e.then.Qualified(path, name, steps, when)
	now, errNow := e.now.Qualified(path, name, steps, when)
	return e.alike(then, now, errThen, errNow)
}

func (e *frameEnv) Apply(name string, args []*logic.Term) (*logic.Term, bool, error) {
	then, knownThen, errThen := e.then.Apply(name, args)
	now, knownNow, errNow := e.now.Apply(name, args)
	if knownThen != knownNow {
		e.f.failed = true
	}
	if !knownThen {
		return then, false, errThen
	}
	t, err := e.alike(then, now, errThen, errNow)
	return t, true, err
}

func (e *frameEnv) Applies(name string) bool {
	then := e.then.Applies(name)
	if then != e.now.Applies(name) {
		e.f.failed = true
	}
	return then
}

// OpenBound starts a level of pairs for the quantifier, and the gathering
// of each reading's facts under it.
func (e *frameEnv) OpenBound(vars []*logic.Term) {
	e.f.levels = append(e.f.levels, nil)
	e.f.vars = append(e.f.vars, vars)
	e.then.OpenBound(vars)
	e.now.OpenBound(vars)
}

// CloseBound returns the quantifier's pairs, under what the two readings
// learned of the cells they read there, as the one fact the resolver
// then quantifies over the variables under the domain and hands to Keep.
// The readings are closed in the order opposite to their opening, since
// each saved the gatherer around it.
func (e *frameEnv) CloseBound() []*logic.Term {
	learned := append(e.now.CloseBound(), e.then.CloseBound()...)
	top := len(e.f.levels) - 1
	pairs := e.f.levels[top]
	e.f.levels = e.f.levels[:top]
	e.f.vars = e.f.vars[:len(e.f.vars)-1]
	if len(pairs) == 0 {
		return nil
	}
	return []*logic.Term{logic.Implies(logic.And(learned...), logic.And(pairs...))}
}

// Keep takes a quantifier's pairs, quantified, into the level around it.
func (e *frameEnv) Keep(fact *logic.Term) {
	top := len(e.f.levels) - 1
	e.f.levels[top] = append(e.f.levels[top], fact)
}

// frameAbort stops a frame from inside a read that would report or give
// up: the frame does not hold, and nothing is reported.
type frameAbort struct{}

// asFrame runs a frame in its own namespace: names come from a counter of
// its own and are not recorded as made, what it materializes is dropped
// after, and it fails at once if it would report. Every other table of the
// verifier must be as it was before; a table that grows is a read the
// frame made visible outside it, which is an internal error.
func (v *fnVerifier) asFrame(run func() bool) (held bool) {
	if v.frameNames != nil {
		panic("vego: internal error: a frame is asked inside a frame")
	}
	sizes := tableSizes(v)
	reports := v.reports
	ns := &frameNamespace{}
	v.frameNames = ns
	savedTyped, savedBound := v.typedReads, v.boundSink
	v.typedReads = nil
	defer func() {
		r := recover()
		v.frameNames = nil
		v.typedReads, v.boundSink = savedTyped, savedBound
		for _, name := range ns.materialized {
			delete(v.layers, name)
			delete(v.joins, name)
		}
		switch r.(type) {
		case nil:
		case frameAbort, unsupported, abort, logic.TooLarge:
			held = false
		default:
			panic(r)
		}
		if v.reports != reports {
			panic("vego: internal error: a frame reported something")
		}
		if grown := tableSizes(v); !maps.Equal(sizes, grown) {
			for name, n := range grown {
				if sizes[name] != n {
					panic(fmt.Sprintf("vego: internal error: the table %s of the verifier changed while a frame was asked", name))
				}
			}
		}
	}()
	return run()
}

// tableSizes returns the length of every map and slice the verifier holds,
// by field, those of the frame itself left out.
func tableSizes(v *fnVerifier) map[string]int {
	sizes := map[string]int{}
	rv := reflect.ValueOf(v).Elem()
	for i := range rv.NumField() {
		field := rv.Type().Field(i)
		if field.Name == "frameNames" || field.Name == "pkgVerifier" {
			continue
		}
		switch f := rv.Field(i); f.Kind() {
		case reflect.Map, reflect.Slice:
			sizes[field.Name] = f.Len()
		case reflect.Pointer:
			// A pointer to a slice, as typedReads.
			if !f.IsNil() && f.Elem().Kind() == reflect.Slice {
				sizes[field.Name] = f.Elem().Len()
			}
		}
	}
	return sizes
}

// framedStep reports whether a conjunct of a clause of a step's invariants
// holds in mem because nothing it reads has changed since an entry of the
// path of st (see K and F above). The guard of the goal is the step's.
func (v *fnVerifier) framedStep(st *state, step invariantStep, mem memory, c *clause, node *logic.Node) bool {
	entry := st.keptFor(step)
	if entry == nil {
		return false
	}
	return v.asFrame(func() bool {
		f := &framer{v: v, levels: [][]*logic.Term{nil}}
		f.scratch = &state{vals: map[*types.Var]value{}, mem: st.mem, brk: st.brk, noted: maps.Clone(st.noted)}
		then := v.invariantEnv(entry.set, f.scratch, entry.mem, entry.val, entry.t)
		now := v.invariantEnv(step.set, f.scratch, mem, step.val, step.t)
		then.framed, now.framed = true, true
		res := v.resolverOf(c)
		apart := &logic.Resolver{Preds: res.Preds, Prefix: res.Prefix, Mark: frameMark}
		if _, err := apart.Formula(node, &frameEnv{f: f, then: then, now: now}); err != nil || f.failed || len(f.levels) != 1 {
			return false
		}
		if !f.differ && sameTerms(entry.val, step.val) && guardWithin(entry.guard, step.guard) {
			return true
		}
		// A clause without a quantifier is proved again at little cost;
		// the question of a frame pays only where the clause has one.
		if !quantified(node) {
			return false
		}
		// The goal's guard must give the entry's, the value must be the
		// entry's, and every pair must hold.
		var same []*logic.Term
		for i := range step.val {
			same = append(same, v.same(step.val[i], entry.val[i]))
		}
		goal := logic.Implies(logic.And(step.guard...), logic.And(logic.And(entry.guard...), logic.And(same...), logic.And(f.levels[0]...)))
		goal = logic.Implies(logic.And(closed(f.scratch.hyps)...), goal)
		result := v.solver().Prove(slices.Clip(st.hyps), goal, v.options(frameEffort, frameAttempt))
		return result == solver.Proved
	})
}

// guardWithin reports whether every condition of an entry's guard is one
// of the goal's, as the same term.
func guardWithin(entry, goal []*logic.Term) bool {
	for _, g := range entry {
		if !slices.ContainsFunc(goal, func(h *logic.Term) bool { return h.String() == g.String() }) {
			return false
		}
	}
	return true
}

// checkClauseFramed is checkClause for a goal that a frame may prove: each
// conjunct is resolved as checkClause resolves it, and when a frame holds
// of it, it is assumed as check assumes a goal it proved, with no problem
// of its own asked. framed, when not nil, is asked of every conjunct; a
// conjunct that is valid(x) is asked of the steps of x.
func (v *fnVerifier) checkClauseFramed(c *clause, env logic.Env, st *state, guard []*logic.Term, pos token.Pos, what string, framed func(node *logic.Node) bool) {
	spec, _ := env.(*specEnv)
	for _, node := range c.node.Conjuncts() {
		text := strings.Join(strings.Fields(c.text[node.Start:node.End]), " ")
		var found []validFound
		var goal *logic.Term
		if spec != nil && isValidCall(node) {
			saved := spec.validFound
			spec.validFound = &found
			goal = v.formula(c, node, env)
			spec.validFound = saved
		} else {
			goal = v.formula(c, node, env)
		}
		done := v.at(pos)
		held := framed != nil && framed(node)
		var kept map[string][]*logic.Term
		if !held && len(found) == 1 {
			kept = v.framedValid(st, guard, found[0])
		}
		done()
		for _, conjunct := range logic.Conjuncts(goal) {
			rest, framed := kept[conjunct.String()]
			switch {
			case conjunct.Op == logic.OpTrue:
				continue
			case held:
			case framed:
				// What no frame proved of the clause is proved, and the
				// clause is assumed whole, as check would assume it.
				v.checkOnly(st, guard, logic.And(rest...), false, pos, "%s: %s", what, text)
			default:
				v.check(st, guard, conjunct, pos, "%s: %s", what, text)
				continue
			}
			st.assume(logic.Implies(logic.And(guard...), conjunct))
		}
	}
}

// framedValid returns, for each conjunct of valid(x) of which a frame
// proves every conjunct that has a quantifier, what is left to prove of
// it: the conjuncts of its clause no frame proved, each under its step's
// guard, which have no quantifier and are proved again at little cost. A
// clause is resolved again only for those, in the memory and with the
// sink its whole was read with, so its reads are those already made.
func (v *fnVerifier) framedValid(st *state, guard []*logic.Term, found validFound) map[string][]*logic.Term {
	kept := map[string][]*logic.Term{}
	for i, step := range found.steps {
		if step.set.broken {
			continue
		}
		goalStep := step
		goalStep.guard = append(slices.Clip(guard), step.guard...)
	clauses:
		for j, c := range step.set.clauses {
			var rest []*logic.Term
			for _, node := range c.node.Conjuncts() {
				if v.framedStep(st, goalStep, found.mem, c, node) {
					continue
				}
				if quantified(node) {
					continue clauses
				}
				residue, ok := v.residue(st, step, found.mem, c, node)
				if !ok {
					continue clauses
				}
				rest = append(rest, residue)
			}
			// A clause no frame proved any of is checked as before.
			if len(rest) == len(c.node.Conjuncts()) {
				continue
			}
			for _, conjunct := range logic.Conjuncts(found.terms[i][j]) {
				kept[conjunct.String()] = rest
			}
		}
	}
	return kept
}

// residue resolves a conjunct of a clause of a step that no frame proved,
// to be proved on its own: in the frame's namespace, so that resolving it
// again leaves every other problem as it was, with what its reads learn as
// its premises.
func (v *fnVerifier) residue(st *state, step invariantStep, mem memory, c *clause, node *logic.Node) (*logic.Term, bool) {
	var residue *logic.Term
	held := v.asFrame(func() bool {
		scratch := &state{vals: map[*types.Var]value{}, mem: st.mem, brk: st.brk, noted: maps.Clone(st.noted)}
		env := v.invariantEnv(step.set, scratch, mem, step.val, step.t)
		res := v.resolverOf(c)
		apart := &logic.Resolver{Preds: res.Preds, Prefix: res.Prefix, Mark: frameMark}
		t, err := apart.Formula(node, env)
		if err != nil {
			return false
		}
		residue = logic.Implies(logic.And(closed(scratch.hyps)...), logic.Implies(logic.And(step.guard...), t))
		return true
	})
	return residue, held
}

// isValidCall reports whether a formula is valid(x).
func isValidCall(node *logic.Node) bool {
	return node.Kind == logic.NCall && node.Name == "valid" && len(node.Kids) == 1
}

// keepValid records, for a clause assumed with no condition of evaluation
// around it, where its valid(x) conjuncts hold: the clause is resolved
// with found set, and when every valid(x) in it is a conjunct of its top
// level, each found step is kept. A valid(x) elsewhere in the clause is
// not kept, nor is any of the clause's, which only loses a frame.
func keepValid(st *state, c *clause, found []validFound) {
	all, top := 0, 0
	c.node.Walk(func(n *logic.Node) {
		if isValidCall(n) {
			all++
		}
	})
	for _, node := range c.node.Conjuncts() {
		if isValidCall(node) {
			top++
		}
	}
	if all != top || len(found) != top {
		return
	}
	for _, f := range found {
		for _, step := range f.steps {
			if !step.set.broken {
				st.keep(step, f.mem)
			}
		}
	}
}

// assumeKeeping assumes a clause resolved through env, with no condition
// of evaluation around it, and keeps where its valid(x) conjuncts hold.
func (v *fnVerifier) assumeKeeping(st *state, c *clause, env *specEnv) {
	var found []validFound
	saved := env.validFound
	env.validFound = &found
	st.assume(v.formula(c, c.node, env))
	env.validFound = saved
	keepValid(st, c, found)
}

// quantified reports whether a formula has a quantifier.
func quantified(node *logic.Node) bool {
	found := false
	node.Walk(func(n *logic.Node) {
		if n.Kind == logic.NQuant {
			found = true
		}
	})
	return found
}
