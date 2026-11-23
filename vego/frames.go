package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"maps"
	"math"
	"math/big"
	"reflect"
	"regexp"
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
	// from says where the invariants were assumed, for a message, and
	// logAt how many writes the state had logged then.
	from  string
	logAt int
}

// loggedWrite is a statement after which a state's memory was not what it
// was after the one before: where it is, what it is, and the memory after
// it. A frame that fails asks these in turn to name what may have written
// what the clause reads (explainFrame).
type loggedWrite struct {
	pos  token.Pos
	what string
	mem  memory
}

// logWrite records, after a statement, that memory changed, if it did.
func (st *state) logWrite(pos token.Pos, what string) {
	last := memory{}
	if n := len(st.writes); n > 0 {
		last = st.writes[n-1].mem
	}
	if maps.Equal(last, st.mem) {
		return
	}
	st.writes = append(st.writes, loggedWrite{pos: pos, what: what, mem: maps.Clone(st.mem)})
}

// writeOf says what a statement is, for a message that names a write.
func writeOf(s ast.Stmt) string {
	switch s := s.(type) {
	case *ast.AssignStmt:
		if len(s.Rhs) == 1 {
			if call, ok := ast.Unparen(s.Rhs[0]).(*ast.CallExpr); ok {
				return callOf(call) + " in the assignment to " + types.ExprString(s.Lhs[0])
			}
		}
		return "the assignment to " + types.ExprString(s.Lhs[0])
	case *ast.IncDecStmt:
		return "the assignment to " + types.ExprString(s.X)
	case *ast.ExprStmt:
		if call, ok := ast.Unparen(s.X).(*ast.CallExpr); ok {
			return callOf(call)
		}
	case *ast.ForStmt, *ast.RangeStmt:
		return "the loop"
	case *ast.IfStmt:
		return "the if statement"
	case *ast.SwitchStmt, *ast.TypeSwitchStmt:
		return "the switch statement"
	case *ast.DeclStmt:
		if gen, ok := s.Decl.(*ast.GenDecl); ok && len(gen.Specs) == 1 {
			if spec, ok := gen.Specs[0].(*ast.ValueSpec); ok && len(spec.Values) == 1 {
				if call, ok := ast.Unparen(spec.Values[0]).(*ast.CallExpr); ok {
					return callOf(call) + " in the declaration of " + spec.Names[0].Name
				}
			}
		}
		return "the declaration"
	}
	return "the statement"
}

// callOf names a call for a message.
func callOf(call *ast.CallExpr) string {
	if _, lit := ast.Unparen(call.Fun).(*ast.FuncLit); lit {
		return "the function literal called"
	}
	return "the call to " + types.ExprString(call.Fun)
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
func (st *state) keep(step invariantStep, mem memory, from string) {
	st.kept = append(st.kept, &keptEntry{set: step.set, val: step.val, t: step.t, guard: step.guard, mem: maps.Clone(mem), from: from, logAt: len(st.writes)})
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
	// vars holds the variables of each quantifier being read, and labels
	// the path each pair of a level reads, for a message; closed is the
	// first label of the level a quantifier closed, which its kept pairs
	// take.
	vars   [][]*logic.Term
	labels [][]string
	closed string
	// differs holds, for each level, the label of its first pair whose
	// own tables of memory are not the entry's (tablesOf), and same, for
	// the top level, which of its pairs are the same term.
	differs    []string
	same       []bool
	closedSame bool
	// only, when not negative, keeps of the top level the one pair at that
	// index, for the question that names what changed.
	only int
	// reads maps what a read gave in the entry's memory to how it is
	// spelled, so that an index is spelled by the reads it was made of,
	// and topReads holds, of each read outside every quantifier, each
	// table of memory it read with the reference it read it at.
	reads    map[string]string
	topReads map[string]bool
	// tables holds every table of memory the entry's reading read, and
	// changedTables those the goal's reading does not read.
	tables, changedTables map[string]bool
	// nested counts the clauses validPaired read, each with a resolver of
	// its own, whose names it keeps apart.
	nested int
	// split is set to read a quantifier whose domain may grow
	// (framedLoop): opened and fact record the variables of the
	// quantifier at the top and the one fact CloseBound returned for it.
	split  bool
	opened []*logic.Term
	fact   *logic.Term
	// differ is set when some pair is not the same term on both sides.
	differ bool
	// failed is set when the two readings did not go alike, or a form the
	// frame does not pair was read; the frame then does not hold.
	failed bool
}

// pair records that what the goal's memory gives for a name must be what
// the entry's gave.
func (f *framer) pair(now, then *logic.Term, label string) {
	if now.Sort != then.Sort {
		f.failed = true
		return
	}
	identical := now.String() == then.String()
	if !identical {
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
	f.labels[top] = append(f.labels[top], label)
	if f.reads != nil {
		f.reads[then.String()] = label
	}
	if top == 0 {
		if f.topReads == nil {
			f.topReads = map[string]bool{}
		}
		// Each table of memory the read reads, at the reference it reads
		// it at, as region and reference: has(tasks, k) reads the table of
		// keys at the map, and the field tasks at the struct on the way.
		var walk func(t *logic.Term)
		walk = func(t *logic.Term) {
			if t.Op == logic.OpSelect && len(t.Args) == 2 && t.Args[0].Sort.IsSeq() && t.Args[0].Sort.Elem().IsSeq() {
				f.topReads[t.Args[0].String()+"|"+t.Args[1].String()] = true
			}
			for _, arg := range t.Args {
				walk(arg)
			}
		}
		walk(then)
	}
	// The read that changed is named by the first pair whose own tables
	// of memory are not the entry's: a read whose only difference is an
	// index or a reference read before it inherited the change.
	thenTables, nowTables := tablesOf(then), tablesOf(now)
	if f.tables == nil {
		f.tables, f.changedTables = map[string]bool{}, map[string]bool{}
	}
	for table := range thenTables {
		f.tables[table] = true
		if !nowTables[table] {
			f.changedTables[table] = true
		}
	}
	if !identical && f.differs[top] == "" && !maps.Equal(thenTables, nowTables) {
		f.differs[top] = label
	}
	if top == 0 {
		f.same = append(f.same, identical)
	}
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
func (e *frameEnv) alike(then, now *logic.Term, errThen, errNow error, label string) (*logic.Term, error) {
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
	e.f.pair(now, then, label)
	return then, nil
}

func (e *frameEnv) Path(root string, steps []logic.Step, when logic.When) (*logic.Term, error) {
	then, errThen := e.then.Path(root, steps, when)
	now, errNow := e.now.Path(root, steps, when)
	return e.alike(then, now, errThen, errNow, e.f.spellRead(root, steps))
}

// Relation pairs fresh, within, and apart like any read, and valid(x)
// through what it is made of (validPaired).
func (e *frameEnv) Relation(name string, paths []logic.Path) (*logic.Term, error) {
	if name == "valid" && len(paths) == 1 {
		return e.validPaired(paths[0])
	}
	then, errThen := e.then.Relation(name, paths)
	now, errNow := e.now.Relation(name, paths)
	var spelled []string
	for _, p := range paths {
		spelled = append(spelled, e.f.spellRead(p.Root, p.Steps))
	}
	return e.alike(then, now, errThen, errNow, name+"("+strings.Join(spelled, ", ")+")")
}

// validPaired reads valid(x) in both memories as specEnv.valid does: the
// value x leads to and the steps of invariantSteps are paired, their nil
// guards and values included, and the clauses of each step are read through
// a frameEnv of their own over the same framer, so that their pairs fall
// under the quantifiers around them. Compared as one boolean, valid(x)
// would be the alignment a frame is there to spare Z3. It returns what
// the entry's memory gives.
func (e *frameEnv) validPaired(path logic.Path) (*logic.Term, error) {
	then, errThen := e.then.locateAt(path.Root, path.Steps, path.When, true)
	now, errNow := e.now.locateAt(path.Root, path.Steps, path.When, true)
	label := "valid(" + e.f.spellRead(path.Root, path.Steps) + ")"
	if errThen != nil || errNow != nil || len(then.val) != len(now.val) || then.constant != nil || now.constant != nil {
		e.f.failed = true
		if errThen == nil {
			errThen = fmt.Errorf("%s cannot be read for a frame", label)
		}
		return nil, errThen
	}
	for i := range then.val {
		e.f.pair(now.val[i], then.val[i], label)
	}
	v := e.f.v
	stepsThen := v.invariantSteps(then.sink, then.mem, then.val, then.typ, nil, "", map[types.Type]bool{})
	stepsNow := v.invariantSteps(now.sink, now.mem, now.val, now.typ, nil, "", map[types.Type]bool{})
	if len(stepsThen) == 0 || len(stepsThen) != len(stepsNow) {
		e.f.failed = true
		return nil, fmt.Errorf("%s has no steps to frame", label)
	}
	var conjuncts []*logic.Term
	for i, stepThen := range stepsThen {
		stepNow := stepsNow[i]
		if stepThen.set != stepNow.set || stepThen.set.broken || len(stepThen.val) != len(stepNow.val) || len(stepThen.guard) != len(stepNow.guard) {
			e.f.failed = true
			return nil, fmt.Errorf("%s steps apart", label)
		}
		for j := range stepThen.val {
			e.f.pair(stepNow.val[j], stepThen.val[j], label)
		}
		for j := range stepThen.guard {
			e.f.pair(stepNow.guard[j], stepThen.guard[j], label)
		}
		for _, c := range stepThen.set.clauses {
			nested := &frameEnv{f: e.f,
				then: v.invariantEnv(stepThen.set, then.sink, then.mem, stepThen.val, stepThen.t),
				now:  v.invariantEnv(stepNow.set, now.sink, now.mem, stepNow.val, stepNow.t)}
			e.f.nested++
			res := v.resolverOf(c)
			apart := &logic.Resolver{Preds: res.Preds, Prefix: res.Prefix, Mark: fmt.Sprintf("%s%d ", frameMark, e.f.nested)}
			t, err := apart.Formula(c.node, nested)
			if err != nil {
				e.f.failed = true
				return nil, err
			}
			conjuncts = append(conjuncts, logic.Implies(logic.And(stepThen.guard...), t))
		}
	}
	return logic.And(conjuncts...), nil
}

func (e *frameEnv) Qualified(path, name string, steps []logic.Step, when logic.When) (*logic.Term, error) {
	then, errThen := e.then.Qualified(path, name, steps, when)
	now, errNow := e.now.Qualified(path, name, steps, when)
	return e.alike(then, now, errThen, errNow, e.f.spellRead(name, steps))
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
	t, err := e.alike(then, now, errThen, errNow, name)
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
	if e.f.split && e.f.opened == nil && len(e.f.levels) == 1 {
		e.f.opened = vars
	}
	e.f.levels = append(e.f.levels, nil)
	e.f.labels = append(e.f.labels, nil)
	e.f.differs = append(e.f.differs, "")
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
	e.f.closed = e.f.differs[top]
	closedSame := e.f.closed == ""
	e.f.labels = e.f.labels[:top]
	e.f.differs = e.f.differs[:top]
	e.f.closedSame = closedSame
	if len(pairs) == 0 {
		return nil
	}
	fact := logic.Implies(logic.And(learned...), logic.And(pairs...))
	if e.f.split && len(e.f.levels) == 1 && e.f.fact == nil {
		e.f.fact = fact
	}
	return []*logic.Term{fact}
}

// Keep takes a quantifier's pairs, quantified, into the level around it.
func (e *frameEnv) Keep(fact *logic.Term) {
	top := len(e.f.levels) - 1
	e.f.levels[top] = append(e.f.levels[top], fact)
	e.f.labels[top] = append(e.f.labels[top], e.f.closed)
	if !e.f.closedSame && e.f.differs[top] == "" {
		e.f.differs[top] = e.f.closed
	}
	if top == 0 {
		e.f.same = append(e.f.same, e.f.closedSame)
	}
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
// When it does not hold and an entry was there, why is v.lastFrame's.
func (v *fnVerifier) framedStep(st *state, step invariantStep, mem memory, c *clause, node *logic.Node) bool {
	entry := st.keptFor(step)
	if entry == nil {
		return false
	}
	held := v.frameAnswer(st, entry, step, mem, c, node, frameEffort, frameAttempt, -1).result == solver.Proved
	if !held {
		v.lastFrame = &frameFailure{st: st, entry: entry, step: step, mem: mem, c: c, node: node}
	}
	return held
}

// frameAnswered is what frameAnswer found: Proved when the frame holds,
// Refuted when Z3 showed it does not, and otherwise what stopped the
// question; the labels of the top level and which of its pairs are the
// same term; whether some pair was not the same term on both sides; and
// the label of the first read whose tables changed.
type frameAnswered struct {
	result  solver.Result
	labels  []string
	same    []bool
	differ  bool
	changed string
	// every is set when no table of memory the clause read is the same,
	// as after a write through a footprint, which starts an epoch.
	every bool
}

// frameAnswer asks a frame from an entry: by identity, and otherwise, for
// a clause with a quantifier, as a question at the effort and of the kind
// given. With only not negative, the question keeps of the top level the
// one pair at that index, and the identity is not tried; past the last
// pair, nothing is asked.
func (v *fnVerifier) frameAnswer(st *state, entry *keptEntry, step invariantStep, mem memory, c *clause, node *logic.Node, effort int, kind question, only int) (answer frameAnswered) {
	result := solver.Unknown
	var labels []string
	var same []bool
	defer func() { answer.result, answer.labels, answer.same = result, labels, same }()
	v.asFrame(func() bool {
		f := &framer{v: v, levels: [][]*logic.Term{nil}, labels: [][]string{nil}, differs: []string{""}, only: only, reads: map[string]string{}}
		f.scratch = &state{vals: map[*types.Var]value{}, mem: st.mem, brk: st.brk, noted: maps.Clone(st.noted)}
		then := v.invariantEnv(entry.set, f.scratch, entry.mem, entry.val, entry.t)
		now := v.invariantEnv(step.set, f.scratch, mem, step.val, step.t)
		res := v.resolverOf(c)
		apart := &logic.Resolver{Preds: res.Preds, Prefix: res.Prefix, Mark: frameMark}
		if _, err := apart.Formula(node, &frameEnv{f: f, then: then, now: now}); err != nil || f.failed || len(f.levels) != 1 {
			return false
		}
		labels, same = f.labels[0], f.same
		answer.differ, answer.changed = f.differ, f.differs[0]
		answer.every = len(f.tables) > 1 && len(f.changedTables) == len(f.tables)
		top := f.levels[0]
		if only >= 0 {
			if only >= len(top) {
				return false
			}
			top = top[only : only+1]
		} else if !f.differ && sameTerms(entry.val, step.val) && guardWithin(entry.guard, step.guard) {
			result = solver.Proved
			return true
		}
		if only < 0 && kind == frameAttempt {
			// A clause without a quantifier is proved again at little
			// cost; the question of a frame pays only where the clause
			// has one.
			if !quantified(node) {
				return false
			}
			// A frame cannot hold where a region was written directly, in
			// the memory since the entry, at a reference the clause reads
			// outside every quantifier, as a store method writes its map:
			// the question would only run to its limit (F11 of the review).
			if writtenAt(entry.mem, mem, f.topReads) {
				return false
			}

		}
		// The goal's guard must give the entry's, the value must be the
		// entry's, and every pair must hold.
		var same []*logic.Term
		for i := range step.val {
			same = append(same, v.same(step.val[i], entry.val[i]))
		}
		goal := logic.Implies(logic.And(step.guard...), logic.And(logic.And(entry.guard...), logic.And(same...), logic.And(top...)))
		goal = logic.Implies(logic.And(closed(f.scratch.hyps)...), goal)
		result = v.solver().Prove(slices.Clip(st.hyps), goal, v.options(effort, kind))
		return result == solver.Proved
	})
	return answer
}

// writtenAt reports whether some region of mem was written directly, by a
// store, a write, or a splice of a table, between its term in from and its
// term in mem, at a reference at which a read in reads reads that region:
// reads holds, for each, the region's table in from and the reference. A
// store into a field of the same struct that the clause does not read is
// not one (F15 of the review). A region that a layer or a join made is not
// looked through: what it keeps is for the frame to ask.
func writtenAt(from, mem memory, reads map[string]bool) bool {
	if len(reads) == 0 {
		return false
	}
	for key, now := range mem {
		if key == epochKey {
			continue
		}
		before := from.region(key, now.Sort).String()
		for t := now; t != nil && t.String() != before; {
			switch t.Op {
			case logic.OpStore, logic.OpWrite, logic.OpSpliceAt:
				if t.Args[0].Sort.Elem().IsSeq() && reads[before+"|"+t.Args[1].String()] {
					return true
				}
				t = t.Args[0]
			default:
				t = nil
			}
		}
	}
	return false
}

// frameFailure is a frame that was asked from an entry and did not hold.
type frameFailure struct {
	st    *state
	entry *keptEntry
	step  invariantStep
	mem   memory
	c     *clause
	node  *logic.Node
}

// frameWhyEffort bounds each question that names what changed.
const frameWhyEffort = quickEffort

// explainFrame says why a frame did not hold, for the message of the
// clause it was asked for: from where, which value the clause reads may
// have changed, and which logged statement may have written it.
//
// The statements logged since the entry are taken in order, but those
// after which memory is the entry's or what it was after the one before.
// For each, the clause is read in the entry's memory and in the memory
// after it, at the entry's value, with no question asked: the first after
// which some value the clause reads is no longer the same term as in the
// entry's memory touched what the clause reads. A question at a small
// limit then asks whether the frame still holds there, which a write that
// rewrote a value with itself, or wrote beside it, passes; the search then
// goes on, at most six questions in all. The statement found is named
// with the last read that changed in its memory. Where no statement
// touched what the clause reads, none is named. Nothing here is a proof:
// the sentence says "may".
func (v *fnVerifier) explainFrame(fail *frameFailure) string {
	var writes []loggedWrite
	last := fail.entry.mem
	for _, w := range fail.st.writes[min(fail.entry.logAt, len(fail.st.writes)):] {
		if !maps.Equal(w.mem, last) && !maps.Equal(w.mem, fail.entry.mem) {
			writes = append(writes, w)
			last = w.mem
		}
	}
	// At the entry's value, so that the reading is about the memory
	// alone: the step's value read after a later write is another term.
	at := fail.step
	at.val, at.guard = fail.entry.val, fail.entry.guard
	questions := 0
	before := fail.entry.mem
	for _, w := range writes {
		previous := before
		before = w.mem
		read := v.frameAnswer(fail.st, fail.entry, at, w.mem, fail.c, fail.node, 0, frameWhy, math.MaxInt)
		if !read.differ {
			continue
		}
		if questions < 6 {
			questions++
			if v.frameAnswer(fail.st, fail.entry, at, w.mem, fail.c, fail.node, frameWhyEffort, frameWhy, -1).result == solver.Proved {
				continue
			}
		}
		// The read named is the first whose tables this statement
		// changed: read in the memory before it and after it.
		since := *fail.entry
		since.mem = previous
		// A statement that changed every table the clause reads, as a
		// write through a footprint does, says nothing of which read.
		local := v.frameAnswer(fail.st, &since, at, w.mem, fail.c, fail.node, 0, frameWhy, math.MaxInt)
		changed := local.changed
		if changed == "" {
			changed = read.changed
		}
		// A write through a footprint starts an epoch, after which no
		// read of memory is the term it was; it may lose what lies in the
		// footprint, which no read names (F16 of the review).
		if changed == "" || local.every || w.mem[epochKey] != previous[epochKey] {
			changed = "what it reads"
		}
		return fmt.Sprintf("; it was not kept from %s, since %s may have changed: %s at %s may write it", fail.entry.from, changed, w.what, v.placeOf(w.pos))
	}
	// No logged statement touched what the clause reads: there is nothing
	// to say of why that a user could act on.
	return ""
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
func (v *fnVerifier) checkClauseFramed(c *clause, env logic.Env, st *state, guard []*logic.Term, pos token.Pos, what string, framed func(node *logic.Node, goal *logic.Term) bool) {
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
		v.lastFrame = nil
		held := framed != nil && framed(node, goal)
		failed := v.lastFrame
		var kept map[string][]*logic.Term
		var why map[string]*frameFailure
		if !held && len(found) == 1 {
			kept, why = v.framedValid(st, guard, found[0])
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
				if f := why[conjunct.String()]; f != nil {
					failed = f
				}
				v.explaining = failed
				v.check(st, guard, conjunct, pos, "%s: %s", what, text)
				v.explaining = nil
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
func (v *fnVerifier) framedValid(st *state, guard []*logic.Term, found validFound) (map[string][]*logic.Term, map[string]*frameFailure) {
	kept := map[string][]*logic.Term{}
	why := map[string]*frameFailure{}
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
				v.lastFrame = nil
				if v.framedStep(st, goalStep, found.mem, c, node) {
					continue
				}
				if v.lastFrame != nil {
					for _, conjunct := range logic.Conjuncts(found.terms[i][j]) {
						why[conjunct.String()] = v.lastFrame
					}
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
	return kept, why
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
func keepValid(st *state, c *clause, found []validFound, from string) {
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
				st.keep(step, f.mem, from)
			}
		}
	}
}

// assumeKeeping assumes a clause resolved through env, with no condition
// of evaluation around it, and keeps where its valid(x) conjuncts hold.
func (v *fnVerifier) assumeKeeping(st *state, c *clause, env *specEnv, from string) {
	var found []validFound
	saved := env.validFound
	env.validFound = &found
	st.assume(v.formula(c, c.node, env))
	env.validFound = saved
	keepValid(st, c, found, from)
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

// frameBound is how a bound variable of a frame's resolver is spelled.
var frameBound = regexp.MustCompile(regexp.QuoteMeta(frameMark) + `(?:[0-9]+ )?([A-Za-z_][A-Za-z_0-9]*)#[0-9]+`)

// spellRead spells a read as a formula writes it, for a message: an
// index by the reads it was made of, and never a term of the logic.
func (f *framer) spellRead(root string, steps []logic.Step) string {
	spelled := root
	for _, step := range steps {
		switch {
		case step.Field != "":
			spelled += "." + step.Field
		case step.Len:
			spelled = "|" + spelled + "|"
		case step.Cap:
			spelled = "cap(" + spelled + ")"
		case step.State != "":
			spelled = step.State + "(" + spelled + ")"
		case step.Has && step.Index != nil:
			spelled = "has(" + spelled + ", " + f.spellTerm(step.Index) + ")"
		case step.Nil:
			spelled += " = nil"
		case step.Addr:
			spelled = "&" + spelled
		case step.ElemSize:
			spelled = "elemsize(" + spelled + ")"
		case step.Keys:
			spelled = "the keys of " + spelled
		case step.Index != nil:
			spelled += "[" + f.spellTerm(step.Index) + "]"
		}
	}
	return spelled
}

// spellTerm spells an index: a read by how it was spelled, a variable of a
// quantifier by its name in the formula, a number, and sums and products
// of those; anything else is "...".
func (f *framer) spellTerm(t *logic.Term) string {
	if label, ok := f.reads[t.String()]; ok {
		return label
	}
	switch t.Op {
	case logic.OpBound:
		if m := frameBound.FindStringSubmatch(t.Name); m != nil {
			return m[1]
		}
	case logic.OpIntLit:
		return t.Value().String()
	case logic.OpNeg:
		return "-" + f.spellTerm(t.Args[0])
	case logic.OpAdd:
		if b := t.Args[1]; b.Op == logic.OpNeg {
			return f.spellTerm(t.Args[0]) + " - " + f.spellTerm(b.Args[0])
		}
		if b := t.Args[1]; b.Op == logic.OpIntLit && b.Value().Sign() < 0 {
			return f.spellTerm(t.Args[0]) + " - " + new(big.Int).Neg(b.Value()).String()
		}
		return f.spellTerm(t.Args[0]) + " + " + f.spellTerm(t.Args[1])
	case logic.OpMul:
		return f.spellTerm(t.Args[0]) + " * " + f.spellTerm(t.Args[1])
	}
	return "..."
}

// tablesOf returns the tables of memory a reading reads, the regions as a
// whole, whatever their indexes.
func tablesOf(t *logic.Term) map[string]bool {
	found := map[string]bool{}
	var walk func(t *logic.Term)
	walk = func(t *logic.Term) {
		if t.Sort.IsSeq() && t.Sort.Elem().IsSeq() {
			found[t.String()] = true
			return
		}
		for _, arg := range t.Args {
			walk(arg)
		}
	}
	walk(t)
	return found
}

// loopKept is a head of a loop at which its invariants were assumed: the
// state there, which the paths of its body continue, and where the
// annotations of the loop are read.
type loopKept struct {
	c    *clause
	head *state
	at   token.Pos
}

// framedLoop reports whether a conjunct of a loop invariant holds at the
// end of the body, or wherever it is a goal, because nothing it reads has
// changed since a loop's head where a conjunct of the same text was
// assumed: the loop's own head, or, after a loop nested in its body
// whose invariant repeats it, that loop's. Read in its own scope, a
// conjunct of the same text is the same formula over what its names
// denote there, so pairing what the two readings give is the frame lemma
// as for one clause. goal is the conjunct as st reads it. At most two
// heads are tried, the latest first.
//
// When the conjunct is a Forall over one variable whose domain the body
// changed, as [0, |tasks|) grows by an append, it is asked split: of every
// element of the domain at the end, that it is an element of the domain
// at the head whose reads are as they were there, or that the body holds
// of it at the end. The first case holds of the head's elements by the
// invariant assumed there, so only the new ones are proved. The split
// goal is Forall i : D1(i) -> ((D0(i) And Unch(i)) Or B1(i)), with D1 and
// B1 those of the goal and D0 and Unch read through the frame. It is asked
// at the default limit, since it stands for the goal itself.
func (v *fnVerifier) framedLoop(st *state, at token.Pos, c *clause, node *logic.Node, goal *logic.Term) bool {
	text := node.String()
	tried := 0
	for i := len(st.loops) - 1; i >= 0 && tried < 2; i-- {
		k := st.loops[i]
		if !slices.ContainsFunc(k.c.node.Conjuncts(), func(n *logic.Node) bool { return n.String() == text }) {
			continue
		}
		tried++
		if v.framedFrom(st, k, at, c, node, goal) {
			return true
		}
	}
	return false
}

// framedFrom is framedLoop from one head.
func (v *fnVerifier) framedFrom(end *state, k *loopKept, at token.Pos, c *clause, node *logic.Node, goal *logic.Term) bool {
	head := k.head
	read := func(split bool) (*framer, *logic.Term, bool) {
		f := &framer{v: v, levels: [][]*logic.Term{nil}, labels: [][]string{nil}, differs: []string{""}, only: -1, split: split}
		f.scratch = &state{vals: map[*types.Var]value{}, mem: end.mem, brk: end.brk, noted: maps.Clone(end.noted)}
		then := &specEnv{v: v, sink: f.scratch, st: head, pos: k.at, now: head.mem}
		now := &specEnv{v: v, sink: f.scratch, st: end, pos: at, now: end.mem}
		res := v.resolverOf(c)
		apart := &logic.Resolver{Preds: res.Preds, Prefix: res.Prefix, Mark: frameMark}
		t, err := apart.Formula(node, &frameEnv{f: f, then: then, now: now})
		return f, t, err == nil && !f.failed && len(f.levels) == 1
	}
	return v.asFrame(func() bool {
		f, _, ok := read(false)
		if !ok {
			return false
		}
		if !f.differ {
			return true
		}
		if !quantified(node) {
			return false
		}
		// A Forall over one variable at the top is asked split, which
		// holds where the whole frame would; any other conjunct whole.
		if node.Kind != logic.NQuant || node.Op != "Forall" || len(node.Vars) != 1 || goal.Op != logic.OpForall {
			premises := closed(f.scratch.hyps)
			whole := logic.Implies(logic.And(premises...), logic.And(f.levels[0]...))
			return v.solver().Prove(slices.Clip(end.hyps), whole, v.options(frameEffort, frameAttempt)) == solver.Proved
		}
		f, then, ok := read(true)
		if !ok || f.fact == nil || len(f.opened) != 1 || then.Op != logic.OpForall {
			return false
		}
		bound, inner := goal.Args[0], goal.Args[1]
		thenBound, thenInner := then.Args[0], then.Args[1]
		if inner.Op != logic.OpImplies || thenInner.Op != logic.OpImplies || thenBound.Name != f.opened[0].Name {
			return false
		}
		// D0: the guards of the head's reading but the frame's own fact.
		var domain []*logic.Term
		for _, guard := range logic.Conjuncts(thenInner.Args[0]) {
			if guard != f.fact {
				domain = append(domain, guard)
			}
		}
		rename := map[string]*logic.Term{thenBound.Name: bound}
		kept := logic.Subst(logic.And(logic.And(domain...), f.fact), rename)
		split := logic.Forall(bound, logic.Implies(inner.Args[0], logic.Or(kept, inner.Args[1])))
		// What the top level read is the quantifier's domain, which may
		// differ, and its pairs, which the split asks only of the head's
		// elements.
		asked := logic.Implies(logic.And(closed(f.scratch.hyps)...), split)
		r := v.solver().Prove(slices.Clip(end.hyps), asked, v.options(0, frameAttempt))
		return r == solver.Proved
	})
}
