package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"slices"
	"strings"

	"github.com/spachava753/laas/vego/internal/logic"
	"golang.org/x/tools/go/types/typeutil"
)

// A function value has the contract of its type. A named function type
// declares one in its doc comment, with the Requires, Ensures, and Modifies
// annotations a function has, over the parameters and results its signature
// names:
//
//	// @Requires c != nil
//	// @Modifies c
//	type Option func(c *Config)
//
// A call through a value of such a type is checked like a call of a
// function with that contract. A value of a function type without a
// contract can be held and passed on, but not called. Nothing else is known
// of a value than whether it is nil.
//
// Such a contract is not verified: it describes every value of the type,
// and each value is checked against it where verified code makes it. A
// value that arrives from code that is not verified is taken to meet it.
// So a call through a value is treated, where the two differ, like a call
// of a trusted function: what it promises is checked against what is known
// at the call, nothing is assumed of the invariants of what it hands back,
// and a contract that leaves failure open makes the call a source of
// unpredictable failure.

// addTypeContract records an annotation written in the doc comment of a
// named function type.
func (pv *pkgVerifier) addTypeContract(name *types.TypeName, c *clause) {
	named, isNamed := name.Type().(*types.Named)
	switch {
	case c.kind != "Requires" && c.kind != "Ensures" && c.kind != "Modifies" && c.kind != "Vouches":
		pv.unread = true
		pv.report(c.pos, "%s annotations do not belong on a function type; a function type can only have Requires, Ensures, Modifies, and Vouches annotations", c.kind)
		return
	case !isNamed || name.IsAlias():
		pv.unread = true
		pv.report(c.pos, "a contract can only be declared on a defined function type, not on an alias")
		return
	case named.TypeParams() != nil:
		pv.unread = true
		pv.report(c.pos, "a contract on a function type with type parameters is not supported yet")
		return
	}
	fn := pv.funcTypes[name]
	if fn == nil {
		sig := name.Type().Underlying().(*types.Signature)
		fn = newFuncInfo(types.NewFunc(name.Pos(), pv.pass.Pkg, name.Name(), sig))
		fn.valueOf = name
		pv.funcTypes[name] = fn
	}
	pv.addValueClause(fn, c)
}

// addValueClause records a Requires, Ensures, or Modifies annotation of the
// contract of a function type or of a method of an interface type.
func (pv *pkgVerifier) addValueClause(fn *funcInfo, c *clause) {
	if c.kind == "Vouches" {
		pv.addVouches(fn, c)
		return
	}
	if c.kind == "Modifies" {
		targets, err := logic.ParseTargets(c.text)
		if err != nil {
			pv.report(c.pos, "syntax error in Modifies annotation: %v", err)
			fn.broken = true
			return
		}
		fn.modifies = append(fn.modifies, newModTargets(targets, c)...)
		return
	}
	node, err := logic.ParseFormula(c.text)
	if err != nil {
		pv.report(c.pos, "syntax error in %s annotation: %v", c.kind, err)
		fn.broken = true
		return
	}
	c.node = node
	if c.kind == "Requires" {
		fn.requires = append(fn.requires, c)
	} else {
		fn.ensures = append(fn.ensures, c)
	}
}

// addVouches reads a Vouches annotation of a contract of a type: the error
// results whose errors it vouches for, as vouches does in the trust file.
// The claim is checked of every value that verified code makes of the type,
// and assumed of every other, as the rest of the contract is.
func (pv *pkgVerifier) addVouches(fn *funcInfo, c *clause) {
	fn.vouchClauses = append(fn.vouchClauses, c)
	fail := func(format string, args ...any) {
		pv.report(c.pos, "in Vouches annotation: "+format, args...)
		fn.broken = true
	}
	for item := range strings.SplitSeq(c.text, ",") {
		name := strings.TrimSpace(item)
		index, isResult := fn.resultNames[name]
		switch {
		case !token.IsIdentifier(name):
			fail("%q is not a name; a Vouches annotation lists error results, as in // @Vouches err", name)
		case !isResult:
			fail("%s is not a result of %s", name, fn.obj.Name())
		case !isError(fn.results[index].Type()):
			fail("%s has type %s; a Vouches annotation lists results of type error, whose errors it vouches for", name, fn.results[index].Type())
		case fn.vouches[index]:
			fail("%s is listed twice", name)
		default:
			fn.vouches[index] = true
		}
	}
}

// checkTypeContracts checks the contract of every named function type of
// the package once, whether or not anything uses the type: its results have
// names, its parameters and results have types vego models, every name it
// uses means something, its Requires clauses can be met, and what it
// promises does not contradict itself.
func (pv *pkgVerifier) checkTypeContracts() {
	var contracts []*funcInfo
	for _, fn := range pv.funcTypes {
		contracts = append(contracts, fn)
	}
	for _, fn := range pv.ifaceMethods {
		contracts = append(contracts, fn)
	}
	slices.SortFunc(contracts, func(a, b *funcInfo) int { return int(a.obj.Pos() - b.obj.Pos()) })
	for _, fn := range contracts {
		pv.checkValueContract(fn)
	}
	pv.checkDroppedContracts()
}

// checkValueContract checks the contract of a function type or of a method
// of an interface type: where it is declared for one written in source, and
// where it is first used for one that a trust file gives a type of another
// package, whose faults are then defects of the entry, reported at each use
// as for a trusted function.
func (pv *pkgVerifier) checkValueContract(fn *funcInfo) {
	// The contract is named as the type, or as the interface and the
	// method.
	at, title := fn.obj.Pos(), fn.obj.Name()
	example := fmt.Sprintf("type %s func(...) (n int)", title)
	if fn.methodOf != nil {
		title = methodTitle(fn.methodOf)
		example = fmt.Sprintf("%s(...) (n int)", fn.methodOf.Name())
	}
	entry := fn.trust != nil
	misreading := false
	fault := func(at token.Pos, format string, args ...any) {
		fn.broken = true
		// A contract refused for anything but a clause that cannot be read
		// is used nowhere; see viewOf.
		fn.faulted = fn.faulted || !misreading
		if entry {
			fn.defect(format, args...)
			return
		}
		pv.report(at, format, args...)
	}
	// A Vouches annotation adds to a contract; alone, it would be the
	// whole contract without anyone having written one.
	if !entry && len(fn.vouchClauses) > 0 && len(fn.requires) == 0 && len(fn.ensures) == 0 && len(fn.modifies) == 0 {
		fault(fn.vouchClauses[0].pos, "%s has a Vouches annotation and no other clause; a Vouches annotation adds to a contract, so write one, as in // @Ensures True", title)
	}
	// An entry names unnamed results as a trusted contract does.
	for _, result := range fn.results {
		if !entry && (result.Name() == "" || result.Name() == "_") {
			fault(at, "%s has a contract, so each of its results needs a name, as in %s", title, example)
			break
		}
	}
	for _, variable := range slices.Concat(fn.params, fn.results) {
		if _, ok := layoutOf(variable.Type()); !ok {
			fault(at, "%s has a contract, and its %s has type %s, which is not supported", title, describe(variable), variable.Type())
		}
		if variable.Name() != "" && fn.ambiguous(variable.Name(), false) {
			fault(at, "%s names %s, which means something else in annotations; rename it", title, variable.Name())
		}
	}
	if fn.broken {
		return
	}
	pv.run(fn, func(v *fnVerifier) {
		v.misreadAs = func(c *clause, err error) {
			misreading = true
			defer func() { misreading = false }()
			if entry {
				fault(c.pos, "in its %s %q: %v", c.kind, c.text, err)
				return
			}
			fault(c.pos, "in %s annotation: %v", c.kind, err)
		}
		state := v.enter()
		if v.quickly(state, nil, logic.False()) {
			fault(at, "nothing can satisfy the Requires clauses of %s together with what the types of its parameters guarantee, "+
				"so no value of the type could be called", title)
			return
		}
		v.primedPaths(fn)
		for _, refused := range v.entryOnly(state) {
			fault(refused.clause.pos, "%s", refused.message(title))
		}
		if !entry {
			for _, defect := range fn.defects {
				pv.report(at, "the contract of %s cannot be used: %s", title, defect)
			}
		}
		if _, post, _ := v.contractInstance(state); pv.contradictory(post) {
			fault(at, "the contract of %s contradicts itself, so a call of a value of the type would prove anything", title)
			return
		}
		if !v.canBeMet(state) {
			fault(at, "the Ensures clauses of %s are not proved to be satisfiable for every call that its Requires allow, "+
				"by results and a change of what Modifies lists; a value of the type is taken to meet them, so a call of one could prove something false. "+
				"State in the Requires when some result exists, or weaken the Ensures", title)
		}
	})
}

// canBeMet reports whether, in every state its Requires allow, some outcome
// of a call meets the contract of the function type being checked. A value
// that comes from code that is not verified is taken to meet the contract.
// A contract that cannot be met for some call would make what it promises
// there a fact about the arguments, as 2 * y = x would make x even.
//
// The outcome is built so that Z3 only has to choose numbers: the results,
// the bound of what exists afterwards, and, for each struct or field that
// Modifies lists, a value written there. Slices and maps that Modifies
// lists keep their contents. A contract that can only be met by changing
// those, or by memory the call creates, is reported, which errs towards
// refusing.
func (v *fnVerifier) canBeMet(entry *state) bool {
	fn := v.fn
	st := entry.clone()
	mark, known := len(v.made), len(st.hyps)
	st.brk = v.fresh("brk", logic.Ref)
	st.assume(logic.Le(entry.brk, st.brk))
	// An outcome may make interface values whose footprints hold what it
	// creates, as a call may; the rows of the homes it makes are its
	// choice, and one with an empty row is offered below.
	grown := v.grow(st, entry.brk, nil)
	grown.after = st.brk
	rows := st.mem[footprintRegion]
	// The homes of the footprints that Modifies lists, whose rows an
	// outcome may grow by memory it makes.
	var listedHomes []*logic.Term
	for _, m := range fn.modifies {
		_, t, err := v.locateTarget(fn, m, v.entry, st, memory{})
		if err == nil && t.fp {
			listedHomes = append(listedHomes, t.ref)
		}
		covered := coveredType(fn, m)
		if err == nil && t.row && covered != nil {
			// Each state the value is known to have gets a value that Z3
			// chooses, at the key of its states.
			at := t.ref
			if t.fp {
				at = t.skey
			}
			for _, state := range v.ifaceStatesOf(covered) {
				v.put(st, []cell{stateCell}, at, state.position(), value{v.fresh("out", logic.Bool)})
			}
			continue
		}
		if err != nil || !t.single || covered == nil {
			continue
		}
		pointer := covered
		if object, isPointer := pointee(covered); isPointer {
			covered = object
		}
		v.put(st, t.cells, t.ref, t.lo, v.unknown("out", covered, st))
		// The states of what a pointer of a type with states points to,
		// which the entry covers with the struct, get values that Z3
		// chooses too (S0b of F34).
		if states, ok := v.pointerStatesTarget(t); ok {
			v.notePointerKey(st, value{t.base.ref, t.base.at})
			for _, state := range v.pointerStates(types.NewPointer(covered)) {
				v.put(st, []cell{stateCell}, states.ref, state.position(), value{v.fresh("out", logic.Bool)})
			}
			_ = pointer
		}
	}
	results := make([]value, len(fn.results))
	for i, result := range fn.results {
		results[i] = v.unknown("out", result.Type(), st)
	}
	env := &specEnv{v: v, sink: st, fn: fn, args: v.entry, results: results, now: memory{}, post: st.mem, before: entry.brk}
	var promised []*logic.Term
	var reads []typedRead
	v.typedReads = &reads
	for _, c := range fn.ensures {
		promised = append(promised, v.calleeFormula(c, env))
	}
	v.typedReads = nil
	// Reading the Ensures notes facts, such as the range of a number read
	// from memory on entry. One that mentions nothing the outcome produced
	// is a fact about the entry state, which holds wherever that memory is
	// read; the rest is what the outcome has to meet.
	given := slices.Clip(entry.hyps)
	// A value read from memory that existed on entry is a value of its
	// type there, below the bound on entry; the read notes it with the
	// bound of the outcome, which makes it a goal about the table of
	// homes that the entry may not settle. Its fact with the bound on entry
	// is true of the entry state, and given.
	outcomeMade := map[string]bool{}
	for _, name := range v.made[mark:] {
		outcomeMade[name] = name != st.brk.Name
	}
	for _, read := range reads {
		if !mentionsMade(read.val, outcomeMade) {
			given = append(given, v.wellFormed(read.val, read.t, entry.brk))
		}
	}
	facts := promised
	for _, fact := range st.hyps[known:] {
		if mentionsAny(fact, v.made[mark:]) {
			facts = append(facts, fact)
		} else {
			given = append(given, fact)
		}
	}
	facts, homesChosen, keysChosen := v.chooseHomes(facts, v.made[mark:])
	// A result that holds memory may be memory the outcome makes and adds
	// to a listed footprint, as a header that a response writer makes on
	// the first call (F34 of the review of step 4).
	var made []*logic.Term
	if len(listedHomes) > 0 {
		for i, result := range fn.results {
			if _, isPointer := pointee(result.Type()); (isPointer || isSlice(result.Type()) || isMap(result.Type())) && results[i] != nil && results[i][0].Op == logic.OpConst {
				made = append(made, results[i][0])
			}
		}
	}
	if len(homesChosen) > 0 || len(made) > 0 {
		// Z3 does not find a home and a bound above it for a value by
		// itself, so instances are offered beside the question as it is:
		// new homes at the bound on entry, one after another, with the
		// bound after them; and every home the home of one interface value
		// whose home the entry reads outside a quantifier, with the bound
		// as it was. Each is an instance of the outcome, so a proof of one
		// is a proof that some outcome exists.
		instances := []map[string]*logic.Term{{st.brk.Name: logic.Add(entry.brk, logic.IntLit(int64(len(homesChosen)+len(made))))}}
		// The new homes hold nothing in their footprints, which is what a
		// value that writes nothing behind it, or only what it creates,
		// has: fresh(result) of an interface value asks for it (F2).
		emptyRow := logic.Fill(logic.IntLit(0), logic.Fill(logic.IntLit(0), logic.False()))
		chosenRows := grown.prev
		for i, h := range homesChosen {
			instances[0][h.Name] = logic.Add(entry.brk, logic.IntLit(int64(i)))
			// Its states are new too, at the same new row.
			instances[0][keysChosen[i].Name] = instances[0][h.Name]
			chosenRows = logic.Store(chosenRows, instances[0][h.Name], emptyRow)
		}
		whole := logic.Fill(logic.IntLit(0), logic.True())
		for i, ref := range made {
			instances[0][ref.Name] = logic.Add(entry.brk, logic.IntLit(int64(len(homesChosen)+i)))
			for _, at := range listedHomes {
				chosenRows = logic.Store(chosenRows, at, logic.Store(logic.Select(chosenRows, at), instances[0][ref.Name], whole))
			}
		}
		instances[0][rows.Name] = chosenRows
		for _, at := range freeHomeReads(given, 4) {
			instance := map[string]*logic.Term{st.brk.Name: entry.brk}
			for i, h := range homesChosen {
				instance[h.Name] = home(at)
				instance[keysChosen[i].Name] = skey(at)
			}
			instances = append(instances, instance)
		}
		alternatives := []*logic.Term{logic.And(facts...)}
		for _, instance := range instances {
			memo := map[*logic.Term]*logic.Term{}
			var instantiated []*logic.Term
			for _, fact := range facts {
				instantiated = append(instantiated, substituteConsts(fact, instance, memo))
			}
			alternatives = append(alternatives, logic.And(instantiated...))
		}
		facts = []*logic.Term{logic.Or(alternatives...)}
	}
	return v.proves(given, v.someOutcome(facts, v.made[mark:]), 0)
}

// chooseHomes lets an outcome choose the home of each interface value it
// produces. The homes are one table, which the entry does not constrain at a
// reference it has never seen, so an outcome that returns a new interface
// value chooses its home as it chooses the value. The facts become one
// disjunction over which of the produced references are nil: a nil one is
// the reference 0, and one that is not nil has a home of its own, chosen
// like a result. Z3 then has no equation under the existential to solve.
//
// What this lets the outcome choose is what an outcome of Go can be, for a
// produced reference that the facts use only inside its home or compared
// with 0. Such a reference is one whose number decides nothing, so it can
// be taken to be a new reference, apart from every other. One that a
// formula compares with another interface value, as in r = x, occurs
// elsewhere and keeps the home the table gives it. A new reference is what a
// conversion gives, and the model gives its home no value of its own: a
// converted value may hold memory that is new, or what another value holds,
// so any home from 1 up to the bound afterwards is one that some outcome
// has. An outcome writes produced values into what Modifies lists too, and
// the facts read them back through those writes; such a read is written
// out first as the value written where the place is the one written and
// what was there otherwise, which means the same, so that a read of the
// home of a value the outcome wrote is the home of that value. A produced
// reference that then still occurs anywhere else, as inside a region, keeps
// the home the table gives it.
//
// It also returns the homes it made, in order.
func (v *fnVerifier) chooseHomes(facts []*logic.Term, made []string) ([]*logic.Term, []*logic.Term, []*logic.Term) {
	produced := map[string]bool{}
	for _, name := range made {
		produced[name] = true
	}
	expanded := make([]*logic.Term, len(facts))
	memo := map[*logic.Term]*logic.Term{}
	for i, fact := range facts {
		expanded[i] = liftHomes(readBack(fact, produced, memo), map[*logic.Term]*logic.Term{})
	}
	facts = expanded
	// The produced references whose homes are read, and those that occur
	// elsewhere than in their home or compared with 0.
	var order []*logic.Term
	listed, pinned := map[string]bool{}, map[string]bool{}
	seen := map[*logic.Term]bool{}
	isProduced := func(t *logic.Term) bool { return t.Op == logic.OpConst && produced[t.Name] }
	var collect func(t *logic.Term)
	collect = func(t *logic.Term) {
		if seen[t] {
			return
		}
		seen[t] = true
		switch {
		case isHomeRead(t) && isProduced(t.Args[1]):
			if !listed[t.Args[1].Name] {
				listed[t.Args[1].Name] = true
				order = append(order, t.Args[1])
			}
			return
		case t.Op == logic.OpEq && (isProduced(t.Args[0]) && isZeroRef(t.Args[1]) || isProduced(t.Args[1]) && isZeroRef(t.Args[0])):
			return
		case isProduced(t):
			pinned[t.Name] = true
			return
		}
		for _, arg := range t.Args {
			collect(arg)
		}
	}
	for _, fact := range facts {
		collect(fact)
	}
	order = slices.DeleteFunc(order, func(ref *logic.Term) bool { return pinned[ref.Name] })
	if len(order) == 0 {
		return facts, nil, nil
	}
	// Each produced value gets a home and a key of its states of its own,
	// two constants, so that an instance can give it what another value
	// has of each (S0b of F34).
	chosen, chosenKeys := map[string]*logic.Term{}, map[string]*logic.Term{}
	var homesMade, keysMade []*logic.Term
	for _, ref := range order {
		chosen[ref.Name] = v.fresh("outhome", logic.Ref)
		chosenKeys[ref.Name] = v.fresh("outkey", logic.Ref)
		homesMade = append(homesMade, chosen[ref.Name])
		keysMade = append(keysMade, chosenKeys[ref.Name])
	}
	zero := logic.RefLit(0)
	// Each subset of the produced references is a choice of which are nil.
	// Beyond three, only all and none are tried, which can only refuse more.
	var subsets [][]bool
	if len(order) <= 3 {
		for mask := 0; mask < 1<<len(order); mask++ {
			nils := make([]bool, len(order))
			for i := range order {
				nils[i] = mask&(1<<i) != 0
			}
			subsets = append(subsets, nils)
		}
	} else {
		none, all := make([]bool, len(order)), make([]bool, len(order))
		for i := range all {
			all[i] = true
		}
		subsets = [][]bool{none, all}
	}
	var cases []*logic.Term
	for _, nils := range subsets {
		asZero, asHome, asKey := map[string]*logic.Term{}, map[string]*logic.Term{}, map[string]*logic.Term{}
		var conditions []*logic.Term
		for i, ref := range order {
			if nils[i] {
				asZero[ref.Name] = zero
				continue
			}
			asHome[ref.Name], asKey[ref.Name] = chosen[ref.Name], chosenKeys[ref.Name]
			conditions = append(conditions, logic.Ne(ref, zero))
		}
		homeMemo, zeroMemo := map[*logic.Term]*logic.Term{}, map[*logic.Term]*logic.Term{}
		for _, fact := range facts {
			conditions = append(conditions, substituteConsts(replaceHomes(fact, asHome, asKey, homeMemo), asZero, zeroMemo))
		}
		cases = append(cases, logic.And(conditions...))
	}
	return []*logic.Term{logic.Or(cases...)}, homesMade, keysMade
}

// freeHomeReads returns up to limit references, in the order met, whose
// homes the facts read outside any quantifier.
func freeHomeReads(facts []*logic.Term, limit int) []*logic.Term {
	var found []*logic.Term
	listed := map[string]bool{}
	seen := map[*logic.Term]bool{}
	var collect func(t *logic.Term)
	collect = func(t *logic.Term) {
		if seen[t] || len(found) >= limit || t.Op == logic.OpForall || t.Op == logic.OpExists {
			return
		}
		seen[t] = true
		if _, read := isKeyRead(t); read {
			if key := t.Args[1].String(); !listed[key] {
				listed[key] = true
				found = append(found, t.Args[1])
			}
		}
		for _, arg := range t.Args {
			collect(arg)
		}
	}
	for _, fact := range facts {
		collect(fact)
	}
	return found
}

// isHomeRead reports whether a term reads the table of homes, or that of
// the keys of states: a produced value is given one new row, its home and
// the key of its states alike (S0b of F34).
func isHomeRead(t *logic.Term) bool {
	_, read := isKeyRead(t)
	return read
}

// isZeroRef reports whether a term is the reference 0.
func isZeroRef(t *logic.Term) bool {
	return t.Op == logic.OpIntLit && t.Sort == logic.Ref && t.Val == 0
}

// readBack writes out each read of a cell through a write whose value is a
// produced constant as that value where the cell is the one written, and
// the read beneath otherwise. A read and a write of the same reference and
// position, the same terms, give the value.
func readBack(t *logic.Term, produced map[string]bool, memo map[*logic.Term]*logic.Term) *logic.Term {
	if done, ok := memo[t]; ok {
		return done
	}
	result := t
	if len(t.Args) > 0 {
		args := make([]*logic.Term, len(t.Args))
		changed := false
		for i, arg := range t.Args {
			args[i] = readBack(arg, produced, memo)
			changed = changed || args[i] != arg
		}
		if changed {
			result = logic.WithArgs(t, args)
		}
	}
	// A cell is read as Select(Select(region, ref), at).
	if result.Op == logic.OpSelect && result.Args[0].Op == logic.OpSelect {
		result = readCell(result.Args[0].Args[0], result.Args[0].Args[1], result.Args[1], produced, result)
	}
	memo[t] = result
	return result
}

// readCell reads the cell at ref and at of a region, through the writes of
// produced constants on top of it; plain is the read as it stands.
func readCell(region, ref, at *logic.Term, produced map[string]bool, plain *logic.Term) *logic.Term {
	if region.Op != logic.OpWrite {
		return plain
	}
	written := region.Args[3]
	if written.Op != logic.OpConst || !produced[written.Name] {
		return plain
	}
	beneath := readCell(region.Args[0], ref, at, produced, logic.Select(logic.Select(region.Args[0], ref), at))
	var same []*logic.Term
	if !sameTerm(ref, region.Args[1]) {
		same = append(same, logic.Eq(ref, region.Args[1]))
	}
	if !sameTerm(at, region.Args[2]) {
		same = append(same, logic.Eq(at, region.Args[2]))
	}
	if len(same) == 0 {
		return written
	}
	return logic.Ite(logic.And(same...), written, beneath)
}

// sameTerm reports whether two terms are written the same.
func sameTerm(a, b *logic.Term) bool {
	return a == b || a.String() == b.String()
}

// liftHomes moves a choice out of a read of a home and out of a comparison
// of references, so that a produced reference read back from memory stands
// inside its home, or compared with 0, as it does when it is a result.
func liftHomes(t *logic.Term, memo map[*logic.Term]*logic.Term) *logic.Term {
	if done, ok := memo[t]; ok {
		return done
	}
	result := t
	if len(t.Args) > 0 {
		args := make([]*logic.Term, len(t.Args))
		changed := false
		for i, arg := range t.Args {
			args[i] = liftHomes(arg, memo)
			changed = changed || args[i] != arg
		}
		if changed {
			result = logic.WithArgs(t, args)
		}
	}
	switch {
	case isHomeRead(result) && result.Args[1].Op == logic.OpIte:
		choice := result.Args[1]
		table := result.Args[0]
		result = logic.Ite(choice.Args[0], liftHomes(logic.Select(table, choice.Args[1]), memo), liftHomes(logic.Select(table, choice.Args[2]), memo))
	case result.Op == logic.OpEq && result.Args[0].Sort == logic.Ref && result.Args[0].Op == logic.OpIte:
		choice := result.Args[0]
		result = logic.Ite(choice.Args[0], liftHomes(logic.Eq(choice.Args[1], result.Args[1]), memo), liftHomes(logic.Eq(choice.Args[2], result.Args[1]), memo))
	case result.Op == logic.OpEq && result.Args[1].Sort == logic.Ref && result.Args[1].Op == logic.OpIte:
		choice := result.Args[1]
		result = logic.Ite(choice.Args[0], liftHomes(logic.Eq(result.Args[0], choice.Args[1]), memo), liftHomes(logic.Eq(result.Args[0], choice.Args[2]), memo))
	}
	memo[t] = result
	return result
}

// replaceHomes replaces the home of each reference that by names with the
// constant given for it, and the key of its states with the one keys
// gives.
func replaceHomes(t *logic.Term, by, keys map[string]*logic.Term, memo map[*logic.Term]*logic.Term) *logic.Term {
	if done, ok := memo[t]; ok {
		return done
	}
	result := t
	switch {
	case isHomeRead(t) && t.Args[1].Op == logic.OpConst && t.Args[0].Name == skeys.Name && keys[t.Args[1].Name] != nil:
		result = keys[t.Args[1].Name]
	case isHomeRead(t) && t.Args[1].Op == logic.OpConst && t.Args[0].Name == keyedByHeld.Name && keys[t.Args[1].Name] != nil:
		// A produced value with states has the states of what it holds,
		// as every such value has.
		result = logic.True()
	case isHomeRead(t) && t.Args[1].Op == logic.OpConst && t.Args[0].Name == homes.Name && by[t.Args[1].Name] != nil:
		result = by[t.Args[1].Name]
	case len(t.Args) > 0:
		args := make([]*logic.Term, len(t.Args))
		changed := false
		for i, arg := range t.Args {
			args[i] = replaceHomes(arg, by, keys, memo)
			changed = changed || args[i] != arg
		}
		if changed {
			result = logic.WithArgs(t, args)
		}
	}
	memo[t] = result
	return result
}

// mentionsMade reports whether a value mentions a constant that the set
// marks.
func mentionsMade(val value, set map[string]bool) bool {
	for _, leaf := range val {
		if _, mentioned := estranged(leaf, set); mentioned {
			return true
		}
	}
	return false
}

// mentionsAny reports whether a term mentions a constant of the given names.
func mentionsAny(t *logic.Term, names []string) bool {
	set := map[string]bool{}
	for _, name := range names {
		set[name] = true
	}
	_, mentioned := estranged(t, set)
	return mentioned
}

// someOutcome states that some outcome of a call has the facts given: the
// constants that stand for what the call produced, among made, are bound
// by an existential quantifier.
func (v *fnVerifier) someOutcome(facts []*logic.Term, made []string) *logic.Term {
	produced := map[string]bool{}
	for _, name := range made {
		produced[name] = true
	}
	sorts := map[string]logic.Sort{}
	var order []string
	var collect func(t *logic.Term)
	seen := map[*logic.Term]bool{}
	collect = func(t *logic.Term) {
		if seen[t] {
			return
		}
		seen[t] = true
		if t.Op == logic.OpConst && produced[t.Name] {
			if _, known := sorts[t.Name]; !known {
				order = append(order, t.Name)
			}
			sorts[t.Name] = t.Sort
		}
		for _, arg := range t.Args {
			collect(arg)
		}
	}
	body := logic.And(facts...)
	collect(body)
	bound := map[string]*logic.Term{}
	for _, name := range order {
		bound[name] = v.bound("out")
		bound[name] = logic.Bound(bound[name].Name, sorts[name])
	}
	body = substituteConsts(body, bound, map[*logic.Term]*logic.Term{})
	for _, name := range slices.Backward(order) {
		body = logic.Exists(bound[name], body)
	}
	return body
}

// substituteConsts replaces constants by the terms given for their names.
func substituteConsts(t *logic.Term, by map[string]*logic.Term, memo map[*logic.Term]*logic.Term) *logic.Term {
	if done, ok := memo[t]; ok {
		return done
	}
	result := t
	switch {
	case t.Op == logic.OpConst && by[t.Name] != nil:
		result = by[t.Name]
	case len(t.Args) > 0:
		args := make([]*logic.Term, len(t.Args))
		changed := false
		for i, arg := range t.Args {
			args[i] = substituteConsts(arg, by, memo)
			changed = changed || args[i] != arg
		}
		if changed {
			result = logic.WithArgs(t, args)
		}
	}
	memo[t] = result
	return result
}

// exportTypeContracts publishes the contracts of the function types of the
// package and of the methods of its interface types. A value of an
// unexported type can reach another package too.
func (pv *pkgVerifier) exportTypeContracts() {
	for name, fn := range pv.funcTypes {
		if name.Parent() != pv.pass.Pkg.Scope() {
			continue
		}
		fact := pv.contractFactOf(fn, name.Pos())
		fact.Verified = !fn.broken && !pv.unread && !pv.predicatesBroken
		pv.pass.ExportObjectFact(name, fact)
	}
	// A method of an interface type has a contract only when the type is
	// declared at package level.
	for method, fn := range pv.ifaceMethods {
		fact := pv.contractFactOf(fn, method.Pos())
		fact.Verified = !fn.broken && !pv.unread && !pv.predicatesBroken
		pv.pass.ExportObjectFact(method, fact)
	}
}

// vouchingContract names the contract of a type that vouches for errors, in
// a message: the trusted contract by its key, or the contract in source by
// the type, or the interface and the method.
func vouchingContract(T *funcInfo) string {
	switch {
	case T.trust != nil:
		return "the trusted contract of " + T.trust.key
	case T.methodOf != nil:
		return "the contract of " + methodTitle(T.methodOf)
	}
	return "the contract of " + T.obj.Name()
}

// valueContract returns the contract that a call through a value of a type
// is checked against, or nil if the type has none.
func (pv *pkgVerifier) valueContract(t types.Type) *funcInfo {
	named, ok := types.Unalias(t).(*types.Named)
	if !ok || !isFunc(t) {
		return nil
	}
	name := named.Origin().Obj()
	if name.Pkg() == pv.pass.Pkg {
		if fn := pv.funcTypes[name]; fn != nil {
			return fn
		}
		return pv.entryFuncType(name)
	}
	if fn, done := pv.importedTypes[name]; done {
		return fn
	}
	pv.importedTypes[name] = nil
	fact := &contractFact{}
	if name.Pkg() == nil || !pv.pass.ImportObjectFact(name, fact) {
		fn := pv.entryFuncType(name)
		pv.importedTypes[name] = fn
		return fn
	}
	sig := name.Type().Underlying().(*types.Signature)
	fn := pv.contractFromFact(types.NewFunc(name.Pos(), name.Pkg(), name.Name(), sig), name.Pkg(), fact)
	if !fact.Verified {
		fn.defects = []string{fmt.Sprintf("the annotations of package %s were not all read", name.Pkg().Path())}
	}
	if pv.entryFor(funcTypeKey(name)) != nil {
		fn.defect("it has a contract where it is declared and also an entry %s in the trust file", funcTypeKey(name))
	}
	fn.valueOf = name
	pv.importedTypes[name] = fn
	return fn
}

// usableValueContract returns the contract of the type of a function value
// that is called, or stops the verification when there is none or it cannot
// be used.
func (v *fnVerifier) usableValueContract(fun ast.Expr, st *state, guard []*logic.Term) *funcInfo {
	t := v.info.TypeOf(fun)
	fn := v.valueContract(t)
	if fn == nil {
		v.unsupported(fun.Pos(), fmt.Sprintf("%s has type %s, which has no contract; "+
			"declare a named function type with a contract and use it here%s", types.ExprString(fun), t, v.funcTypeHint(t)))
	}
	return v.usable(fun.Pos(), fn, fn.obj.Name(), st, guard, true)
}

// callValue verifies a call through a function value. The value and the
// arguments are evaluated before the call, which is an event of the unit
// like any call; then the value must not be nil, and the contract of its
// type applies.
func (v *fnVerifier) callValue(call *ast.CallExpr, st *state, guard []*logic.Term) []value {
	fn := v.usableValueContract(call.Fun, st, guard)
	u := v.unit
	operands := u.pushCeiling()
	fun, args := v.valueOperands(call, fn, st, guard)
	u.reach(operands)
	name := types.ExprString(call.Fun)
	v.check(st, guard, logic.Ne(fun[0], logic.RefLit(0)), call.Pos(), "the function value %s may be nil", name)
	results := v.invoke(call, fn, args, st, guard)
	u.calls = append(u.calls, unitCall{name: name, pos: call.Pos(), pure: v.callMemoryFree(fn, fn.obj.Type().(*types.Signature))})
	u.event()
	return results
}

// valueOperands evaluates the function value of a call and its arguments,
// and refuses an argument that carries code nobody has seen.
func (v *fnVerifier) valueOperands(call *ast.CallExpr, fn *funcInfo, st *state, guard []*logic.Term) (value, map[*types.Var]value) {
	bound := v.bindParams(call, fn)
	fun := v.eval(call.Fun, st, guard)
	args := map[*types.Var]value{}
	for _, passed := range bound {
		args[passed.param] = v.evalPassed(passed, st, guard)
	}
	v.checkHandedToValue(call, fn, "the function value "+types.ExprString(call.Fun))
	return fun, args
}

// deferValue executes the defer of a call through a function value: the
// value and the arguments are settled now, and the call runs when the frame
// returns. A nil value would panic then; it is reported here, where the
// value is fixed.
func (v *fnVerifier) deferValue(s *ast.DeferStmt, st *state) {
	fn := v.usableValueContract(s.Call.Fun, st, nil)
	var fun value
	var args map[*types.Var]value
	v.evaluate(st, func() {
		defer v.begin()()
		fun, args = v.valueOperands(s.Call, fn, st, nil)
	})
	v.check(st, nil, logic.Ne(fun[0], logic.RefLit(0)), s.Call.Pos(), "the function value %s may be nil", types.ExprString(s.Call.Fun))
	st.deferred = append(slices.Clip(st.deferred), deferredCall{call: s.Call, fn: fn, args: args})
}

// checkHandedToValue refuses an argument of a call through a function value
// that carries code nobody has seen. The value may come from code that is
// not verified, which could run that code, and its contract would then not
// say what the call does: an error of unknown origin, whose methods could
// write memory, a function value whose type has no contract, or anything
// else that can hold an interface. A function value of a type with a
// contract and an error of known origin carry no such code.
func (v *fnVerifier) checkHandedToValue(call *ast.CallExpr, fn *funcInfo, callee string) {
	type handed struct {
		arg ast.Expr
		t   types.Type
	}
	var given []handed
	for _, passed := range v.bindParams(call, fn) {
		if !passed.packed {
			given = append(given, handed{passed.expr, passed.param.Type()})
			continue
		}
		// Each argument of a pack is an element of a new slice.
		for _, arg := range passed.pack {
			given = append(given, handed{arg, elemType(passed.param.Type())})
		}
	}
	for _, h := range given {
		arg, t := h.arg, h.t
		v.noteEntriesIn(t, arg.Pos())
		if isError(t) {
			if v.knownError(v.bodyOrigins(), arg, -1) {
				continue
			}
			v.unsupported(arg.Pos(), fmt.Sprintf("%s is passed to %s and is an error whose origin is not known%s; "+
				"the value may come from code that is not verified, which could run code through it that nobody has seen",
				types.ExprString(arg), callee, v.originWhy(arg)))
		}
		if what := v.foreignCode(t, map[types.Type]bool{}); what != "" {
			v.unsupported(arg.Pos(), fmt.Sprintf("%s is passed to %s and is a value of type %s, which can hold %s; "+
				"the value may come from code that is not verified, which could run code through it that nobody has seen",
				types.ExprString(arg), callee, t, what))
		}
	}
}

// foreignCode says what code a value of a type can hold, however deep, that
// nothing describes: an interface, a function value whose type has no
// contract, or a channel through which either may arrive. It returns ""
// when there is none.
func (pv *pkgVerifier) foreignCode(t types.Type, seen map[types.Type]bool) string {
	if t == nil || seen[t] {
		return ""
	}
	seen[t] = true
	if held, replaced := heldAs(t); replaced {
		return pv.foreignCode(held, seen)
	}
	switch u := t.Underlying().(type) {
	case *types.Interface:
		// Every method of an interface with a contract on each is code
		// that meets its contract.
		if pv.fullyContracted(t) {
			return ""
		}
		if isIface(t) && u.NumMethods() > 0 {
			for method := range u.Methods() {
				if fn := pv.methodContract(method); fn != nil && fn.broken {
					return "an interface value with a method whose contract cannot be used"
				}
			}
			return "an interface value with a method that has no contract"
		}
		return "an error, or another interface"
	case *types.Chan:
		return "a channel"
	case *types.Basic:
		if u.Kind() == types.UnsafePointer {
			return "an unsafe.Pointer"
		}
	case *types.Signature:
		if pv.valueContract(t) == nil {
			return "a function value whose type has no contract"
		}
	case *types.Pointer:
		return pv.foreignCode(u.Elem(), seen)
	case *types.Slice:
		return pv.foreignCode(u.Elem(), seen)
	case *types.Array:
		return pv.foreignCode(u.Elem(), seen)
	case *types.Map:
		if what := pv.foreignCode(u.Key(), seen); what != "" {
			return what
		}
		return pv.foreignCode(u.Elem(), seen)
	case *types.Struct:
		for field := range u.Fields() {
			if what := pv.foreignCode(field.Type(), seen); what != "" {
				return what
			}
		}
	}
	return ""
}

// holdsContractedValue reports whether a value of a type can hold, however
// deep, through pointers, slices, and maps, a function value of a type with
// a contract, or an interface value with a method that has one.
func (pv *pkgVerifier) holdsContractedValue(t types.Type, seen map[types.Type]bool) bool {
	if t == nil || seen[t] {
		return false
	}
	seen[t] = true
	if held, replaced := heldAs(t); replaced {
		return pv.holdsContractedValue(held, seen)
	}
	switch u := t.Underlying().(type) {
	case *types.Signature:
		return pv.valueContract(t) != nil
	case *types.Interface:
		// Verified code can call a method that has a contract, and only
		// such a method. Until type assertions are built, nothing else
		// that an interface holds can reach it: an interface without
		// contracts, any, and errors are left out, and must be counted
		// once they are.
		if !isIface(t) {
			return false
		}
		for method := range u.Methods() {
			if pv.methodContract(method) != nil {
				return true
			}
		}
		return false
	case *types.Pointer:
		return pv.holdsContractedValue(u.Elem(), seen)
	case *types.Slice:
		return pv.holdsContractedValue(u.Elem(), seen)
	case *types.Array:
		return pv.holdsContractedValue(u.Elem(), seen)
	case *types.Map:
		return pv.holdsContractedValue(u.Key(), seen) || pv.holdsContractedValue(u.Elem(), seen)
	case *types.Struct:
		for field := range u.Fields() {
			if pv.holdsContractedValue(field.Type(), seen) {
				return true
			}
		}
	}
	return false
}

// holdsCallable reports whether a value of a type can hold, however deep, a
// function value of any type, or an interface value that verified code can
// make: one of an interface whose methods all have contracts, none of
// which speaks of a state (see makeable). For those,
// runs claims only that the contract holds for values that meet their
// contracts, which a cycle back through code that verified code made would
// make circular. Verified code makes no value of an interface with a method
// that has no contract: a conversion to one is refused, and a conversion
// between interfaces keeps the methods of the value. So no such value holds
// code that verified code made, and nothing is circular; for it, as for an
// interface without contracts, any, and an error, runs claims that the
// contract holds whatever code arrives, and a cycle would make that claim
// false, which is on the author of the entry. Until type assertions are
// built, verified code also makes no value that such an interface holds and
// that it could call; they must be counted once it does.
func holdsCallable(pv *pkgVerifier, t types.Type, seen map[types.Type]bool) bool {
	if t == nil || seen[t] {
		return false
	}
	seen[t] = true
	if held, replaced := heldAs(t); replaced {
		return holdsCallable(pv, held, seen)
	}
	switch u := t.Underlying().(type) {
	case *types.Signature:
		return true
	case *types.Basic:
		// An unsafe.Pointer may point to a function value or to an
		// interface value that verified code made.
		return u.Kind() == types.UnsafePointer
	case *types.Interface:
		// An error may hold a value verified code converted, whose methods
		// are verified code (F33, O4 of the design review).
		return pv.fullyContracted(t) || isError(t)
	case *types.Pointer:
		return holdsCallable(pv, u.Elem(), seen)
	case *types.Slice:
		return holdsCallable(pv, u.Elem(), seen)
	case *types.Array:
		return holdsCallable(pv, u.Elem(), seen)
	case *types.Map:
		return holdsCallable(pv, u.Key(), seen) || holdsCallable(pv, u.Elem(), seen)
	case *types.Struct:
		for field := range u.Fields() {
			if holdsCallable(pv, field.Type(), seen) {
				return true
			}
		}
	}
	return false
}

// mayCallValues reports whether running a function may make a call through
// a function value, in its own body or in what it calls. A function whose
// body is in this package is judged by its body: a call that has no static
// callee, a range over a function, and a call of a function that may. One
// verified in another package says so in its contract. A trusted function
// may when its contract lists, under runs, a parameter that can hold a
// function value. A function without a contract or a body may.
func (pv *pkgVerifier) mayCallValues(obj *types.Func) bool {
	// A method of an interface runs whatever the value holds. errors.New
	// makes an error of the string it is given and calls nothing. fmt.Errorf
	// formats its operands, which runs the methods of errors of known
	// origin, which are the standard library's or vouched for and so return
	// and write nothing, and the String and Error methods that the rule for
	// formatting admits, which are calls of the function that formats; see
	// formattedMethods.
	switch {
	case isIfaceMethod(obj):
		return true
	case errorConstructor(obj):
		return false
	}
	if pv.mayCall == nil {
		pv.mayCall = map[*types.Func]bool{}
		pv.valueReasons = map[*types.Func]valueReason{}
		pv.findValueCallers()
	}
	origin := pv.originOf(obj)
	if may, known := byFuncOK(pv.mayCall, origin); known {
		return may
	}
	may := true
	switch fn := pv.contractOf(origin); {
	case isGeneric(origin):
		// Of a generic function only the entry can be read; its
		// parameters of a type parameter's type hold no code.
		if entry := pv.entryFor(origin.FullName()); entry != nil {
			may = genericRunsValues(entry)
		}
	case fn == nil:
	case fn.imported != nil:
		may = fn.imported.CallsValues
	case fn.trust != nil:
		may = pv.runsValues(fn)
	}
	pv.mayCall[origin] = may
	return may
}

// mayCallValuesAtCall is mayCallValues for a function called where the
// call can be seen: what a trusted function of another package may run of
// what a call gives it is judged at the call, by heldCallWhy, and not by
// what its entry lists under runs.
func (pv *pkgVerifier) mayCallValuesAtCall(callee *types.Func) bool {
	if origin := pv.originOf(callee); callee.Pkg() != pv.pass.Pkg {
		if fn := pv.contractOf(origin); fn != nil && fn.trust != nil {
			return false
		}
		if isGeneric(origin) && pv.entryFor(origin.FullName()) != nil {
			return false
		}
	}
	return pv.mayCallValues(callee)
}

// heldCallWhy says why a call into another package may run code that it
// gives that code, as the edges the call graph gives the call; "" when it
// may run none of this package.
func (pv *pkgVerifier) heldCallWhy(call *ast.CallExpr) string {
	callee := typeutil.StaticCallee(pv.info, call)
	if callee == nil || callee.Pkg() == pv.pass.Pkg {
		return ""
	}
	sites := pv.callGraph().sites[call]
	if len(sites) == 0 {
		return ""
	}
	e := sites[0]
	return fmt.Sprintf("%s, which may run %s", e.text, pv.nodeName(e.to))
}

// runsValues reports whether a trusted function may call a function value,
// or a method of an interface value with a contract, that it is given: one
// held, at any depth, by a parameter listed under runs, other than a
// function parameter with a contract under calls. What is handed over
// there is judged where it is handed over. See holdsCallable.
func (pv *pkgVerifier) runsValues(fn *funcInfo) bool {
	for param := range fn.runs.all() {
		if fn.calls.get(param) == nil && holdsCallable(pv, param.Type(), map[types.Type]bool{}) {
			return true
		}
	}
	return false
}

// findValueCallers decides mayCallValues for every function of the package
// that has a body, as the least set closed under calls: a function is in it
// when its body makes a call through a function value, or calls a function
// that is in it. A trusted function of the package is judged by its body
// too, which is there to read, as well as by its contract: one whose body
// calls a function value kept in a variable makes such a call whatever its
// runs says.
func (pv *pkgVerifier) findValueCallers() {
	calls := map[*types.Func][]*types.Func{}
	// local holds the functions judged by their bodies here. It is kept
	// apart from mayCall, which also caches what other functions are
	// judged to do as they are asked about.
	local := map[*types.Func]bool{}
	var pending []*types.Func
	for _, fn := range pv.order {
		if fn.decl.Body == nil {
			continue
		}
		local[fn.obj] = true
		direct, why := false, ""
		because := func(text string) {
			if !direct {
				why = text
			}
			direct = true
		}
		var trusted *funcInfo
		switch entry := pv.entryFor(fn.obj.FullName()); {
		case isGeneric(fn.obj):
			// Of a generic function only the entry can be read.
			if entry != nil && genericRunsValues(entry) {
				because("is trusted and runs what a parameter its runs lists without a contract under calls holds")
			}
		default:
			trusted = pv.trustedContract(fn.obj)
			if trusted != nil && pv.runsValues(trusted) {
				because(pv.runsReason(trusted))
			}
		}
		bound, _ := literalUses(pv.info, fn.decl.Body)
		ast.Inspect(fn.decl.Body, func(n ast.Node) bool {
			switch n := n.(type) {
			case *ast.RangeStmt:
				if rangesByCalling(pv.info.TypeOf(n.X)) {
					because("ranges over a function")
				}
			case *ast.CallExpr:
				tv := pv.info.Types[n.Fun]
				if tv.IsType() || tv.IsBuiltin() {
					break
				}
				if callee := typeutil.StaticCallee(pv.info, n); callee != nil {
					// What a call into another package may run of the code
					// that it is given, by the one rule the call graph uses.
					if why := pv.heldCallWhy(n); why != "" {
						because(why)
					}
					calls[fn.obj] = append(calls[fn.obj], callee.Origin())
					// Formatting a value calls its String or Error method.
					for _, method := range pv.formattedMethods(n) {
						calls[fn.obj] = append(calls[fn.obj], method.Origin())
					}
					// What a trusted function is handed to call runs as part
					// of this call: a literal is walked as part of the body,
					// a function or method is called, and anything else is a
					// call through a function value.
					for _, arg := range pv.handedArgs(n) {
						switch handed, isLit := pv.handedFunc(arg); {
						case isLit:
						case handed != nil:
							calls[fn.obj] = append(calls[fn.obj], handed.Origin())
						default:
							because(fmt.Sprintf("hands %s to %s, which calls it", types.ExprString(arg), callee.Name()))
						}
					}
					break
				}
				switch fun := ast.Unparen(n.Fun).(type) {
				case *ast.FuncLit:
					return true
				case *ast.Ident:
					if variable, ok := pv.info.Uses[fun].(*types.Var); ok && bound[variable] != nil {
						return true
					}
					// A trusted function that calls what it is handed under
					// calls runs code its caller hands over, which is
					// judged where it is handed over.
					if variable, ok := pv.info.Uses[fun].(*types.Var); ok && trusted != nil && trusted.calls.get(variable) != nil {
						return true
					}
				}
				if method, _ := throughValue(pv.info, n); method != nil {
					because("calls through the interface value " + types.ExprString(ast.Unparen(n.Fun).(*ast.SelectorExpr).X))
				} else {
					because("calls through the function value " + types.ExprString(n.Fun))
				}
			}
			return true
		})
		pv.mayCall[fn.obj] = direct
		if direct {
			pv.valueReasons[fn.obj] = valueReason{text: why}
			pending = append(pending, fn.obj)
		}
	}
	// What calls a function that may make such a call may make one too.
	callers := map[*types.Func][]*types.Func{}
	for caller, callees := range calls {
		for _, callee := range callees {
			if !local[callee] && pv.mayCallValuesAtCall(callee) {
				if !pv.mayCall[caller] {
					pv.mayCall[caller] = true
					pv.valueReasons[caller] = valueReason{via: callee}
					pending = append(pending, caller)
				}
			}
			callers[callee] = append(callers[callee], caller)
		}
	}
	for len(pending) > 0 {
		callee := pending[len(pending)-1]
		pending = pending[:len(pending)-1]
		for _, caller := range callers[callee] {
			if !pv.mayCall[caller] {
				pv.mayCall[caller] = true
				pv.valueReasons[caller] = valueReason{via: callee}
				pending = append(pending, caller)
			}
		}
	}
}

// valueReason is why a function may make a call through a value: a call,
// a range, or a hand-over in its body, or what the entry of a trusted
// function runs, in text; or a function it calls that may, in via.
type valueReason struct {
	text string
	via  *types.Func
}

// whyValues says why running a function may make a call through a value,
// as a sentence with the function as its subject, following the functions
// it calls that may to the first that does.
func (pv *pkgVerifier) whyValues(obj *types.Func) string {
	pv.mayCallValues(obj)
	hops := []string{}
	seen := map[*types.Func]bool{}
	for {
		origin := pv.originOf(obj)
		reason, local := byFuncOK(pv.valueReasons, origin)
		switch {
		case seen[origin]:
		case local && reason.via != nil:
			seen[origin] = true
			hops = append(hops, "calls "+reason.via.Name())
			obj = reason.via
			continue
		case local:
			hops = append(hops, reason.text)
		case isIfaceMethod(obj):
			hops = append(hops, "is a method of an interface, which runs whatever the value holds")
		default:
			switch fn := pv.contractOf(origin); {
			case isGeneric(origin) && pv.entryFor(origin.FullName()) != nil:
				hops = append(hops, "is trusted and runs what a parameter its runs lists without a contract under calls holds")
			case fn == nil:
				hops = append(hops, "has no contract")
			case fn.imported != nil:
				hops = append(hops, "is verified in package "+obj.Pkg().Path()+", whose contract says that it may")
			case fn.trust != nil:
				hops = append(hops, pv.runsReason(fn))
			}
		}
		break
	}
	return strings.Join(hops, ", which ")
}

// runsReason says which parameter of a trusted function under runs makes it
// one that may call through a value, and what that parameter can hold that
// verified code can make.
func (pv *pkgVerifier) runsReason(fn *funcInfo) string {
	for _, param := range fn.params {
		if !fn.runs.get(param) || fn.calls.get(param) != nil {
			continue
		}
		if what := pv.callableIn(param.Type(), map[types.Type]bool{}); what != "" {
			return fmt.Sprintf("is trusted and runs what %s holds, which can be %s", param.Name(), what)
		}
	}
	return "is trusted and runs what it is given"
}

// callableIn names what holdsCallable finds in a type.
func (pv *pkgVerifier) callableIn(t types.Type, seen map[types.Type]bool) string {
	if t == nil || seen[t] {
		return ""
	}
	seen[t] = true
	if held, replaced := heldAs(t); replaced {
		return pv.callableIn(held, seen)
	}
	switch u := t.Underlying().(type) {
	case *types.Signature:
		return "a function value of type " + t.String()
	case *types.Basic:
		if u.Kind() == types.UnsafePointer {
			return "an unsafe.Pointer, which may point to a function value or an interface value that verified code made"
		}
	case *types.Interface:
		if pv.fullyContracted(t) {
			return fmt.Sprintf("a value of %s, whose methods all have contracts, so that it can hold code that verified code made", t)
		}
		if isError(t) {
			return "an error, which can hold a value that verified code converted, whose methods are verified code"
		}
	case *types.Pointer:
		return pv.callableIn(u.Elem(), seen)
	case *types.Slice:
		return pv.callableIn(u.Elem(), seen)
	case *types.Array:
		return pv.callableIn(u.Elem(), seen)
	case *types.Map:
		if what := pv.callableIn(u.Key(), seen); what != "" {
			return what
		}
		return pv.callableIn(u.Elem(), seen)
	case *types.Struct:
		for field := range u.Fields() {
			if what := pv.callableIn(field.Type(), seen); what != "" {
				return what
			}
		}
	}
	return ""
}

// coveredType returns the type a Modifies entry ends in: the pointer, slice,
// or map whose memory it covers, or the field it names. It returns nil for
// an entry that does not follow the types, which is reported elsewhere.
func coveredType(fn *funcInfo, m *modTarget) types.Type {
	param, ok := fn.paramNames[m.name]
	if !ok {
		return nil
	}
	steps := make([]logic.Step, len(m.steps))
	for i, step := range m.steps {
		steps[i] = logic.Step{Field: step.field}
		if step.index == nil {
			continue
		}
		_, indexed, err := plan(param.Type(), steps[:i], fn.writtenIn())
		if err != nil {
			return nil
		}
		steps[i].Index = logic.IntLit(0)
		if isMap(indexed) {
			steps[i].Index = keyPlaceholder(indexed)
		}
	}
	_, final, err := plan(param.Type(), steps, fn.writtenIn())
	if err != nil {
		return nil
	}
	return final
}

// A value of a function type with a contract is made in one of these ways,
// where Go converts it to the type: from a function literal, a function, or
// a method value written there; from nil; or from a value of the same type.
// The first three are checked against the contract of the type there, as a
// function of their own: in a state with memory of its own, knowing of
// what they capture only its value where the value is made. Every other way
// is refused, since nothing would show that the value meets the contract.
// So is making a value of a function type that has no contract.

// functionValue evaluates an expression that is assigned to something of a
// function type.
func (v *fnVerifier) functionValue(e ast.Expr, want types.Type, st *state, guard []*logic.Term) value {
	inner := ast.Unparen(e)
	named, method := v.valueForm(inner)
	_, isLiteral := inner.(*ast.FuncLit)
	if named == nil && method == nil && !isLiteral {
		if !types.Identical(v.info.TypeOf(e), want) {
			v.unsupported(e.Pos(), fmt.Sprintf("converting %s to %s is not supported: a value of a function type is made only from "+
				"a function literal, a function, or a method value written there, from nil, or from a value of the same type",
				types.ExprString(e), want))
		}
		return v.eval(e, st, guard)
	}
	T := v.valueContract(want)
	if T == nil {
		what := types.ExprString(e)
		if isLiteral {
			what = "the function literal"
		}
		v.unsupported(e.Pos(), fmt.Sprintf("%s is used as a value of type %s, which has no contract; "+
			"declare a named function type with a contract and use it here%s", what, want, v.funcTypeHint(want)))
	}
	T = v.usable(e.Pos(), T, T.obj.Name(), st, guard, false)
	switch {
	case isLiteral:
		v.madeLiteral(inner.(*ast.FuncLit), T, st, guard)
	case named != nil:
		v.madeFrom(e, T, named, nil, st, guard)
	default:
		sel := inner.(*ast.SelectorExpr)
		recv := method.Type().(*types.Signature).Recv()
		// The receiver is evaluated where the method value is made, as for
		// a call: a pointer receiver takes the address of a variable, and a
		// value receiver copies the struct, which a nil pointer cannot.
		var receiver value
		func() {
			defer v.begin()()
			receiver = v.receiver(&ast.CallExpr{Fun: sel, Lparen: sel.End(), Rparen: sel.End()}, recv, st, guard)
		}()
		v.madeFrom(e, T, method, receiver, st, guard)
	}
	return value{logic.RefLit(1)}
}

// valueForm returns the function, or the method of a method value, that an
// expression names, if it is one of those. A method expression, T.M, is
// neither and is refused.
func (v *fnVerifier) valueForm(e ast.Expr) (named, method *types.Func) {
	switch e := e.(type) {
	case *ast.IndexExpr, *ast.IndexListExpr:
		// A generic function written with its type arguments is that
		// function, which the use then refuses as any generic function.
		if generic := explicitInstance(v.info, e); generic != nil {
			return generic, nil
		}
	case *ast.Ident:
		named, _ = v.info.Uses[e].(*types.Func)
	case *ast.SelectorExpr:
		if selection := v.info.Selections[e]; selection != nil {
			switch selection.Kind() {
			case types.MethodVal:
				method, _ = selection.Obj().(*types.Func)
			case types.MethodExpr:
				v.unsupported(e.Pos(), "a method expression, as in T.M, cannot be used as a value yet; use a method value, as in x.M, or a function literal")
			}
			break
		}
		named, _ = v.info.Uses[e.Sel].(*types.Func)
	}
	return named, method
}

// madeFrom checks that a function, or a method on a receiver, meets the
// contract of the function type it is used as. It is checked as a
// function of its own that calls it: called in a state where the Requires
// of the type hold, with memory of its own, it must meet the Requires of
// the function, write nothing the type does not list, and leave the Ensures
// of the type true. What it runs must make no call through a function
// value.
func (v *fnVerifier) madeFrom(e ast.Expr, T *funcInfo, callee *types.Func, receiver value, st *state, guard []*logic.Term) {
	site := v.site(e.Pos(), "in %s used as a value of type %s at %s", types.ExprString(e), T.obj.Name(), v.placeOf(e.Pos()))
	v.madeAs(e, e, T, callee, "a value", "a function value", site, func(_ *fnVerifier, _ *state, carry *transport) value {
		return carry.value(receiver)
	}, st, guard)
}

// madeAs checks that a function or method meets the contract T of what it
// is made into where e is converted: a value of a function type, or a
// method of an interface value. It is checked as a function of its own that
// calls it, written fun: called in a state where the Requires of T hold,
// with memory of its own, it must meet the Requires of the function, write
// nothing T does not list, and leave the Ensures of T true. What it runs
// must make no call through a function value or an interface value. as
// says what it is used as, and holder what holds it, in messages; receive
// gives the receiver of a method in the state of the check.
func (v *fnVerifier) madeAs(e, fun ast.Expr, T *funcInfo, callee *types.Func, as, holder string, site inlineSite,
	receive func(sv *fnVerifier, entry *state, carry *transport) value, st *state, guard []*logic.Term) {
	sig := callee.Type().(*types.Signature)
	if sig.TypeParams() != nil || sig.RecvTypeParams() != nil {
		v.unsupported(e.Pos(), fmt.Sprintf("generic functions cannot be used as %s yet", as))
	}
	fn := v.contractOf(callee)
	if fn == nil {
		v.unsupported(e.Pos(), fmt.Sprintf("it uses %s as %s, and %s has no contract; annotate %s with // @ annotations so that it is verified, "+
			"%s", callee.Name(), as, callee.Name(), callee.Name(), v.addEntryAdvice(callee.FullName())))
	}
	// A contract that cannot be read is reported here, and the check runs
	// with what can be read, or not at all; see viewOf.
	view := v.viewOf(fn)
	v.reportUnusable(e.Pos(), view, v.calleeName(callee))
	if view.cut {
		return
	}
	fn = view.fn
	// An entry of an interface method that lists no keeps claims that no
	// implementation keeps what it is handed, as io.Writer and io.Reader
	// document of p; a verified implementation must not, by its summary
	// (F27, step 3a).
	if T != nil && T.trust != nil {
		kept := map[string]bool{}
		for _, k := range T.trust.keeps {
			kept[k.name] = true
		}
		if summary := v.pkgVerifier.ownSummaryOf(fn); summary != nil {
			offset := len(fn.params) - sig.Params().Len()
			for i := range sig.Params().Len() {
				if at := offset + i; at >= 0 && at < len(summary.keeps) && summary.keeps[at] && i < len(T.params) && !kept[T.params[len(T.params)-sig.Params().Len()+i].Name()] {
					name := callee.Name()
					if recv := sig.Recv(); recv != nil {
						name = "(" + types.TypeString(recv.Type(), types.RelativeTo(v.pass.Pkg)) + ")." + name
					}
					v.report(e.Pos(), "%s keeps %s, which an implementation of %s may not, since its entry lists no keeps; copy what it needs of %s",
						name, sig.Params().At(i).Name(), as, sig.Params().At(i).Name())
				}
			}
		}
	}
	// What a value made by verified code runs may make no call through a
	// function value or an interface value. No contract of a function type
	// or an interface method has a variant, so nothing would then prove
	// that a chain of such calls ends: a value could be handed back to code
	// that calls it again. With this rule a call through a value made by
	// verified code runs code that makes no such call.
	if v.pkgVerifier.mayCallValues(callee) {
		v.unsupported(e.Pos(), fmt.Sprintf("%s may call through a function value or an interface value, and code that %s runs cannot do that yet: "+
			"no contract of a function type or of a method of an interface has a variant, so nothing would prove that such calls end; %s %s. "+
			"Make the value in code that is not verified, or keep that call out of what %s runs",
			callee.Name(), holder, callee.Name(), v.pkgVerifier.whyValues(callee), callee.Name()))
	}
	// A contract of a type that vouches for the errors of a result is
	// believed of every value of the type, so a value that verified code
	// makes must return only errors of known origin there.
	for i := range T.results {
		if T.vouches[i] && !v.returnsKnownErrors(callee) && !(fn.trust != nil && fn.vouches[i]) {
			v.report(e.Pos(), "%s may return an error whose origin is not known in %s, and %s vouches for the errors there; "+
				"return only errors made by errors.New or fmt.Errorf, or vouched for, %s", callee.Name(), spelledResult(T, i), vouchingContract(T), site.text)
		}
	}
	sv, entry, carry := v.subVerifier(T, st, guard, site)
	if sig.Recv() != nil {
		contract, made := T.obj.Name(), as
		if T.methodOf == nil {
			contract, made = "the contract of "+T.obj.Name(), "a value of type "+T.obj.Name()
		}
		sv.heldReceiver = fn.params[0]
		sv.heldRemedy = fmt.Sprintf("%s can list only what its parameters refer to, so a method that writes what its receiver refers to "+
			"cannot be used as %s yet", contract, made)
	}
	// The arguments of the call: the receiver, and the parameters of T in
	// order.
	args := map[*types.Var]value{}
	var inputs []*types.Var
	if sig.Recv() != nil {
		args[fn.params[0]] = receive(sv, entry, carry)
		inputs = fn.params[1:]
		// A method of an interface with states whose contract lists its
		// receiver but not behind it changes the states only (D2), so the
		// method may write nothing behind its receiver.
		if T.receiver != nil && v.hasStates(T.receiver.Type()) && !listsBehind(T) {
			sv.heldRemedy = fmt.Sprintf("the contract of %s lists %s, which covers its states and nothing else; a method that also writes behind its receiver "+
				"says so with behind(%s) in Modifies", T.obj.Name(), T.receiver.Name(), T.receiver.Name())
		}
	} else {
		inputs = fn.params
	}
	call := &ast.CallExpr{Fun: fun, Lparen: e.End(), Rparen: e.End()}
	if sig.Variadic() {
		// The value passes its slice on as it is.
		call.Ellipsis = e.End()
	}
	for i, param := range inputs {
		args[param] = sv.entry[T.params[i]]
		call.Args = append(call.Args, &ast.Ident{NamePos: e.Pos(), Name: T.params[i].Name()})
	}
	if fn.trust != nil && fn.keeps.len() > 0 {
		v.unsupported(e.Pos(), fmt.Sprintf("%s keeps code it is given, and cannot be used as %s: "+
			"what it would be given would come from whoever calls the value, and a value of a type has no place to say what it keeps", callee.Name(), as))
	}
	if fn.trust != nil && fn.decoded != nil {
		v.unsupported(e.Pos(), fmt.Sprintf("%s decodes into what it is given as encoding/json does, and cannot be used as %s: "+
			"what it is given is checked at each call written out, and a value is called with what nobody checks. Call %s directly", callee.Name(), as, callee.Name()))
	}
	if fn.trust != nil && fn.encoded != nil {
		v.unsupported(e.Pos(), fmt.Sprintf("%s encodes what it is given as encoding/json does, and cannot be used as %s: "+
			"what it is given is checked at each call written out, and a value is called with what nobody checks. Call %s directly", callee.Name(), as, callee.Name()))
	}
	if fn.trust != nil && fn.calls.len() > 0 {
		v.unsupported(e.Pos(), fmt.Sprintf("%s calls a function it is given, and cannot be used as %s: "+
			"what it would be given would come from code nobody has seen", callee.Name(), as))
	}
	if fn.trust != nil {
		v.noteUse(fn, e.Pos())
		// The receiver is handed to the trusted method at each call, as
		// at a call written out, where checkHandedOver looks at it. A
		// method whose entry lists it under runs may call through what it
		// holds, and is refused above.
		if recv := sig.Recv(); recv != nil && !fn.runs.get(fn.params[0]) && holdsCode(recv.Type(), map[types.Type]bool{}) {
			v.unsupported(e.Pos(), fmt.Sprintf("%s is used as %s, which hands its receiver to %s at each call; %s is trusted, and its receiver "+
				"is a value of type %s, which is or holds %s, so %s could run code through it that nobody has seen. "+
				"If its contract holds whatever that code does, list %s under runs in the contract",
				types.ExprString(e), as, fn.obj.Name(), fn.obj.Name(), recv.Type(), heldCode(recv.Type(), map[types.Type]bool{}), fn.obj.Name(), fn.params[0].Name()))
		}
		// The parameters of the value come from whoever calls it, so what
		// can carry code is handed on to the trusted function unseen.
		for _, param := range inputs {
			if fn.runs.get(param) || !holdsCode(param.Type(), map[types.Type]bool{}) {
				continue
			}
			// What a parameter under formats is given is checked at each
			// call written out, and a value is called with what nobody
			// checks.
			if param == fn.formatted {
				v.unsupported(e.Pos(), fmt.Sprintf("%s is used as %s, which passes what it is called with to %s as %s; %s formats %s, "+
					"and what a value is called with cannot be checked as it is at a call written out. Call %s directly",
					types.ExprString(e), as, fn.obj.Name(), param.Name(), fn.obj.Name(), param.Name(), fn.obj.Name()))
			}
			v.unsupported(e.Pos(), fmt.Sprintf("%s is used as %s, which passes what it is called with to %s as %s; "+
				"%s is trusted, and that can hold code nobody has seen. If its contract holds whatever that code does, "+
				"list %s under runs in the contract", types.ExprString(e), as, fn.obj.Name(), param.Name(), fn.obj.Name(), param.Name()))
		}
	}
	results := sv.invoke(call, fn, args, entry, nil)
	// A method of an interface with states whose contract lists its
	// receiver changes the states of a value verified code made, which are
	// ghost: the check chooses them after the call (F28).
	if T.receiver != nil && v.hasStates(T.receiver.Type()) && slices.ContainsFunc(T.modifies, func(m *modTarget) bool { return !m.behind && m.name == T.receiver.Name() }) {
		sv.chooseStates = T.receiver
	}
	sv.atReturn(entry, results, e.Pos())
}

// subVerifier returns a verifier for a function value that is made in a
// state: a function of its own with the contract of its type, whose entry
// state holds its parameters as the contract describes them, memory of its
// own, and a copy of the state where the value is made, in which every
// constant is renamed. The copy tells what is known of the values the
// function value keeps, and nothing of the memory it sees when it runs.
// carry renames values of the state where the value is made into the copy.
func (v *fnVerifier) subVerifier(fn *funcInfo, st *state, guard []*logic.Term, site inlineSite) (sv *fnVerifier, entry *state, carry *transport) {
	sv = v.newVerifier(fn)
	sv.originBody = v.bodyOrigin()
	sv.boxed = v.boxed
	sv.sites = append(slices.Clip(v.sites), site)
	// The names of the copy cannot be those of the verifier that reads it.
	// A copy made inside a copy renames the names of the outer copy again,
	// so they stay apart from both.
	carry = &transport{prefix: transportMark + " ", memo: map[*logic.Term]*logic.Term{}}
	entry = sv.enter()
	for _, fact := range st.hyps {
		entry.assume(carry.term(fact))
	}
	for _, cond := range guard {
		entry.assume(carry.term(cond))
	}
	// Everything that existed where the value was made exists when it runs.
	entry.assume(logic.Le(carry.term(st.brk), entry.brk))
	return sv, entry, carry
}

// bodyOrigin returns the body bodyOrigins reads.
func (v *fnVerifier) bodyOrigin() *ast.BlockStmt {
	if v.originBody != nil {
		return v.originBody
	}
	if v.fn.decl != nil {
		return v.fn.decl.Body
	}
	return nil
}

// transportMark begins every name in a renamed copy of a state. No name the
// verifier makes begins with it; see fresh.
const transportMark = "^"

// transport renames the constants of terms into a namespace of its own,
// apart from the names of the verifier that reads them. The constants of
// package-level variables that keep their values and nil are kept, since
// they mean the same everywhere.
type transport struct {
	prefix string
	memo   map[*logic.Term]*logic.Term
}

// term returns a term with its constants renamed.
func (tr *transport) term(t *logic.Term) *logic.Term {
	if renamed, done := tr.memo[t]; done {
		return renamed
	}
	var renamed *logic.Term
	switch {
	case t == logic.NilErr() || isFixedTerm(t):
		renamed = t
	case t.Op == logic.OpConst:
		renamed = logic.Const(tr.prefix+t.Name, t.Sort)
	case t.Op == logic.OpBound:
		renamed = logic.Bound(tr.prefix+t.Name, t.Sort)
	case len(t.Args) == 0:
		renamed = t
	default:
		args := make([]*logic.Term, len(t.Args))
		changed := false
		for i, arg := range t.Args {
			args[i] = tr.term(arg)
			changed = changed || args[i] != arg
		}
		renamed = t
		if changed {
			renamed = logic.WithArgs(t, args)
		}
	}
	tr.memo[t] = renamed
	return renamed
}

// value renames the leaves of a value.
func (tr *transport) value(val value) value {
	if val == nil {
		return nil
	}
	renamed := make(value, len(val))
	for i, leaf := range val {
		renamed[i] = tr.term(leaf)
	}
	return renamed
}

// A function literal used as a value travels: it may run during the call it
// is handed to or long after, any number of times, while the function that
// made it has moved on or returned. It is verified once where it is made,
// against the contract of the type it is given, as a function of its own:
// its parameters are what the contract allows, the memory it sees is
// memory of its own, and of the variables it captures it knows this:
//
//   - one that nothing assigns but its declaration, and whose address is not
//     taken, has the value it has where the literal is made, for ever, with
//     what is known of that value there;
//   - any other is a value of its type and nothing more.
//
// It may not assign a variable it captures, so no call through a value can
// change a variable of any function, and what in-place literals assume of
// the variables they capture stays true. A loop variable belongs to its
// iteration from Go 1.22 on and is captured with the value it has there; in
// older files the iterations share it, and it is assigned by the loop.

// madeLiteral checks a function literal that is made into a value of a
// function type with the contract T.
func (v *fnVerifier) madeLiteral(lit *ast.FuncLit, T *funcInfo, st *state, guard []*logic.Term) {
	captured := v.capturedBy(lit)
	v.stratified(lit)
	sig := v.info.TypeOf(lit).(*types.Signature)
	fn := &funcInfo{
		obj:         types.NewFunc(lit.Pos(), v.pass.Pkg, T.obj.Name(), sig),
		requires:    T.requires,
		ensures:     T.ensures,
		modifies:    T.modifies,
		params:      slices.Collect(sig.Params().Variables()),
		results:     slices.Collect(sig.Results().Variables()),
		paramNames:  map[string]*types.Var{},
		resultNames: map[string]int{},
		vouches:     map[int]bool{},
		decl:        &ast.FuncDecl{Name: &ast.Ident{NamePos: lit.Pos(), Name: T.obj.Name()}, Type: lit.Type, Body: lit.Body},
		ownParams:   map[string]*types.Var{},
		spelled:     T,
	}
	// The contract names the parameters and results of the type, which are
	// those of the literal in the same order.
	for i, param := range T.params {
		fn.paramNames[param.Name()] = fn.params[i]
	}
	for name, index := range T.resultNames {
		fn.resultNames[name] = index
	}
	for _, param := range fn.params {
		fn.ownParams[param.Name()] = param
	}
	for _, c := range v.fn.body {
		if c.pos >= lit.Body.Pos() && c.pos < lit.Body.End() {
			fn.body = append(fn.body, c)
		}
	}
	site := v.site(lit.Pos(), "in the function literal used as a value of type %s at %s", T.obj.Name(), v.placeOf(lit.Pos()))
	for i := range T.results {
		if T.vouches[i] && !v.returnsKnown(v.bodyOrigins(), lit.Body, fn.results) {
			v.report(lit.Pos(), "the function literal may return an error whose origin is not known in %s, and %s vouches for the errors there; "+
				"return only errors made by errors.New or fmt.Errorf, or vouched for, %s", spelledResult(T, i), vouchingContract(T), site.text)
			break
		}
	}
	sv, entry, carry := v.subVerifier(fn, st, guard, site)
	for _, variable := range captured {
		held := st.vals[variable]
		if held == nil {
			continue
		}
		if v.final(variable) || v.boxed[variable] {
			// The value is fixed: the variable itself, or for one that
			// lives in memory, the pointer to it. What it holds there is
			// read from the memory the literal sees.
			entry.vals[variable] = carry.value(held)
			continue
		}
		entry.vals[variable] = sv.unknown(variable.Name(), variable.Type(), entry)
	}
	sv.looped = findLooped(lit.Body)
	sv.classifyLiterals()
	for _, variable := range slices.Concat(fn.params, fn.results) {
		if sv.boxed[variable] && entry.vals[variable] != nil {
			sv.bind(entry, variable, entry.vals[variable])
		}
	}
	sv.seq(lit.Body.List, lit.Body.Lbrace, lit.Body.Rbrace, entry, ctrl{}, func(end *state) {
		sv.returned(end, nil, lit.Body.Rbrace)
	})
}

// capturedBy returns the local variables declared outside a literal that it
// uses, and refuses one that it assigns, or that holds a literal used in
// place: that literal may assign the variables of the function around it.
func (v *fnVerifier) capturedBy(lit *ast.FuncLit) []*types.Var {
	outside := func(variable *types.Var) bool {
		return variable != nil && !variable.IsField() && variable.Pkg() == v.pass.Pkg && variable.Parent() != v.pass.Pkg.Scope() &&
			(variable.Pos() < lit.Pos() || variable.Pos() >= lit.End())
	}
	var captured []*types.Var
	seen := map[*types.Var]bool{}
	ast.Inspect(lit.Body, func(n ast.Node) bool {
		var targets []ast.Expr
		switch n := n.(type) {
		case *ast.Ident:
			variable, _ := v.info.Uses[n].(*types.Var)
			if !outside(variable) || seen[variable] {
				break
			}
			seen[variable] = true
			if v.boundLits[variable] != nil {
				v.unsupported(n.Pos(), fmt.Sprintf("a function literal used as a value cannot use %s, which holds a function literal "+
					"of the function around it", n.Name))
			}
			captured = append(captured, variable)
		case *ast.AssignStmt:
			targets = n.Lhs
		case *ast.IncDecStmt:
			targets = []ast.Expr{n.X}
		case *ast.RangeStmt:
			if n.Tok == token.ASSIGN {
				targets = []ast.Expr{n.Key, n.Value}
			}
		}
		for _, target := range targets {
			if variable := v.assignedLocal(target); outside(variable) && !v.boxed[variable] {
				v.unsupported(target.Pos(), fmt.Sprintf("a function literal used as a value cannot assign %s, a variable of the function "+
					"around it: it may run when that function has moved on, and no call of it could tell that function what it did", variable.Name()))
			}
		}
		return true
	})
	return captured
}

// final reports whether a variable keeps the value it is declared with: no
// statement of the declared function around it assigns it but its
// declaration, its address is not taken, and it is not a named result, which
// a return assigns. The variable of a range loop belongs to its iteration
// from Go 1.22 on; before that the loop assigns it at each iteration.
func (v *fnVerifier) final(variable *types.Var) bool {
	body := v.bodyOrigin()
	if v.assignedIn == nil {
		v.assignedIn = map[*ast.BlockStmt]map[*types.Var]bool{}
	}
	assigned := v.assignedIn[body]
	if assigned == nil {
		assigned = v.findReassigned(body)
		v.assignedIn[body] = assigned
	}
	return !assigned[variable] && !v.boxed[variable]
}

// findReassigned returns the variables of a body that something other than
// their declaration assigns.
func (v *fnVerifier) findReassigned(body *ast.BlockStmt) map[*types.Var]bool {
	assigned := map[*types.Var]bool{}
	mark := func(e ast.Expr) {
		if variable := v.assignedLocal(e); variable != nil {
			assigned[variable] = true
		}
	}
	results := func(t *ast.FuncType) {
		if t.Results == nil {
			return
		}
		for _, field := range t.Results.List {
			for _, name := range field.Names {
				if variable, ok := v.info.Defs[name].(*types.Var); ok {
					assigned[variable] = true
				}
			}
		}
	}
	// The named results of the declared function whose body this is, which
	// may be the function around a literal that is verified on its own.
	for _, fn := range v.order {
		if fn.decl.Body == body {
			results(fn.decl.Type)
		}
	}
	ast.Inspect(body, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.FuncLit:
			results(n.Type)
		case *ast.AssignStmt:
			for _, lhs := range n.Lhs {
				id, isIdent := ast.Unparen(lhs).(*ast.Ident)
				if n.Tok == token.DEFINE && isIdent && v.info.Defs[id] != nil {
					continue
				}
				mark(lhs)
			}
		case *ast.IncDecStmt:
			mark(n.X)
		case *ast.RangeStmt:
			if n.Tok == token.ASSIGN || !v.freshEachIteration(n.Pos()) {
				for _, target := range []ast.Expr{n.Key, n.Value} {
					if target != nil {
						mark(target)
					}
				}
			}
		}
		return true
	})
	return assigned
}

// stratified refuses a literal used as a value whose body may call through
// a function value: itself, in a literal it calls in place, or in what it
// calls. No contract of a function type has a variant, so nothing would
// prove that a chain of such calls ends. A literal that it makes into a
// value is checked where it is made.
func (v *fnVerifier) stratified(lit *ast.FuncLit) {
	bound, _ := literalUses(v.info, lit.Body)
	inPlace := map[*ast.FuncLit]bool{}
	for _, inner := range bound {
		inPlace[inner] = true
	}
	refuse := func(pos token.Pos, what string) {
		v.unsupported(pos, fmt.Sprintf("the function literal used as a value %s, and code that a function value runs cannot do that yet: "+
			"no contract of a function type has a variant, so nothing would prove that such calls end. "+
			"Make the value in code that is not verified, or keep that call out of the literal", what))
	}
	ast.Inspect(lit.Body, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.FuncLit:
			return inPlace[n]
		case *ast.RangeStmt:
			if rangesByCalling(v.info.TypeOf(n.X)) {
				refuse(n.Pos(), "ranges over a function")
			}
		case *ast.CallExpr:
			tv := v.info.Types[n.Fun]
			if tv.IsType() || tv.IsBuiltin() {
				break
			}
			if callee := typeutil.StaticCallee(v.info, n); callee != nil {
				if why := v.pkgVerifier.heldCallWhy(n); why != "" {
					refuse(n.Pos(), why)
				}
				if v.pkgVerifier.mayCallValuesAtCall(callee) {
					refuse(n.Pos(), fmt.Sprintf("calls %s, which may call through a function value or an interface value: %s %s",
						callee.Name(), callee.Name(), v.pkgVerifier.whyValues(callee)))
				}
				// Formatting a value calls its String or Error method, as
				// part of the call.
				for _, method := range v.pkgVerifier.formattedMethods(n) {
					if v.pkgVerifier.mayCallValues(method) {
						refuse(n.Pos(), fmt.Sprintf("calls %s, which formats a value whose %s may call through a function value or an interface value: %s %s",
							callee.Name(), method.FullName(), method.Name(), v.pkgVerifier.whyValues(method)))
					}
				}
				// What a trusted function is handed to call runs during the
				// call, as part of the literal.
				for _, arg := range v.pkgVerifier.handedArgs(n) {
					switch handed, isLit := v.pkgVerifier.handedFunc(arg); {
					case isLit:
						inPlace[ast.Unparen(arg).(*ast.FuncLit)] = true
					case handed != nil:
						if v.pkgVerifier.mayCallValues(handed) {
							refuse(arg.Pos(), fmt.Sprintf("hands %s to %s, which calls it, and %s may call through a function value or an interface value: %s %s",
								handed.Name(), callee.Name(), handed.Name(), handed.Name(), v.pkgVerifier.whyValues(handed)))
						}
					default:
						refuse(arg.Pos(), fmt.Sprintf("hands the function value %s to %s, which calls it", types.ExprString(arg), callee.Name()))
					}
				}
				break
			}
			switch fun := ast.Unparen(n.Fun).(type) {
			case *ast.FuncLit:
				inPlace[fun] = true
				return true
			case *ast.Ident:
				if variable, ok := v.info.Uses[fun].(*types.Var); ok && bound[variable] != nil {
					return true
				}
			}
			if callee, _ := typeutil.Callee(v.info, n).(*types.Func); isIfaceMethod(callee) {
				refuse(n.Pos(), "calls through the interface value "+types.ExprString(ast.Unparen(n.Fun).(*ast.SelectorExpr).X))
				break
			}
			refuse(n.Pos(), "calls through the function value "+types.ExprString(n.Fun))
		}
		return true
	})
}
