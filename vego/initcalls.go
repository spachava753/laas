package vego

import (
	"go/ast"
	"go/types"
	"slices"

	"github.com/spachava753/laas/vego/internal/logic"
)

// Initialisers that call functions (step 5 of F32).
//
// In a package with annotations every initialiser is run as code, in Go's
// order of initialisation, as checkValueInitialisers runs those of the
// variables that hold code. A call there of a verified function whose
// Requires may not hold is reported where it stands (F1). What the run
// shows of a fixed variable, the facts of its path that read no memory, is
// known to every function of the package that reads it.
//
// Why that is sound: in every run of the program that reads the variable
// its initialiser completed, and the real results of its calls and the
// variable's value satisfy the facts of that path together. The constants
// of the run other than those of fixed variables are renamed into names of
// the variable's own, which nothing else constrains, so asserting the facts
// adds nothing false; and the variable is fixed, so they hold from the end
// of its initialisation on. Go initialises every variable an initialiser
// reads first, also through functions, so what the run knows of other
// fixed variables already holds there; hidden init code stays refused, as
// part 1 refuses it.

// runInitialiser runs an initialiser as code, reporting a call of a
// verified function outside its Requires, and records what it shows of the
// fixed variables it initialises.
func (pv *pkgVerifier) runInitialiser(init *types.Initializer) {
	// A function literal in an initialiser is not run here; it shows
	// nothing, and a call in it of a verified function that requires
	// something is reported, since nothing checks that call (F1).
	var literal *ast.FuncLit
	ast.Inspect(init.Rhs, func(n ast.Node) bool {
		if lit, ok := n.(*ast.FuncLit); ok && literal == nil {
			literal = lit
		}
		return literal == nil
	})
	if literal != nil {
		ast.Inspect(literal, func(n ast.Node) bool {
			call, ok := n.(*ast.CallExpr)
			if !ok {
				return true
			}
			callee := pv.calleeAt(call)
			// A call through a value, or of a method of an interface, may
			// run a verified function of the package too (F22).
			var contract *funcInfo
			name := types.ExprString(call.Fun)
			switch {
			case callee == nil:
				if tv := pv.info.Types[call.Fun]; !tv.IsType() && !tv.IsBuiltin() {
					contract = pv.valueContract(pv.info.TypeOf(call.Fun))
				}
			case isGeneric(callee):
			case callee.Type().(*types.Signature).Recv() != nil && isIface(callee.Type().(*types.Signature).Recv().Type()):
				contract = pv.methodContract(callee)
			default:
				if fn := pv.contractOf(callee); fn != nil && fn.trust == nil {
					contract, name = fn, callee.Name()
				}
			}
			if contract != nil && len(contract.requires) > 0 {
				pv.report(call.Pos(), "%s is called in a function literal in the initialiser of a package-level variable, where its Requires is not checked; "+
					"call it from a function with a contract of its own", name)
			}
			if callee == nil || isGeneric(callee) {
				return true
			}
			if entry := pv.entryFor(pv.originOf(callee).FullName()); entry != nil && entry.initialiserOnly {
				pv.report(call.Pos(), "%s", initialiserOnlyWhy(callee))
			}
			return true
		})
		return
	}
	var captured []string
	saved := pv.capturing
	pv.capturing = &captured
	var facts []*logic.Term
	failed := false
	name := "_"
	if len(init.Lhs) > 0 && init.Lhs[0] != nil {
		name = init.Lhs[0].Name()
	}
	pv.initRunning = true
	defer func() { pv.initRunning = false }()
	pv.run(&funcInfo{obj: types.NewFunc(init.Rhs.Pos(), pv.pass.Pkg, "the initialiser of "+name, types.NewSignatureType(nil, nil, nil, nil, nil, false))}, func(v *fnVerifier) {
		v.inInitialiser = true
		st := &state{vals: map[*types.Var]value{}, mem: memory{}, brk: logic.Const("brk", logic.Ref), noted: map[string]bool{}}
		v.entryBrk = st.brk
		st.assume(logic.Le(logic.IntLit(1), st.brk))
		v.openUnit(st)
		var vals []value
		if len(init.Lhs) == 1 {
			vals = []value{v.evalAs(init.Rhs, init.Lhs[0].Type(), st, nil)}
		} else {
			whole := v.eval(init.Rhs, st, nil)
			at := 0
			for _, variable := range init.Lhs {
				n := len(mustLayout(variable.Type()))
				vals = append(vals, whole[at:at+n])
				at += n
			}
		}
		v.closeUnit(st)
		facts = pv.initialiserFacts(init, vals, st)
		failed = v.initFailed
	})
	pv.capturing = saved
	// A run that did not verify shows nothing.
	if len(captured) > 0 || failed {
		return
	}
	// What part 1 reads from an initialiser of its forms is already known,
	// more cheaply.
	for _, variable := range init.Lhs {
		if known, fixed := pv.fixed[variable]; variable != nil && variable.Name() != "_" && fixed && !knownComplete(known) {
			pv.initFacts[variable] = facts
		}
	}
}

// initialiserFacts returns what the run of an initialiser shows of the
// values it gives: the facts of its path, with every constant but those of
// fixed variables renamed into the namespace of the first variable, and the
// leaves of each variable equal to the value it was given, keeping only
// what is connected to those leaves and reads no sequence.
func (pv *pkgVerifier) initialiserFacts(init *types.Initializer, vals []value, st *state) []*logic.Term {
	var first *types.Var
	for _, variable := range init.Lhs {
		if variable != nil && variable.Name() != "_" {
			first = variable
			break
		}
	}
	if first == nil {
		return nil
	}
	tr := &transport{prefix: "init " + errorKey(first) + " ", memo: map[*logic.Term]*logic.Term{}}
	var facts []*logic.Term
	for _, fact := range st.hyps {
		facts = append(facts, tr.term(fact))
	}
	reached := map[string]bool{}
	for i, variable := range init.Lhs {
		if variable == nil || variable.Name() == "_" || i >= len(vals) {
			continue
		}
		for j, lf := range mustLayout(variable.Type()) {
			// A sequence, as a string, has no equality in the logic; what
			// is known of one is what part 1 reads from the initialiser.
			if lf.sort.IsSeq() {
				continue
			}
			leaf := logic.Const(fixedName+errorKey(variable)+lf.path, lf.sort)
			reached[leaf.Name] = true
			facts = append(facts, logic.Eq(leaf, tr.term(vals[i][j])))
		}
	}
	// Only the facts connected to the variable's leaves, through any
	// constant they name, tell a reader anything; one that names a
	// sequence of the run, as memory or a string it made, is of the run's
	// memory. Fixed constants hold the same everywhere, so what the run
	// knew of another fixed variable, as later = 3, comes along.
	names := func(t *logic.Term) (out []*logic.Term) {
		seen := map[*logic.Term]bool{}
		var walk func(t *logic.Term)
		walk = func(t *logic.Term) {
			if seen[t] {
				return
			}
			seen[t] = true
			if t.Op == logic.OpConst && t != logic.NilErr() {
				out = append(out, t)
			}
			for _, arg := range t.Args {
				walk(arg)
			}
		}
		walk(t)
		return out
	}
	usable := slices.DeleteFunc(slices.Clone(facts), func(fact *logic.Term) bool {
		return slices.ContainsFunc(names(fact), func(c *logic.Term) bool { return c.Sort.IsSeq() && !isFixedTerm(c) })
	})
	var kept []*logic.Term
	taken := make([]bool, len(usable))
	for changed := true; changed; {
		changed = false
		for i, fact := range usable {
			if taken[i] {
				continue
			}
			constants := names(fact)
			if !slices.ContainsFunc(constants, func(c *logic.Term) bool { return reached[c.Name] }) {
				continue
			}
			taken[i], changed = true, true
			kept = append(kept, fact)
			for _, c := range constants {
				reached[c.Name] = true
			}
		}
	}
	return kept
}

// knownComplete reports whether part 1 reads from an initialiser all that a
// run of it could show of the value: something of every part.
func knownComplete(known knownValue) bool {
	switch known.Kind {
	case knownNothing:
		return false
	case knownStruct:
		return !slices.ContainsFunc(known.Parts, func(part knownValue) bool { return !knownComplete(part) })
	}
	return true
}

// initialiserOnlyWhy says why a call of an entry marked initialiserOnly
// cannot stand where it stands: outside the initialiser of a
// package-level variable, its panic can be recovered and the code after it
// run.
func initialiserOnlyWhy(callee *types.Func) string {
	return callee.Name() + " panics when it fails, and its trusted contract holds only where the initialiser of a package-level variable calls it, " +
		"outside every function: a panic there stops the program, or the plugin that holds the package, before any code reads the variable; " +
		"elsewhere call a function that returns an error and check it, as regexp.Compile"
}
