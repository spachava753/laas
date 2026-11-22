package vego

import (
	"fmt"
	"go/token"
	"go/types"
	"math/big"
	"slices"
	"strconv"
	"strings"

	"github.com/spachava753/laas/vego/internal/logic"
)

// A state of an interface value, such as whether the value has been
// closed, belongs to what the value holds and not to the variable: two
// variables that hold the same reader share its state, and two readers do
// not. The verifier does not know what a value holds, so it gives every
// interface value a home, a number that is a function of its reference.
// Equal references have one home, so a copy, a conversion along shared
// declarations (which keeps the reference), and a value held in an any
// share the state. Two different references may or may not have one home:
// two interface values can hold the same file, or a wrapper and what it
// wraps. Only parameters are assumed apart, and verified callers prove it.
//
// Every state of every interface value lies in one region, at the row of
// the value's home, at the position of the state: a number made from the
// name of the state and of the interface that declares it, the same in
// every package. A method whose contract lists its receiver under Modifies
// may change the whole row, every state whoever declared it; one that does
// not keeps the row. That is the claim a declaration makes: every method a
// value with the state has, whose contract does not list the receiver,
// leaves the state unchanged.
//
// A state of an interface is declared on a defined interface type that
// declares a method of its own: in the shipped files for the standard
// library, in a project's trust file for an interface of another module,
// and with a State annotation in the doc comment of an interface of the project. An
// interface has the states of every interface that declares one of its
// methods, so io.ReadCloser has the state closed of io.Closer.

// stateRegion is the region that holds the states of interface values.
const stateRegion = "iface state"

// stateCell is the cell of one state at its position.
var stateCell = cell{key: stateRegion, sort: logic.Bool}

// homes names the function from the reference of an interface value to its
// home. It is a sequence that nothing writes, read at the reference, which
// the translation to SMT-LIB writes as any other read.
var homes = logic.Const("home", logic.SeqOf(logic.Ref))

// home returns the home of an interface value.
func home(ref *logic.Term) *logic.Term {
	return logic.Select(homes, ref)
}

// ifaceState is a state that an interface type declares.
type ifaceState struct {
	owner  *types.TypeName // the interface that declares it
	name   string
	reason string
	// file is the trust file that declares it, or nil for one declared in
	// source.
	file *trustFile
}

// position returns where the state lies in the row of a home: the number
// whose digits in base 256 are the bytes of its name qualified by the
// interface that declares it, as in "io".Closer@closed. No name
// holds a zero byte, so two names give two numbers.
func (s ifaceState) position() *logic.Term {
	qualified := strconv.Quote(s.owner.Pkg().Path()) + "." + s.owner.Name() + "@" + s.name
	return logic.BigLit(new(big.Int).SetBytes([]byte(qualified)))
}

// title names the state for a reader, as in closed of io.Closer.
func (s ifaceState) title() string {
	return s.name + " of " + s.owner.Pkg().Name() + "." + s.owner.Name()
}

// stateFact carries the states that an interface type of a package declares
// in source, with the reason of each, which is its doc comment.
type stateFact struct {
	Names   []string
	Reasons []string
}

func (*stateFact) AFact() {}

func (f *stateFact) String() string { return "states(" + strings.Join(f.Names, ", ") + ")" }

// declaringInterface returns the defined interface type that declares a
// method of an interface, or nil.
func declaringInterface(method *types.Func) *types.TypeName {
	recv := method.Type().(*types.Signature).Recv()
	if recv == nil {
		return nil
	}
	named, ok := types.Unalias(recv.Type()).(*types.Named)
	if !ok {
		return nil
	}
	return named.Obj()
}

// ifaceStatesOf returns the states of an interface type: those of every
// interface that declares one of its methods.
func (pv *pkgVerifier) ifaceStatesOf(t types.Type) []ifaceState {
	if !isIface(t) {
		return nil
	}
	var states []ifaceState
	seen := map[*types.TypeName]bool{}
	for method := range t.Underlying().(*types.Interface).Methods() {
		owner := declaringInterface(method)
		if owner == nil || seen[owner] {
			continue
		}
		seen[owner] = true
		states = append(states, pv.declaredStates(owner)...)
	}
	return states
}

// hasStates reports whether values of a type have a state.
func (pv *pkgVerifier) hasStates(t types.Type) bool {
	return len(pv.ifaceStatesOf(t)) > 0
}

// declaredStates returns the states an interface type declares itself.
func (pv *pkgVerifier) declaredStates(owner *types.TypeName) []ifaceState {
	if pv.ownStates == nil {
		pv.ownStates = map[*types.TypeName][]ifaceState{}
	}
	if states, done := pv.ownStates[owner]; done {
		return states
	}
	var states []ifaceState
	switch {
	case owner.Pkg() == nil:
	case owner.Pkg() == pv.pass.Pkg:
		// Collected from the annotations of the package before anything
		// is verified; see addState.
	default:
		if fact := (&stateFact{}); pv.pass.ImportObjectFact != nil && pv.pass.ImportObjectFact(owner, fact) {
			for i, name := range fact.Names {
				states = append(states, ifaceState{owner: owner, name: name, reason: fact.Reasons[i]})
			}
			break
		}
		states = pv.fileStates(owner)
	}
	pv.ownStates[owner] = states
	return states
}

// fileStates returns the states that the trust files declare for an
// interface of another module, and records that the proofs of the package
// rest on them, or on there being none: two modules built together that
// declare different states for one interface would let a value whose state
// one proof changed reach another proof that reads it otherwise. A
// declaration that is not allowed gives no state; loadTrust reports it.
func (pv *pkgVerifier) fileStates(owner *types.TypeName) []ifaceState {
	key := stateKey(owner.Pkg().Path(), owner.Name())
	var file *trustFile
	var decls []stateDecl
	for _, shipped := range shippedContracts() {
		if len(shipped.states[key]) > 0 {
			file, decls = shipped, shipped.states[key]
		}
	}
	// A declaration that is not allowed is reported by loadTrust and
	// gives no state; the shipped ones stand.
	if pv.projectTrust != nil && len(pv.projectTrust.states[key]) > 0 && file == nil && pv.fileStateProblem(owner, key) == "" {
		file, decls = pv.projectTrust, pv.projectTrust.states[key]
	}
	fingerprint := ""
	var states []ifaceState
	for _, decl := range decls {
		states = append(states, ifaceState{owner: owner, name: decl.name, reason: decl.reason, file: file})
		if fingerprint != "" {
			fingerprint += "\n"
		}
		fingerprint += decl.name + ": " + decl.reason
	}
	use := "states of " + key
	if file == nil && pv.unentered != nil {
		pv.unentered[use] = pv.inAnalysedModule(owner.Pkg(), owner.Pos())
	} else {
		pv.stateUses = append(pv.stateUses, &EntryUse{Key: use, Reason: fingerprint, Shipped: file.shipped, File: file.path, Line: decls[0].typeLine,
			Every: key, Fingerprint: fingerprint})
	}
	return states
}

// fileStateProblem says what is wrong with a declaration of states for a
// type in a project trust file, or returns "".
func (pv *pkgVerifier) fileStateProblem(owner *types.TypeName, key string) string {
	for _, shipped := range shippedContracts() {
		if len(shipped.states[key]) > 0 {
			return "the contracts shipped with vego declare; remove the declaration"
		}
	}
	return pv.stateDeclProblem(owner)
}

// declaresMethod reports whether an interface type declares a method
// itself. A type defined from another interface, as in type B io.Closer, has
// the methods of that declaration, which its states belong to.
func declaresMethod(owner *types.TypeName) bool {
	for method := range owner.Type().Underlying().(*types.Interface).Methods() {
		if declaringInterface(method) == owner {
			return true
		}
	}
	return false
}

// stateDeclProblem says what is wrong with declaring a state on a type, or
// returns "".
func (pv *pkgVerifier) stateDeclProblem(owner *types.TypeName) string {
	named, isNamed := owner.Type().(*types.Named)
	switch {
	case !types.IsInterface(owner.Type()):
		return "is not an interface type; a trust file can declare states only of an interface"
	case owner.IsAlias() || !isNamed || named.TypeParams() != nil || owner.Parent() != owner.Pkg().Scope():
		return "is not a defined interface type at package level without type parameters"
	case isError(owner.Type()) || !isIface(owner.Type()):
		return "is not an interface that vego models"
	case !declaresMethod(owner):
		return "declares no method of its own; declare the state on the interface that declares the methods whose contracts speak of it"
	case pv.inAnalysedModule(owner.Pkg(), owner.Pos()):
		return "is declared in the module of this package; declare the state with @State in its doc comment"
	}
	if fact := (&stateFact{}); pv.pass.ImportObjectFact != nil && pv.pass.ImportObjectFact(owner, fact) && len(fact.Names) > 0 {
		return "declares states in source"
	}
	return ""
}

// makeable reports whether verified code can make a value of an interface
// type by converting a value of a type that is not an interface: every
// method has a contract that can be used, and no contract in use names its
// receiver, which is the only way a contract can speak of a state. A value
// made by verified code would have to keep the states of the interface true
// to what its methods do, and nothing ties a state to an implementation
// yet. Stratification counts exactly the interfaces this admits.
func (pv *pkgVerifier) makeable(t types.Type) bool {
	if !pv.fullyContracted(t) {
		return false
	}
	return pv.stateSpeaker(t) == nil
}

// stateSpeaker returns a method of an interface whose contract in use names
// its receiver, or nil.
func (pv *pkgVerifier) stateSpeaker(t types.Type) *types.Func {
	for method := range t.Underlying().(*types.Interface).Methods() {
		if fn := pv.methodContract(method); fn != nil && fn.receiver != nil {
			return method
		}
	}
	return nil
}

// stateNames names the states of a type for messages, as in "the state
// closed" or "the states closed and open", with the pronoun that stands for
// them.
func stateNames(states []ifaceState) (phrase, pronoun string) {
	names := make([]string, len(states))
	for i, s := range states {
		names[i] = s.name
	}
	slices.Sort(names)
	if len(names) == 1 {
		return "the state " + names[0], "it"
	}
	return "the states " + strings.Join(names[:len(names)-1], ", ") + " and " + names[len(names)-1], "them"
}

// ifaceState resolves name(x) for an interface value x whose reference is
// ref: the cell of the state in the row of its home, read in mem.
func (e *specEnv) ifaceState(what string, typ types.Type, ref *logic.Term, sink *state, mem memory, name string) (*logic.Term, error) {
	states := e.v.ifaceStatesOf(typ)
	var found []ifaceState
	for _, s := range states {
		if s.name == name {
			found = append(found, s)
		}
	}
	switch {
	case len(found) > 1:
		return nil, fmt.Errorf("%s(%s) is ambiguous: %s has the state %s of %s and of %s", name, what, typ,
			name, found[0].owner.Name(), found[1].owner.Name())
	case len(found) == 0 && len(states) == 0:
		return nil, &logic.NoState{Msg: fmt.Sprintf("%s(%s): %s has type %s, which has no states", name, what, what, typ)}
	case len(found) == 0:
		phrase, _ := stateNames(states)
		return nil, &logic.NoState{Msg: fmt.Sprintf("%s(%s): %s has type %s, which has %s", name, what, what, typ, phrase)}
	}
	return e.v.fetch(sink, mem, []cell{stateCell}, home(ref), found[0].position())[0], nil
}

// reservedStateNames are the names that mean something of their own in
// formulas and cannot name a state.
var reservedStateNames = append(slices.Clone(logic.Reserved), "nil", "True", "False",
	"And", "Or", "Forall", "Exists", "in", "result")

// addState records a state declared with a State annotation in the doc comment of an
// interface type of the package.
func (pv *pkgVerifier) addState(name *types.TypeName, c *clause) {
	text := strings.TrimSpace(c.text)
	if name == nil || pv.stateDeclProblemHere(name) != "" {
		problem := "is not a type"
		if name != nil {
			problem = pv.stateDeclProblemHere(name)
		}
		what := "this declaration"
		if name != nil {
			what = name.Name()
		}
		pv.report(c.pos, "a state can be declared only on a defined interface type that declares a method of its own; %s %s", what, problem)
		return
	}
	if !token.IsIdentifier(text) || slices.Contains(reservedStateNames, text) {
		pv.report(c.pos, "%q cannot name a state: write one identifier that the formula language does not use, as in // @State closed", text)
		return
	}
	if slices.ContainsFunc(pv.ownStates[name], func(s ifaceState) bool { return s.name == text }) {
		pv.report(c.pos, "%s already has the state %s", name.Name(), text)
		return
	}
	pv.ownStates[name] = append(pv.ownStates[name], ifaceState{owner: name, name: text,
		reason: "declared with @State at " + pv.pass.Fset.Position(c.pos).String()})
}

// stateDeclProblemHere says what is wrong with declaring a state in source
// on a type of the package, or returns "".
func (pv *pkgVerifier) stateDeclProblemHere(name *types.TypeName) string {
	named, isNamed := name.Type().(*types.Named)
	switch {
	case !types.IsInterface(name.Type()):
		return "is not an interface type"
	case name.IsAlias() || !isNamed || named.TypeParams() != nil || name.Parent() != name.Pkg().Scope():
		return "is not a defined interface type at package level without type parameters"
	case isError(name.Type()) || !isIface(name.Type()):
		return "is not an interface that vego models"
	case !declaresMethod(name):
		return "declares no method of its own, so no contract written on it could change the state"
	}
	return ""
}

// setReceiver names the receiver of the contract of a method of an
// interface, as a Receiver annotation or receiver in an entry does. It returns what is
// wrong with the name, or "".
func (fn *funcInfo) setReceiver(name string, method *types.Func) string {
	owner := declaringInterface(method)
	_, isParam := fn.paramNames[name]
	_, isResult := fn.resultNames[name]
	switch {
	case fn.receiver != nil:
		return "the receiver is named twice"
	case !token.IsIdentifier(name) || name == "_":
		return fmt.Sprintf("%q cannot name the receiver; write one identifier", name)
	case owner == nil:
		return "the method has no receiver to name"
	case isParam || isResult:
		return fmt.Sprintf("%s already names a parameter or a result of %s", name, method.Name())
	case fn.ambiguous(name, false):
		return fmt.Sprintf("%s means something else in annotations", name)
	}
	fn.receiver = types.NewParam(method.Pos(), method.Pkg(), name, owner.Type())
	fn.paramNames[name] = fn.receiver
	return ""
}

// placesWithin reports whether an Ensures of a contract of an interface
// method says that something lies within the receiver, as a header lies in
// the response writer that hands it out (F34 of the review of step 4).
func placesWithin(fn *funcInfo) bool {
	found := false
	for _, c := range fn.ensures {
		if c.node == nil {
			continue
		}
		c.node.Walk(func(n *logic.Node) {
			if n.Kind == logic.NCall && n.Name == "within" && len(n.Kids) == 2 && n.Kids[1].Kind == logic.NIdent && n.Kids[1].Name == fn.receiver.Name() {
				found = true
			}
		})
	}
	return found
}

// checkReceivers reports, once the annotations of the package are read, a
// receiver named for a method of an interface without states, and an
// interface of the package with two states of one name.
func (pv *pkgVerifier) checkReceivers() {
	for method, fn := range pv.ifaceMethods {
		if fn.receiver != nil && !pv.hasStates(fn.receiver.Type()) && !writesBehind(fn) && !placesWithin(fn) {
			pv.report(method.Pos(), "%s names its receiver %s, but %s has no states and the contract does not list %s in Modifies; "+
				"a contract names its receiver to speak of its states, to say that the method writes behind it, or to place a result within it; "+
				"remove the Receiver annotation, list %s in a // @Modifies clause, or declare a state with @State",
				methodTitle(method), fn.receiver.Name(), declaringInterface(method).Name(), fn.receiver.Name(), fn.receiver.Name())
			fn.broken = true
		}
	}
	for _, name := range pv.pass.Pkg.Scope().Names() {
		obj, ok := pv.pass.Pkg.Scope().Lookup(name).(*types.TypeName)
		if !ok || !isIface(obj.Type()) {
			continue
		}
		seen := map[string]ifaceState{}
		for _, s := range pv.ifaceStatesOf(obj.Type()) {
			if first, twice := seen[s.name]; twice {
				pv.report(obj.Pos(), "%s has two states named %s, %s and %s; a formula %s(x) could not tell them apart, so rename one",
					obj.Name(), s.name, first.title(), s.title(), s.name)
				continue
			}
			seen[s.name] = s
		}
	}
}

// exportStates publishes the states that the interface types of the
// package declare in source.
func (pv *pkgVerifier) exportStates() {
	for owner, states := range pv.ownStates {
		if owner.Pkg() != pv.pass.Pkg || len(states) == 0 {
			continue
		}
		fact := &stateFact{}
		for _, s := range states {
			fact.Names = append(fact.Names, s.name)
			fact.Reasons = append(fact.Reasons, s.reason)
		}
		pv.pass.ExportObjectFact(owner, fact)
	}
}

// sharing lists the pairs of interface parameters with states, the
// receiver of an interface method among them, which a function may assume,
// and its callers must show, to have homes of their own when neither is
// nil, as slice parameters of one element type share no element. Only a
// pair of which the contract lists one under Modifies is such a pair: a
// contract that lists neither changes no state of either, since a write of
// a state it does not list is refused, so what it reads of their states
// does not depend on whether their homes are one. And only a pair whose
// states the contract names, of each (F5 of the design review): what the
// body relies on of a state of a parameter must come from the contract, so
// a contract that names no state of one relies on none, as Pump, which
// lists its reader and writer for their footprints, does not. One value
// passed as both of such a pair is refused, as two overlapping slices are:
// a function that closes both could not be verified otherwise. A call that
// changes the states of one changes every state at its home, so two values
// whose types have no state in common may still not share a home.
func (v *fnVerifier) sharing(fn *funcInfo) [][2]*types.Var {
	inputs := slices.Clone(fn.params)
	if fn.receiver != nil {
		inputs = append([]*types.Var{fn.receiver}, inputs...)
	}
	listed := map[*types.Var]bool{}
	for _, m := range fn.modifies {
		if form, _, err := v.locateTarget(fn, m, nil, nil, nil); err == nil && form.row && form.direct && len(m.steps) == 0 {
			listed[form.param] = true
		}
	}
	var pairs [][2]*types.Var
	for i, first := range inputs {
		if !v.hasStates(first.Type()) {
			continue
		}
		for _, second := range inputs[i+1:] {
			if v.hasStates(second.Type()) && (listed[first] || listed[second]) && v.namesStateOf(fn, first) && v.namesStateOf(fn, second) {
				pairs = append(pairs, [2]*types.Var{first, second})
			}
		}
	}
	return pairs
}

// namesStateOf reports whether a clause of a contract names a state of a
// parameter, as closed(r) or closed(r') does.
func (v *fnVerifier) namesStateOf(fn *funcInfo, param *types.Var) bool {
	states := map[string]bool{}
	for _, state := range v.ifaceStatesOf(param.Type()) {
		states[state.name] = true
	}
	found := false
	for _, clauses := range [][]*clause{fn.requires, fn.ensures} {
		for _, c := range clauses {
			if c.node == nil {
				continue
			}
			c.node.Walk(func(n *logic.Node) {
				if n.Kind == logic.NCall && states[n.Name] && len(n.Kids) == 1 && n.Kids[0].Kind == logic.NIdent && n.Kids[0].Name == param.Name() {
					found = true
				}
			})
		}
	}
	return found
}

// apartHomes states that two interface values that are not nil have homes
// of their own. The nil interface has a home too, and two nil values share
// it.
func apartHomes(a, b *logic.Term) *logic.Term {
	zero := logic.RefLit(0)
	return logic.Or(logic.Eq(a, zero), logic.Eq(b, zero), logic.Ne(home(a), home(b)))
}
