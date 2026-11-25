package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"maps"
	"slices"
	"sort"
	"strings"

	"github.com/spachava753/laas/vego/internal/logic"
	"github.com/spachava753/laas/vego/internal/solver"
)

// Optional interfaces (F35). Functions of the standard library find a
// faster method of a value they are handed by asserting it to an interface
// its static type does not have, as io.WriteString asserts its writer to
// io.StringWriter. A method found that way runs under the entry of the
// interface found, so every value verified code makes under a static type
// from which such an assertion can lead must meet that entry too.
//
// O is the set of interfaces of other modules each of whose methods has an
// entry in the trust files, which have no states and are not scoped: of
// the shipped files io.Writer, io.Reader, and io.StringWriter. A project's
// trust file may add interfaces of other modules. Interfaces with states
// are left out, since a state found by assertion would not be the state
// of a pointer the value holds; scoped ones, since what is taken out by
// assertion would need the marks of a scoped value; and interfaces with a
// method that has no entry, since verified code could then make a value of
// them that stratification does not count.
//
// What is known depends on the static type a value was checked, assumed,
// or vouched under, so the feature is stated over static types. For an
// interface S declared in package P, O_S is the members of O whose package
// is in P's build: every package that converts to S type-checks against P,
// so it can resolve each of them. S is O-typed when it has, for some X in
// O_S, a method of the name and the signature of each method of X. Then:
//   - a conversion of a concrete value to an O-typed S checks the value
//     against every X in O_S its type implements, for each method of X that
//     S does not have as the same method (optionalChecks);
//   - a conversion between interfaces to an O-typed target needs a source
//     that is O-typed with every member of the target's O in its own
//     (optionalSourceWhy, F7 of the design review);
//   - the value of an assertion of an O-typed operand to an interface whose
//     methods the operand lacks may be used when each such method belongs
//     to a member of the operand's O (R2's lift, in usedIfaceWhy);
//   - an entry over an O-typed parameter may list such an interface under
//     asserts (beyondStatic).
//
// The invariant OI: every non-nil value of an O-typed static type S that
// verified code makes holds a value whose dynamic type meets, for every X
// in O_S it implements, each method of X as madeAs checks it against X's
// entry. The routes are in the roadmap (Dynamic types and typed errors,
// Part 3 as built).

// optionalSet returns O as this package sees it: the members it can
// resolve, by key, in its build.
func (pv *pkgVerifier) optionalSet() map[string]*types.TypeName {
	if pv.optional != nil {
		return pv.optional
	}
	pv.optional = map[string]*types.TypeName{}
	keys := map[string]bool{}
	collect := func(file *trustFile) {
		for key := range file.entries {
			receiver, _, isMethod := strings.Cut(strings.TrimPrefix(key, "("), ").")
			if isMethod && strings.HasPrefix(key, "(") && !strings.HasPrefix(receiver, "*") {
				keys[receiver] = true
			}
		}
	}
	for _, file := range shippedContracts() {
		collect(file)
	}
	if pv.projectTrust != nil {
		collect(pv.projectTrust)
	}
	for _, key := range slices.Sorted(maps.Keys(keys)) {
		dot := strings.LastIndex(key, ".")
		if dot < 0 {
			continue
		}
		pkg := packageOf(pv.pass.Pkg, strings.Trim(key[:dot], `"`))
		if pkg == nil {
			continue
		}
		name, ok := pkg.Scope().Lookup(key[dot+1:]).(*types.TypeName)
		if !ok || name.IsAlias() || !isIface(name.Type()) || pv.inAnalysedModule(pkg, name.Pos()) {
			continue
		}
		if named, isNamed := name.Type().(*types.Named); !isNamed || named.TypeParams() != nil {
			continue
		}
		every := true
		for method := range name.Type().Underlying().(*types.Interface).Methods() {
			every = every && pv.entryFor(method.FullName()) != nil
		}
		if !every || pv.hasStates(name.Type()) || scopedOf(name.Type()) != nil {
			continue
		}
		pv.optional[optionalKey(name)] = name
	}
	return pv.optional
}

// optionalKey is how messages and records name a member of O.
func optionalKey(name *types.TypeName) string {
	return name.Pkg().Path() + "." + name.Name()
}

// optionalOf returns O_S for a static type: the members of O whose
// package is in the build of the package that declares it, in the order
// of their keys. A type that is not a defined interface has none.
func (pv *pkgVerifier) optionalOf(s types.Type) []*types.TypeName {
	named, ok := types.Unalias(s).(*types.Named)
	if !ok || !isIface(s) || named.Obj().Pkg() == nil {
		return nil
	}
	declaring := named.Obj().Pkg()
	var members []*types.TypeName
	for _, key := range slices.Sorted(maps.Keys(pv.optionalSet())) {
		x := pv.optional[key]
		if packageOf(declaring, x.Pkg().Path()) != nil {
			members = append(members, x)
		}
	}
	return members
}

// Two notions decide what F35 does with a static type S (F14 of the review
// of S1). S is O-shaped when it has, for some X in O_S, a method of the
// name and signature of each method of X: a conversion to an O-shaped type
// is checked against O_S, and checking more conversions loses nothing. S
// is O-typed, as ruled, when for some X in O_S each method of X is S's own
// method from X's declaration, or S's method of the name has a contract
// that implies X's, which is proved where it is relied on (proveOTyped):
// the lifts, the source of a conversion between interfaces (F7), and the
// assumption about values from code that is not verified lean on it. So an
// O-typed type has a contracted method that is not Error, which AC refuses
// as the target of an error and which makes a trusted result or written
// memory of it need vouches. An interface without contracts of the shape
// of io.Writer is O-shaped and not O-typed.

// oShaped reports whether a static type is O-shaped.
func (pv *pkgVerifier) oShaped(s types.Type) bool {
	return len(pv.oShapedFor(s)) > 0
}

// oShapedFor returns the members X of O_S whose every method s has by name
// and signature.
func (pv *pkgVerifier) oShapedFor(s types.Type) []*types.TypeName {
	var found []*types.TypeName
	for _, x := range pv.optionalOf(s) {
		all := true
		for method := range x.Type().Underlying().(*types.Interface).Methods() {
			own, _, _ := types.LookupFieldOrMethod(s, false, method.Pkg(), method.Name())
			fn, ok := own.(*types.Func)
			all = all && ok && types.Identical(fn.Type(), method.Type())
		}
		if all {
			found = append(found, x)
		}
	}
	return found
}

// oTyped reports whether a static type is O-typed: for some X in O_S, each
// method of X is s's own from X's declaration, or s's method of the name
// has a contract, which proveOTyped then shows implies X's.
func (pv *pkgVerifier) oTyped(s types.Type) bool {
	return pv.oTypedBy(s) != nil
}

// oTypedBy returns the first member X of O_S by which s is O-typed, or nil.
// One whose every method is s's own from X's declaration comes first,
// since it needs no proof.
func (pv *pkgVerifier) oTypedBy(s types.Type) *types.TypeName {
	var byContract *types.TypeName
	for _, x := range pv.oShapedFor(s) {
		same, contracted := true, true
		for method := range x.Type().Underlying().(*types.Interface).Methods() {
			own, _, _ := types.LookupFieldOrMethod(s, false, method.Pkg(), method.Name())
			fn, _ := own.(*types.Func)
			same = same && fn == method
			contracted = contracted && (fn == method || pv.methodContract(fn) != nil)
		}
		switch {
		case same:
			return x
		case contracted && byContract == nil:
			byContract = x
		}
	}
	return byContract
}

// hasMethodsOf reports whether s has each method of x, from x's
// declaration or under a contract, as oTypedBy asks of a member of O_S.
func (pv *pkgVerifier) hasMethodsOf(s types.Type, x *types.TypeName) bool {
	for method := range x.Type().Underlying().(*types.Interface).Methods() {
		own, _, _ := types.LookupFieldOrMethod(s, false, method.Pkg(), method.Name())
		fn, ok := own.(*types.Func)
		if !ok || !types.Identical(fn.Type(), method.Type()) || fn != method && pv.methodContract(fn) == nil {
			return false
		}
	}
	return true
}

// oTypedByDeclaration reports whether s is O-typed by a member X of O_S
// each of whose methods s has from X's declaration, which needs no proof.
func (pv *pkgVerifier) oTypedByDeclaration(s types.Type) bool {
	x := pv.oTypedBy(s)
	if x == nil {
		return false
	}
	for method := range x.Type().Underlying().(*types.Interface).Methods() {
		own, _, _ := types.LookupFieldOrMethod(s, false, method.Pkg(), method.Name())
		if own != method {
			return false
		}
	}
	return true
}

// proveOTyped proves, where a lift or a conversion leans on s being
// O-typed by a member X whose method s has from another declaration, that
// the contract of s's method implies X's entry, as a conversion by
// contract proves it (convertByContract); a method of covered is proved
// there already. A failure is reported where it is relied on.
func (v *fnVerifier) proveOTyped(e ast.Expr, s types.Type, covered types.Type, st *state, guard []*logic.Term) {
	x := v.oTypedBy(s)
	if x == nil {
		return
	}
	var already []*types.Func
	if covered != nil {
		already = slices.Collect(covered.Underlying().(*types.Interface).Methods())
	}
	for method := range x.Type().Underlying().(*types.Interface).Methods() {
		own, _, _ := types.LookupFieldOrMethod(s, false, method.Pkg(), method.Name())
		source, _ := own.(*types.Func)
		if source == method || slices.Contains(already, method) {
			continue
		}
		TA, TB := v.methodContract(source), v.methodContract(method)
		if why := v.claimsNoLess(TA, TB, source, method); why != "" {
			v.unsupported(e.Pos(), fmt.Sprintf("%s, %s %s, is taken to have the methods of %s, which is not supported: %s",
				types.ExprString(e), article(v.shown(s)), v.shown(s), v.shown(x.Type()), why))
		}
		v.impliesMethod(e, TA, TB, source, method, st, guard)
	}
}

// optionalMember returns the member of O_S that declares a method, or nil.
func (pv *pkgVerifier) optionalMember(s types.Type, method *types.Func) *types.TypeName {
	for _, x := range pv.optionalOf(s) {
		if slices.Contains(slices.Collect(x.Type().Underlying().(*types.Interface).Methods()), method) {
			return x
		}
	}
	return nil
}

// optionalCheck is a method of a member of O that a conversion checks a
// value against.
type optionalCheck struct {
	x      *types.TypeName
	method *types.Func
}

// optionalChecks returns what a conversion of a value of the concrete type
// from to the interface want checks beyond want's own methods: for an
// O-typed want, each method of each member of O_want that from implements
// and that want does not have as the same method.
func (pv *pkgVerifier) optionalChecks(from, want types.Type) []optionalCheck {
	if !pv.oShaped(want) {
		return nil
	}
	own := slices.Collect(want.Underlying().(*types.Interface).Methods())
	var checks []optionalCheck
	for _, x := range pv.optionalOf(want) {
		iface := x.Type().Underlying().(*types.Interface)
		if !types.Implements(from, iface) {
			continue
		}
		for method := range iface.Methods() {
			if !slices.Contains(own, method) {
				checks = append(checks, optionalCheck{x: x, method: method})
			}
		}
	}
	return checks
}

// optionalSourceWhy says why a conversion between interfaces from from to
// an O-typed want cannot be made, or "": the value was checked, assumed,
// or vouched under from, so from must be O-typed itself, and every member
// of want's O must be one of from's, or a value would come to want that
// nobody checked against what want's users may assert it to (F7 of the
// design review of F35).
func (pv *pkgVerifier) optionalSourceWhy(from, want types.Type) string {
	if !pv.oShaped(want) {
		return ""
	}
	shown := func(t types.Type) string { return types.TypeString(t, types.RelativeTo(pv.pass.Pkg)) }
	if !pv.oTyped(from) {
		// What code given a want may assert it to and use, beyond want's
		// own methods.
		own := slices.Collect(want.Underlying().(*types.Interface).Methods())
		var beyond []string
		for _, x := range pv.optionalOf(want) {
			for method := range x.Type().Underlying().(*types.Interface).Methods() {
				if !slices.Contains(own, method) {
					beyond = append(beyond, shown(x.Type()))
					break
				}
			}
		}
		asserted := "the interfaces whose every method has a trust entry"
		if len(beyond) > 0 {
			asserted = strings.Join(beyond, " and ")
		}
		// A source that has the methods of a member of O, from its
		// declaration or under a contract, whose O lacks it: the member's
		// package is not in the build of the package that declares it (F18
		// of the review of S1).
		for _, key := range slices.Sorted(maps.Keys(pv.optionalSet())) {
			x := pv.optional[key]
			if slices.Contains(pv.optionalOf(from), x) || !pv.hasMethodsOf(from, x) {
				continue
			}
			named, ok := types.Unalias(from).(*types.Named)
			if !ok || named.Obj().Pkg() == nil {
				break
			}
			return fmt.Sprintf("code given %s %s may assert it to %s and use what it finds, and %s has the methods of %s, but package %s, which declares %s, does not have package %s in its build, "+
				"so the values of %s were never checked against what %s is checked against", article(shown(want)), shown(want), asserted, shown(from), shown(x.Type()),
				named.Obj().Pkg().Path(), shown(from), x.Pkg().Path(), shown(from), shown(want))
		}
		return fmt.Sprintf("code given %s %s may assert it to %s and use what it finds, as io.WriteString asserts its writer to io.StringWriter, "+
			"and %s does not have every method of an interface whose every method has a trust entry from its declaration or under a contract that implies the entry, so its values "+
			"were never checked, assumed, or vouched for against them",
			article(shown(want)), shown(want), asserted, shown(from))
	}
	have := pv.optionalOf(from)
	for _, x := range pv.optionalOf(want) {
		if !slices.Contains(have, x) {
			return fmt.Sprintf("code given %s %s may assert it to %s, whose package is not in the build of the package that declares %s, so the values of %s were never checked against it",
				article(shown(want)), shown(want), shown(x.Type()), shown(from), shown(from))
		}
	}
	return ""
}

// optionalFinder names, for messages, a function that finds a method of a
// member of O by a type assertion, from the entries that list it under
// asserts, or says what does.
func (pv *pkgVerifier) optionalFinder(x *types.TypeName) string {
	var finders []string
	files := append(slices.Clone(shippedContracts()), pv.projectTrust)
	for _, file := range files {
		if file == nil {
			continue
		}
		for key, entry := range file.entries {
			for _, item := range entry.asserts {
				for _, dest := range item.dests {
					if dest.text == optionalKey(x) || dest.text == x.Pkg().Name()+"."+x.Name() {
						finders = append(finders, key)
					}
				}
			}
		}
	}
	if len(finders) == 0 {
		return "code that asserts it to " + x.Pkg().Name() + "." + x.Name()
	}
	// The function of io whose name says what it does first, then a
	// function of a package before a method.
	if slices.Contains(finders, "io.WriteString") {
		return "io.WriteString"
	}
	sort.Slice(finders, func(i, j int) bool {
		a, b := strings.HasPrefix(finders[i], "("), strings.HasPrefix(finders[j], "(")
		if a != b {
			return b
		}
		return finders[i] < finders[j]
	})
	return finders[0]
}

// checkOptional checks a value converted from the concrete type from to
// the O-typed interface want against the members of O_want its type
// implements (optionalChecks); held is the value as converted. A method of
// a type of another module that passed once in the package, in a verifier
// that knew nothing of its receiver, is not checked again (D6).
func (v *fnVerifier) checkOptional(e ast.Expr, held value, from, want types.Type, checks []optionalCheck, st *state, guard []*logic.Term) {
	shown := func(t types.Type) string { return types.TypeString(t, types.RelativeTo(v.pass.Pkg)) }
	for _, c := range checks {
		xShown := shown(c.x.Type())
		concrete, why := concreteMethod(from, c.method.Pkg(), c.method.Name(), v.pass.Pkg)
		why = strings.TrimPrefix(why, shown(from)+" ")
		reason := fmt.Sprintf("%s implements %s, whose method %s has an entry that %s relies on of every value it finds it on, and a value converted to %s may be handed to it",
			shown(from), xShown, c.method.Name(), v.optionalFinder(c.x), shown(want))
		if why != "" {
			v.unsupported(e.Pos(), fmt.Sprintf("converting %s %s to %s is not supported: %s; %s %s; rename the method, or give %s a method %s of its own that meets the entry",
				article(shown(from)), shown(from), shown(want), reason, shown(from), why, shown(from), c.method.Name()))
		}
		if v.contractOf(concrete) == nil {
			recv := concrete.Type().(*types.Signature).Recv().Type()
			v.unsupported(e.Pos(), fmt.Sprintf("converting %s %s to %s is not supported: %s; %s has no contract; annotate it with // @ annotations that meet the entry of %s, or rename it",
				article(shown(from)), shown(from), shown(want), reason, methodOf(recv, concrete, v.pass.Pkg), c.method.FullName()))
		}
		// A method of a type of another module that passed once in the
		// package, knowing nothing of its receiver, passes here (D6).
		if passed, done := v.pkgVerifier.optionalPassedAt[optionalPair{concrete, c.method}]; done && passed && !v.pkgVerifier.inAnalysedModule(concrete.Pkg(), concrete.Pos()) {
			continue
		}
		remedy := fmt.Sprintf("meet the entry of %s, or rename the method", c.method.FullName())
		if !v.pkgVerifier.inAnalysedModule(concrete.Pkg(), concrete.Pos()) {
			remedy = fmt.Sprintf("the method is of another module, so convert only a value of which its entry gives what the entry of %s needs", c.method.FullName())
		}
		v.madeMethod(e, held, from, c.x.Type(), c.method, fmt.Sprintf(", which %s implements: %s finds %s by a type assertion; %s",
			shown(from), v.optionalFinder(c.x), c.method.Name(), remedy), st, guard)
	}
}

// optionalPair keys what precheckOptional answered for a method of a type
// of another module that a conversion checks against the entry of a
// method of a member of O: whether it passed in a verifier that knew
// nothing of its receiver but its type, which then holds at every
// conversion. The answers are found before the functions of the package
// are verified, so that what each function asks does not depend on the
// order they are verified in.
type optionalPair struct {
	concrete, method *types.Func
}

// precheckOptional checks, once in the package, each method of a type of
// another module that a conversion of the package checks against a member
// of O, in a verifier of its own that knows nothing of the receiver but
// its type (D6 of the design of F35). A check that passes there holds in
// every state: what a conversion knows only adds hypotheses. One that
// fails is checked again at each conversion, where it reports.
func (pv *pkgVerifier) precheckOptional() {
	pv.optionalPassedAt = map[optionalPair]bool{}
	// A package without annotated functions verifies nothing, so it
	// checks no conversion.
	if !slices.ContainsFunc(pv.order, (*funcInfo).annotated) {
		return
	}
	found := pv.findConversions()
	exprs := slices.Collect(func(yield func(ast.Expr) bool) {
		for e := range found.converted {
			if !yield(e) {
				return
			}
		}
	})
	slices.SortFunc(exprs, func(a, b ast.Expr) int { return int(a.Pos() - b.Pos()) })
	for _, e := range exprs {
		from := pv.info.TypeOf(e)
		// A buffer or a bufio type is refused at a conversion to an
		// interface whose methods write behind its receiver, which every
		// member of O that it implements has, before its methods are
		// checked.
		if from == nil || types.IsInterface(from) || growsUnbounded(from) != "" || wrapsKept(from) != "" {
			continue
		}
		for _, want := range found.converted[e] {
			if !isIface(want) {
				continue
			}
			for _, c := range pv.optionalChecks(from, want) {
				concrete, why := concreteMethod(from, c.method.Pkg(), c.method.Name(), pv.pass.Pkg)
				if why != "" || pv.inAnalysedModule(concrete.Pkg(), concrete.Pos()) || pv.contractOf(concrete) == nil {
					continue
				}
				pair := optionalPair{concrete, c.method}
				if _, done := pv.optionalPassedAt[pair]; done {
					continue
				}
				pv.optionalPassedAt[pair] = pv.precheckOne(e, from, c)
			}
		}
	}
}

// precheckOne runs the check of one method against one entry knowing
// nothing of the receiver, with what it would report captured: it passes
// when nothing is.
func (pv *pkgVerifier) precheckOne(e ast.Expr, from types.Type, c optionalCheck) bool {
	shown := func(t types.Type) string { return types.TypeString(t, types.RelativeTo(pv.pass.Pkg)) }
	concrete, _ := concreteMethod(from, c.method.Pkg(), c.method.Name(), pv.pass.Pkg)
	recv := concrete.Type().(*types.Signature).Recv().Type()
	var captured []string
	saved := pv.capturing
	pv.capturing = &captured
	name := methodOf(recv, concrete, pv.pass.Pkg) + " as a method of " + shown(c.x.Type())
	pv.run(&funcInfo{obj: types.NewFunc(token.NoPos, pv.pass.Pkg, name, types.NewSignatureType(nil, nil, nil, nil, nil, false))}, func(v *fnVerifier) {
		st := &state{vals: map[*types.Var]value{}, mem: memory{}, brk: logic.Const("brk", logic.Ref), noted: map[string]bool{}}
		v.entryBrk = st.brk
		st.assume(logic.Le(logic.IntLit(1), st.brk))
		held := v.unknown("held", from, st)
		v.madeMethod(e, held, from, c.x.Type(), c.method, "", st, nil)
	})
	pv.capturing = saved
	return len(captured) == 0
}

// optionalUse is what the package records of the trust files it reads for
// D5: the keys of every type to whose methods an entry gives a contract,
// by receiver as written, with the file of each, and those that resolve in
// the build to a type that is not an interface.
func (pv *pkgVerifier) optionalUse() OptionalUse {
	use := OptionalUse{Package: pv.pass.Pkg.Path()}
	files := map[string]string{}
	collect := func(file *trustFile, name string) {
		for key := range file.entries {
			receiver, _, isMethod := strings.Cut(strings.TrimPrefix(key, "("), ").")
			if isMethod && strings.HasPrefix(key, "(") && !strings.HasPrefix(receiver, "*") {
				if _, done := files[receiver]; !done {
					files[receiver] = name
				}
			}
		}
	}
	for _, file := range shippedContracts() {
		collect(file, "the shipped files")
	}
	if pv.projectTrust != nil {
		collect(pv.projectTrust, pv.projectTrust.path)
	}
	for _, key := range slices.Sorted(maps.Keys(files)) {
		use.Keys = append(use.Keys, key)
		use.Files = append(use.Files, files[key])
		dot := strings.LastIndex(key, ".")
		if dot < 0 {
			continue
		}
		if pkg := packageOf(pv.pass.Pkg, strings.Trim(key[:dot], `"`)); pkg != nil {
			if name, ok := pkg.Scope().Lookup(key[dot+1:]).(*types.TypeName); ok && !types.IsInterface(name.Type()) {
				use.Concrete = append(use.Concrete, key)
			}
		}
	}
	return use
}

// shown writes a type as messages of the package do.
func (pv *pkgVerifier) shown(t types.Type) string {
	return types.TypeString(t, types.RelativeTo(pv.pass.Pkg))
}

// behindParamWhy says why a function entry cannot list behind(p) for a
// parameter, or "" when it can (F20 of the review of S2 of F35). behind(p)
// claims that the call writes the footprint of what p holds and changes
// none of its states. It may be claimed only where the entry's runs and
// asserts confine the calls on p to methods that change no state: p must
// be an interface value whose type has no states, listed under runs, the
// types listed for it under asserts must be interfaces, and every method
// of every interface that they and p's type reach must belong to an
// interface without states, as Write, Read, and WriteString do; nothing
// reached may be a function value or a pointer with states. What the function calls is the author's claim, held by
// the harness of each shipped entry, whose probes refuse Close and every
// other method the entry does not declare (TestBehindParams).
func (v *fnVerifier) behindParamWhy(fn *funcInfo, param *types.Var) string {
	shown := func(t types.Type) string { return types.TypeString(t, types.RelativeTo(v.pass.Pkg)) }
	name := param.Name()
	switch {
	case !isIface(param.Type()):
		return fmt.Sprintf("behind(%s) names the footprint of an interface value, and %s has type %s; list %s itself", name, name, shown(param.Type()), name)
	case v.hasStates(param.Type()):
		return fmt.Sprintf("behind(%s) claims that the function changes no state of what %s holds, and %s has states, which its methods change; list %s itself", name, name, shown(param.Type()), name)
	case !fn.runs.get(param):
		return fmt.Sprintf("behind(%s) claims what the function calls on %s, which only an entry that lists %s under runs can claim; list %s itself", name, name, name, name)
	}
	called := []types.Type{param.Type()}
	if fn.trust != nil {
		for _, item := range fn.trust.asserts {
			if item.name != name {
				continue
			}
			for _, dest := range item.dests {
				if t, problem := resolveListed(v.pass.Pkg, dest.text); problem == "" {
					called = append(called, t)
				}
			}
		}
	}
	for _, t := range called[1:] {
		if !isIface(t) {
			return fmt.Sprintf("behind(%s) claims that the function changes no state of what %s holds, and its asserts lists %s for %s, a type whose methods it may call; list %s itself", name, name, shown(t), name, name)
		}
	}
	// runs lets the function call the methods of every interface and the
	// function types that what p holds reaches, through fields, elements,
	// pointers, and the results of methods, as beyondStatic walks them
	// (F22 of the review of S2 of F35): each must change no state, and no
	// pointer reached may have states that its own methods change.
	var r reachedTypes
	seen := map[types.Type]bool{}
	for _, t := range called {
		r.walk(t, seen)
	}
	for _, t := range r.ifaces {
		for method := range t.Underlying().(*types.Interface).Methods() {
			if owner := declaringInterface(method); owner == nil || v.hasStates(owner.Type()) {
				if !types.Identical(t, param.Type()) {
					return fmt.Sprintf("behind(%s) claims that the function changes no state of what %s holds, and what %s holds reaches %s, whose method %s it may call, a method of an interface with states; list %s itself",
						name, name, name, shown(t), method.Name(), name)
				}
				return fmt.Sprintf("behind(%s) claims that the function changes no state of what %s holds, and it may call %s, a method of an interface with states; list %s itself",
					name, name, methodTitle(method), name)
			}
		}
	}
	if len(r.funcs) > 0 {
		return fmt.Sprintf("behind(%s) claims that the function changes no state of what %s holds, and what %s holds reaches a function value of type %s, which it may call; list %s itself",
			name, name, name, shown(r.funcs[0]), name)
	}
	for _, t := range r.others {
		for _, ptr := range []types.Type{t, types.NewPointer(t)} {
			if _, isPtr := ptr.Underlying().(*types.Pointer); isPtr && len(v.pointerStateOwners(ptr)) > 0 {
				return fmt.Sprintf("behind(%s) claims that the function changes no state of what %s holds, and what %s holds reaches %s, which has states; list %s itself",
					name, name, name, shown(ptr), name)
			}
		}
	}
	return ""
}

// stateHint says, for a clause of a callee's Requires that reads a state of
// what an argument holds, which call may have changed the state when the
// memory is in an epoch that a call started: a call that writes a
// footprint forgets the states of every other value that may lie in it,
// and what a wrapper keeps is not known to be the value it was given
// (Footprints, Not built: following the kept writer into the result). The
// call named is the latest one before which the clause held, found by
// reading it in the memory each epoch started from, walking back; when it
// held before none of them, or the state is known to be the other one, as
// after a Close, nothing is said. The message ends with it only if the
// check fails.
func (v *fnVerifier) stateHint(c *clause, fn *funcInfo, args map[*types.Var]value, st *state) func(*state, []*logic.Term, *logic.Term) string {
	reads := false
	params := slices.Clone(fn.params)
	if fn.receiver != nil {
		params = append(params, fn.receiver)
	}
	for _, param := range params {
		if args[param] == nil {
			continue
		}
		for _, s := range v.ifaceStatesOf(param.Type()) {
			reads = reads || strings.Contains(c.text, s.name+"(")
		}
	}
	if e := st.mem[epochKey]; !reads || e == nil || v.epochs[e.Name] == nil {
		return nil
	}
	return func(st *state, guard []*logic.Term, conjunct *logic.Term) string {
		if v.attempt(st, guard, logic.Not(conjunct)) == solver.Proved {
			return ""
		}
		// A few epochs back at most: the hint is for the call just before.
		e := st.mem[epochKey]
		for range 8 {
			if e == nil || v.epochs[e.Name] == nil {
				return ""
			}
			ep := v.epochs[e.Name]
			then := st.clone()
			if v.attempt(then, guard, v.formula(c, c.node, &specEnv{v: v, sink: then, fn: fn, args: args, now: ep.before})) == solver.Proved {
				if ep.by == "" {
					return ""
				}
				return fmt.Sprintf("; the state may have been changed by %s, which writes through what it is handed or what a value it is handed keeps, and nothing says that "+
					"what it writes through is not this value, so its states count as those of another value, which a write may change; close or use the value "+
					"only where nothing was written through what keeps it since its state was known, or write to the value itself", ep.by)
			}
			e = ep.before[epochKey]
		}
		return ""
	}
}
