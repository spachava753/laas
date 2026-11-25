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

// oTyped reports whether a static type is O-typed: for some X in O_S it
// has a method of the name and the signature of each method of X, from
// X's declaration or another. A method from another declaration need not
// imply X's here: what O-typed decides is which conversions are checked
// and which assertions lean on the check, and counting more types checks
// more conversions.
func (pv *pkgVerifier) oTyped(s types.Type) bool {
	return len(pv.oTypedFor(s)) > 0
}

// oTypedFor returns the members X of O_S whose every method s has by name
// and signature.
func (pv *pkgVerifier) oTypedFor(s types.Type) []*types.TypeName {
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
	if !pv.oTyped(want) {
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
	if !pv.oTyped(want) {
		return ""
	}
	shown := func(t types.Type) string { return types.TypeString(t, types.RelativeTo(pv.pass.Pkg)) }
	if !pv.oTyped(from) {
		return fmt.Sprintf("%s has the methods of %s, and %s does not, so its values were never checked against the interfaces that code given %s %s may assert them to, "+
			"as io.WriteString asserts its writer to io.StringWriter", shown(want), shown(pv.oTypedFor(want)[0].Type()), shown(from), article(shown(want)), shown(want))
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
					if dest.text == optionalKey(x) || strings.TrimSuffix(dest.text, "") == x.Pkg().Name()+"."+x.Name() {
						finders = append(finders, key)
					}
				}
			}
		}
	}
	if len(finders) == 0 {
		return "code that asserts it to " + x.Pkg().Name() + "." + x.Name()
	}
	sort.Strings(finders)
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

// noteOptional records the members of O a package counts for a static
// type, where it checks a conversion to it or relies on the check.
func (pv *pkgVerifier) noteOptional(s types.Type) {
	key := types.TypeString(s, nil)
	if pv.optionalUses == nil {
		pv.optionalUses = map[string]OptionalUse{}
	}
	if _, done := pv.optionalUses[key]; done {
		return
	}
	use := OptionalUse{Target: key, Package: pv.pass.Pkg.Path()}
	for _, x := range pv.optionalOf(s) {
		use.Members = append(use.Members, optionalKey(x))
		file := "?"
		for method := range x.Type().Underlying().(*types.Interface).Methods() {
			if entry := pv.entryFor(method.FullName()); entry != nil {
				file = fmt.Sprintf("%s:%d", entry.file.path, entry.line)
				break
			}
		}
		use.Files = append(use.Files, file)
	}
	pv.optionalUses[key] = use
}

// shown writes a type as messages of the package do.
func (pv *pkgVerifier) shown(t types.Type) string {
	return types.TypeString(t, types.RelativeTo(pv.pass.Pkg))
}
