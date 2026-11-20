package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"maps"
	"slices"
	"strings"

	"github.com/spachava753/laas/vego/internal/logic"
)

// Which error an error is.
//
// Two errors are equal in the logic when they are the same error. Go's ==
// on two error values agrees with that when one of them is nil, made by
// errors.New or fmt.Errorf, or held by a sentinel: such an error is a
// pointer, so == compares the dynamic types and then the pointers, and
// cannot panic. Two errors of which nothing is known may hold the same
// uncomparable type, and then == panics, so comparing them is not
// supported.
//
// A stable error variable is a package-level variable of type error that
// holds one error for as long as code of its importers runs; see
// findSentinels. It stands for one constant throughout, named by its package
// path and name, or by those of the variable it holds. A sentinel is a
// stable variable that holds the error its declaration made with errors.New
// or fmt.Errorf. Each such call makes a new error, as does each call in a
// verified body, so all of them differ from each other.

// stableKind says how a stable error variable gets its value.
type stableKind int

const (
	// stableMade: its initialiser is a call of errors.New or fmt.Errorf,
	// which makes a new error; the variable is a sentinel.
	stableMade stableKind = iota
	// stableAlias: it holds the value of another package-level error
	// variable, which its initialiser names or a function returns.
	stableAlias
	// stableOpaque: anything else. The variable holds one value, and
	// nothing is known of it but what the static type of its initialiser
	// says.
	stableOpaque
)

// sentinelsFact lists the stable error variables of a package by name, and
// says of every other error variable of the package what changes it. It is
// a fact about the package and not about each variable, since only facts
// about packages reach every package built with this one; a fact about a
// variable reaches only the packages that import its package.
type sentinelsFact struct {
	Vars    map[string]sentinelInfo
	Changed map[string]string
}

// sentinelInfo is what is known of one stable error variable.
type sentinelInfo struct {
	Kind stableKind
	// Alias is the key of the variable an alias holds.
	Alias string
	// NonNil and Comparable say of an opaque variable that it is not nil,
	// and that == on it is identity and cannot panic; see concreteError.
	NonNil, Comparable bool
	// Homemade is set when nothing of unknown origin went into the error.
	Homemade bool
	// Rests holds the keys of the other sentinels that went into the
	// error, however deep, on whose values what is known of it rests.
	Rests []string
	// Tree says what the error wraps, and Wraps names the variable it
	// wraps when it wraps one.
	Tree  wrapping
	Wraps string
}

func (*sentinelsFact) AFact() {}

func (f *sentinelsFact) String() string { return fmt.Sprintf("sentinels(%d)", len(f.Vars)) }

// sentinelWrite is an assignment to an error variable of another package,
// or a place that takes its address.
type sentinelWrite struct {
	// Key names the variable, see errorKey, and Name spells it as the
	// writing package does.
	Key, Name string
	// Package is the path of the package that writes, and At the file and
	// line of the write.
	Package, At string
	// pos is the position of the write, known only in its own package.
	pos token.Pos
}

// sentinelWritesFact lists what a package writes of the error variables of
// other packages.
type sentinelWritesFact struct {
	Writes []sentinelWrite
}

func (*sentinelWritesFact) AFact() {}

func (f *sentinelWritesFact) String() string { return fmt.Sprintf("writes(%d)", len(f.Writes)) }

// sentinelRelianceFact lists the error variables whose value the proofs of
// a package rely on, by key.
type sentinelRelianceFact struct {
	Keys []string
	// Values holds the keys among them of variables that are not errors.
	Values []string
}

func (*sentinelRelianceFact) AFact() {}

func (f *sentinelRelianceFact) String() string { return fmt.Sprintf("relies(%d)", len(f.Keys)) }

// errorKey names a package-level variable by its package path and name.
func errorKey(variable *types.Var) string {
	return variable.Pkg().Path() + "." + variable.Name()
}

// sentinelName begins the names of the constants that stand for sentinels.
const sentinelName = "var "

// isSentinelTerm reports whether a term is the constant of a sentinel.
func isSentinelTerm(t *logic.Term) bool {
	return t.Op == logic.OpConst && t.Sort == logic.Err && strings.HasPrefix(t.Name, sentinelName)
}

// foreignSentinel returns what the package of a variable of another
// package published about it as a stable variable, if anything.
func (pv *pkgVerifier) foreignSentinel(variable *types.Var) (sentinelInfo, bool) {
	fact := pv.publishedBy(variable)
	if fact == nil {
		return sentinelInfo{}, false
	}
	info, ok := fact.Vars[variable.Name()]
	return info, ok
}

// publishedBy returns what the package of a variable of another package
// published about its error variables, or nil.
func (pv *pkgVerifier) publishedBy(variable *types.Var) *sentinelsFact {
	pkg := variable.Pkg()
	if pkg == nil || pkg == pv.pass.Pkg || variable.Parent() != pkg.Scope() || !isError(variable.Type()) {
		return nil
	}
	if pv.published == nil {
		pv.published = map[*types.Package]*sentinelsFact{}
	}
	fact, done := pv.published[pkg]
	if !done {
		fact = new(sentinelsFact)
		if !pv.pass.ImportPackageFact(pkg, fact) {
			fact = nil
		}
		pv.published[pkg] = fact
	}
	return fact
}

// spelling returns the name of a package-level variable as this package
// writes it.
func (pv *pkgVerifier) spelling(variable *types.Var) string {
	if variable.Pkg() != pv.pass.Pkg {
		return variable.Pkg().Name() + "." + variable.Name()
	}
	return variable.Name()
}

// usableSentinel reports whether this package may take a variable to hold
// one error throughout, and why not when it may not. It looks at the
// variable alone; see resolve for the variable an alias holds.
func (pv *pkgVerifier) usableSentinel(variable *types.Var) (sentinelInfo, string) {
	spelled := pv.spelling(variable)
	// What is known of a stable variable of this package, or of another.
	info, isSentinel := pv.candidates[variable]
	if variable.Pkg() != pv.pass.Pkg {
		info, isSentinel = pv.foreignSentinel(variable)
	}
	switch {
	case variable.Pkg() == pv.pass.Pkg && pv.unsettled[variable] != "":
		return info, fmt.Sprintf("%s is not known to have its value yet when this runs: %s while the variables of the package are "+
			"initialised, which may run this function first", spelled, pv.unsettled[variable])
	case variable.Pkg() != pv.pass.Pkg && pv.reassigned[variable]:
		return info, fmt.Sprintf("%s %s in this package, so it is not known to hold the error it was declared with", spelled, pv.changeOf[variable])
	case !isSentinel && variable.Pkg() != pv.pass.Pkg:
		if fact := pv.publishedBy(variable); fact != nil && fact.Changed[variable.Name()] != "" {
			return info, fmt.Sprintf("%s %s in package %s, so it is not known to hold the error it was declared with",
				spelled, fact.Changed[variable.Name()], variable.Pkg().Path())
		}
		return info, fmt.Sprintf("%s is a variable of package %s that is not known to hold the error it was declared with", spelled, variable.Pkg().Path())
	case !isSentinel:
		return info, fmt.Sprintf("%s %s, so it is not known to hold the error it was declared with", spelled, pv.ownChanges[variable])
	}
	// A package this one is built with may change the variable, or one
	// that went into its error, before any of this runs.
	for _, key := range append([]string{errorKey(variable)}, info.Rests...) {
		if write, changed := pv.writtenInBuild()[key]; changed {
			what := spelled
			if key != errorKey(variable) {
				what = fmt.Sprintf("%s, which went into %s,", write.Name, spelled)
			}
			return info, fmt.Sprintf("%s is changed at %s in package %s, which this package is built with, so it is not known to hold "+
				"the error it was declared with", what, write.At, write.Package)
		}
	}
	return info, ""
}

// writtenInBuild returns, by key, a write to an error variable in this
// package or in a package it is built with.
func (pv *pkgVerifier) writtenInBuild() map[string]sentinelWrite {
	if pv.buildWrites != nil {
		return pv.buildWrites
	}
	pv.buildWrites = map[string]sentinelWrite{}
	writes := slices.Clone(pv.writes)
	for _, published := range pv.pass.AllPackageFacts() {
		if fact, ok := published.Fact.(*sentinelWritesFact); ok && published.Package != pv.pass.Pkg {
			writes = append(writes, fact.Writes...)
		}
	}
	slices.SortFunc(writes, func(a, b sentinelWrite) int {
		return strings.Compare(a.Package+" "+a.At, b.Package+" "+b.At)
	})
	for _, write := range writes {
		if _, seen := pv.buildWrites[write.Key]; !seen {
			pv.buildWrites[write.Key] = write
		}
	}
	return pv.buildWrites
}

// stableValue is what a stable variable holds, once aliases are followed:
// the value of final, of which info says what is known, and the keys of
// the variables on which that rests.
type stableValue struct {
	final *types.Var
	info  sentinelInfo
	keys  []string
}

// resolve returns what a variable that this package may read holds, or why
// it may not read it. An alias holds what its target holds. An alias whose
// target cannot be relied on holds the value the target had when the alias
// was initialised, which nothing changes, and of which nothing is known.
func (pv *pkgVerifier) resolve(variable *types.Var) (stableValue, string) {
	return pv.resolveFrom(variable, map[*types.Var]bool{})
}

func (pv *pkgVerifier) resolveFrom(variable *types.Var, seen map[*types.Var]bool) (stableValue, string) {
	info, why := pv.usableSentinel(variable)
	if why != "" {
		return stableValue{}, why
	}
	seen[variable] = true
	key := errorKey(variable)
	switch info.Kind {
	case stableAlias:
		if target := pv.lookupKey(info.Alias); target != nil && !seen[target] {
			if r, why := pv.resolveFrom(target, seen); why == "" {
				r.keys = append([]string{key}, r.keys...)
				return r, ""
			}
		}
		return stableValue{final: variable, info: sentinelInfo{Kind: stableOpaque}, keys: []string{key}}, ""
	case stableMade:
		return stableValue{final: variable, info: info, keys: append([]string{key}, info.Rests...)}, ""
	}
	return stableValue{final: variable, info: info, keys: []string{key}}, ""
}

// homemadeValue returns what a variable holds when it holds a sentinel of
// this package or another into which nothing of unknown origin went, and
// which this package may read.
func (pv *pkgVerifier) homemadeValue(variable *types.Var) (stableValue, bool) {
	r, why := pv.resolve(variable)
	return r, why == "" && r.info.Kind == stableMade && r.info.Homemade
}

// rely records that a proof rests on the values of the variables with the
// given keys.
func (pv *pkgVerifier) rely(keys []string) {
	for _, key := range keys {
		pv.reliedKeys[key] = true
	}
}

// namedVariable returns the variable an expression names: a plain
// identifier, or one qualified by the name of its package.
func (pv *pkgVerifier) namedVariable(e ast.Expr) *types.Var {
	e = ast.Unparen(e)
	if sel, ok := e.(*ast.SelectorExpr); ok {
		if x, isIdent := sel.X.(*ast.Ident); !isIdent || !pv.isPackageName(x) {
			return nil
		}
		e = sel.Sel
	}
	id, ok := e.(*ast.Ident)
	if !ok {
		return nil
	}
	variable, _ := pv.info.Uses[id].(*types.Var)
	return variable
}

// isPackageName reports whether an identifier names an imported package.
func (pv *pkgVerifier) isPackageName(id *ast.Ident) bool {
	_, ok := pv.info.Uses[id].(*types.PkgName)
	return ok
}

// lookupKey finds the variable a key names among the packages this one
// depends on, or nil.
func (pv *pkgVerifier) lookupKey(key string) *types.Var {
	dot := strings.LastIndex(key, ".")
	if dot < 0 {
		return nil
	}
	pkg := pv.lookupPackage(key[:dot])
	if pkg == nil {
		return nil
	}
	variable, _ := pkg.Scope().Lookup(key[dot+1:]).(*types.Var)
	return variable
}

// lookupPackage finds the package with a path among this one and the
// packages it depends on, or nil.
func (pv *pkgVerifier) lookupPackage(path string) *types.Package {
	seen := map[*types.Package]bool{}
	var find func(pkg *types.Package) *types.Package
	find = func(pkg *types.Package) *types.Package {
		if seen[pkg] {
			return nil
		}
		seen[pkg] = true
		if pkg.Path() == path {
			return pkg
		}
		for _, imported := range pkg.Imports() {
			if found := find(imported); found != nil {
				return found
			}
		}
		return nil
	}
	return find(pv.pass.Pkg)
}

// sentinelTerm returns the constant for a package-level error variable that
// is read, or, when it cannot be read, why. The facts that hold of it are
// noted in sink, which may be nil.
func (v *fnVerifier) sentinelTerm(sink *state, variable *types.Var) (*logic.Term, string) {
	r, why := v.resolve(variable)
	if why != "" {
		return nil, why
	}
	v.rely(r.keys)
	info := r.info
	sentinel := logic.Const(sentinelName+errorKey(r.final), logic.Err)
	if info.Kind != stableMade {
		v.noteOpaque(sink, sentinel, info.NonNil)
		return sentinel, ""
	}
	v.noteError(sink, sentinel)
	// Only the tree of an error into which nothing of unknown origin went
	// is a matter of the standard library alone.
	switch {
	case !info.Homemade:
	case info.Tree == wrapsNothing:
		v.noteTree(sink, errorTree{err: sentinel})
	case info.Tree == wrapsOperand:
		if wrapped := v.lookupKey(info.Wraps); wrapped != nil {
			if inner, why := v.sentinelTerm(sink, wrapped); why == "" {
				v.noteTree(sink, errorTree{err: sentinel, wraps: inner})
			}
		}
	}
	return sentinel, ""
}

// noteError records an error that is new or held by a sentinel: it is not
// nil, and differs from every other such error the function has met. The
// facts are noted in sink, which may be nil, and those about inputs alone
// also in the background of the function.
func (v *fnVerifier) noteError(sink *state, made *logic.Term) {
	if !slices.ContainsFunc(v.distinct, func(known *logic.Term) bool { return known.Name == made.Name }) {
		v.distinct = append(v.distinct, made)
	}
	if sink == nil || sink.noted["error "+made.Name] {
		return
	}
	sink.noted["error "+made.Name] = true
	v.fact(sink, logic.Not(logic.IsNil(made)))
	for _, other := range v.distinct {
		if other.Name != made.Name {
			v.fact(sink, logic.Not(logic.Eq(made, other)))
		}
	}
}

// noteOpaque records the value of an opaque variable: it is not nil when
// its type says so, and it differs from every error made in the body,
// which is a new allocation, while the variable has held its value since
// the package was initialised. It is not known to differ from a sentinel,
// whose error it may hold.
func (v *fnVerifier) noteOpaque(sink *state, value *logic.Term, nonNil bool) {
	if !slices.ContainsFunc(v.opaqueErrors, func(known *logic.Term) bool { return known.Name == value.Name }) {
		v.opaqueErrors = append(v.opaqueErrors, value)
	}
	if sink == nil || sink.noted["opaque "+value.Name] {
		return
	}
	sink.noted["opaque "+value.Name] = true
	if nonNil {
		v.fact(sink, logic.Not(logic.IsNil(value)))
	}
	for _, made := range v.madeHere {
		v.fact(sink, logic.Not(logic.Eq(made, value)))
	}
}

// fact assumes in a state something that is true in every state Go has.
// One that speaks of inputs alone is also part of the background of the
// function, from which a sample input must be shown to meet it.
func (v *fnVerifier) fact(sink *state, fact *logic.Term) {
	sink.assume(fact)
	if note := fact.String(); v.inputsOnly(fact) && !v.backgroundSeen[note] {
		v.backgroundSeen[note] = true
		v.background = append(v.background, fact)
	}
}

// knownFacts returns what is known of every input without looking at it:
// the facts about the sample errors, and the background of the function.
func (v *fnVerifier) knownFacts() []*logic.Term {
	return append(sampleErrorFacts(), v.background...)
}

// noteIs adds, for every application of is in a term that does not depend
// on a quantified variable, what errors.Is reports when one of the two is
// nil: it then reports whether the other is nil too, without calling a
// method of either.
func (v *fnVerifier) noteIs(sink *state, t *logic.Term) {
	if sink == nil {
		return
	}
	seen := map[*logic.Term]bool{}
	var walk func(t *logic.Term)
	walk = func(t *logic.Term) {
		if seen[t] {
			return
		}
		seen[t] = true
		if t.Op == logic.OpIs && !hasBound(t) {
			err, target := t.Args[0], t.Args[1]
			if note := target.String(); !v.targetSeen[note] {
				v.targetSeen[note] = true
				v.isTargets = append(v.isTargets, target)
			}
			for _, tree := range v.trees {
				v.treeInstance(sink, tree, target)
			}
			// errors.Is begins with err == nil || target == nil, so it
			// finds nil only in nil and nothing in nil. That is stated of
			// the error and the target, and of nil and the target, which
			// holds whatever the error is: when the error is a result yet to
			// be chosen, as in the check that a contract can be met, nil is
			// then a choice whose facts are known.
			for _, fact := range []*logic.Term{
				logic.Implies(logic.IsNil(err), logic.Iff(t, logic.IsNil(target))),
				logic.Implies(logic.IsNil(target), logic.Iff(t, logic.IsNil(err))),
				logic.Iff(logic.Is(logic.NilErr(), target), logic.IsNil(target)),
			} {
				if note := "is " + fact.String(); !sink.noted[note] {
					sink.noted[note] = true
					v.fact(sink, fact)
				}
			}
		}
		for _, arg := range t.Args {
			walk(arg)
		}
	}
	walk(t)
}

// comparableError reports whether Go's == on an error expression and any
// other error agrees with equality in the logic and cannot panic: the
// expression is nil, has a known origin, or names a variable that holds a
// sentinel, which is a pointer, or an opaque value whose type makes ==
// identity.
func (v *fnVerifier) comparableError(e ast.Expr) bool {
	// Known origin of either kind makes == identity that cannot panic.
	if v.isNil(e) || v.knownError(v.bodyOrigins(), e, -1, map[*types.Var]bool{}) {
		return true
	}
	variable := v.namedErrorVariable(e)
	if variable == nil {
		return false
	}
	r, why := v.resolve(variable)
	return why == "" && (r.info.Kind == stableMade || r.info.Comparable)
}

// compareErrors evaluates x == y or x != y on two errors.
func (v *fnVerifier) compareErrors(x, y ast.Expr, op token.Token, st *state, guard []*logic.Term, pos token.Pos) *logic.Term {
	v.bothErrors(x, y, pos)
	same := v.errorsEqual(x, y, v.expr(x, st, guard), v.expr(y, st, guard), pos)
	if op == token.NEQ {
		return logic.Not(same)
	}
	return same
}

// bothErrors refuses a comparison of an error with something that is not
// one, such as an interface value, before anything is said of its result.
// Go converts the error to the type of the other operand there, and == then
// compares what the two interface values hold.
func (v *fnVerifier) bothErrors(x, y ast.Expr, pos token.Pos) {
	for _, side := range []ast.Expr{x, y} {
		if !v.isNil(side) && !isError(v.info.TypeOf(side)) {
			v.unsupported(pos, fmt.Sprintf("comparing an error with a value of type %s is not supported", v.info.TypeOf(side)))
		}
	}
}

// errorsEqual returns whether two evaluated errors are equal, after making
// sure that Go's == on them is equality and cannot panic.
func (v *fnVerifier) errorsEqual(x, y ast.Expr, a, b *logic.Term, pos token.Pos) *logic.Term {
	v.bothErrors(x, y, pos)
	if !v.comparableError(x) && !v.comparableError(y) {
		v.unsupported(pos, "comparing two errors can panic when both hold the same uncomparable type; one of them must be nil, "+
			"an error made by errors.New or fmt.Errorf or vouched for by a trusted contract, or a package-level error variable that holds such an error or a pointer, "+
			"integer, string, or boolean, or an array or struct of these")
	}
	return logic.Eq(a, b)
}

// reportSentinelWrites publishes the sentinels the proofs of this package
// relied on, and reports every write to a sentinel that a proof relies on,
// among the packages this one is built with. A package that is built with
// both is where the write and the proof meet, whether or not either is in
// this package; a package with no verified code and none in its
// dependencies relies on nothing and reports nothing.
func (pv *pkgVerifier) reportSentinelWrites() {
	// What is known of a sentinel rests on the sentinels that went into
	// it as well.
	own := pv.reliedKeys
	if len(own) > 0 {
		pv.pass.ExportPackageFact(&sentinelRelianceFact{Keys: slices.Sorted(maps.Keys(own)), Values: slices.Sorted(maps.Keys(pv.reliedValues))})
	}
	values := maps.Clone(pv.reliedValues)
	relying := map[string][]string{}
	for key := range own {
		relying[key] = append(relying[key], pv.pass.Pkg.Path())
	}
	// Only a write of this package has a position here.
	writes := slices.Clone(pv.writes)
	for _, published := range pv.pass.AllPackageFacts() {
		if published.Package == pv.pass.Pkg {
			continue
		}
		switch fact := published.Fact.(type) {
		case *sentinelRelianceFact:
			for _, key := range fact.Keys {
				relying[key] = append(relying[key], published.Package.Path())
			}
			for _, key := range fact.Values {
				values[key] = true
			}
		case *sentinelWritesFact:
			for _, write := range fact.Writes {
				write.pos = token.NoPos
				writes = append(writes, write)
			}
		}
	}
	slices.SortFunc(writes, func(a, b sentinelWrite) int {
		return strings.Compare(a.Package+" "+a.At+" "+a.Key, b.Package+" "+b.At+" "+b.Key)
	})
	for _, write := range writes {
		packages := relying[write.Key]
		if len(packages) == 0 {
			continue
		}
		slices.Sort(packages)
		which := "package " + strings.Join(slices.Compact(packages), " and package ")
		relied := "it being the error it was declared with"
		if values[write.Key] {
			relied = "it holding the value it was declared with"
		}
		if write.pos.IsValid() {
			pv.report(write.pos, "%s may be changed here, but proofs in %s rely on %s", write.Name, which, relied)
			continue
		}
		pv.report(pv.pass.Files[0].Package, "%s is changed at %s in package %s, which this package is built with, but proofs in %s rely on %s",
			write.Name, write.At, write.Package, which, relied)
	}
}
