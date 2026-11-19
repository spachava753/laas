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
// A sentinel is a package-level error variable that holds the error its
// declaration made with errors.New or fmt.Errorf; see findSentinels. Each
// such call makes a new error, as does each call in a verified body, so all
// of them differ from each other. A sentinel stands for one constant
// throughout, named by its package path and name.

// errorVarFact marks a package-level error variable that holds, from the
// end of the initialisation of its package on, the error its declaration
// made with errors.New or fmt.Errorf.
type errorVarFact struct {
	// Homemade is set when nothing of unknown origin went into the error.
	Homemade bool
}

func (*errorVarFact) AFact() {}

func (f *errorVarFact) String() string { return fmt.Sprintf("error variable(homemade=%t)", f.Homemade) }

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

// isForeignSentinel reports whether a variable is an error variable of
// another package that its package published as a sentinel.
func (pv *pkgVerifier) isForeignSentinel(variable *types.Var) bool {
	return variable.Pkg() != nil && variable.Pkg() != pv.pass.Pkg && variable.Parent() == variable.Pkg().Scope() &&
		isError(variable.Type()) && pv.pass.ImportObjectFact(variable, new(errorVarFact))
}

// importedHomemade reports whether a variable of another package is a
// sentinel into which nothing of unknown origin went, and which this
// package does not write.
func (pv *pkgVerifier) importedHomemade(variable *types.Var) bool {
	fact := new(errorVarFact)
	return variable.Pkg() != nil && variable.Pkg() != pv.pass.Pkg && !pv.reassigned[variable] &&
		pv.pass.ImportObjectFact(variable, fact) && fact.Homemade
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

// isSentinel reports whether a variable is a sentinel that this package
// may read: one of its own, or one of another package that it does not
// write.
func (pv *pkgVerifier) isSentinel(variable *types.Var) bool {
	if variable.Pkg() == pv.pass.Pkg {
		return pv.sentinels[variable]
	}
	return !pv.reassigned[variable] && pv.isForeignSentinel(variable)
}

// lookupKey finds the variable a key names among the packages this one
// depends on, or nil.
func (pv *pkgVerifier) lookupKey(key string) *types.Var {
	dot := strings.LastIndex(key, ".")
	if dot < 0 {
		return nil
	}
	path, name := key[:dot], key[dot+1:]
	seen := map[*types.Package]bool{}
	var find func(pkg *types.Package) *types.Var
	find = func(pkg *types.Package) *types.Var {
		if seen[pkg] {
			return nil
		}
		seen[pkg] = true
		if pkg.Path() == path {
			variable, _ := pkg.Scope().Lookup(name).(*types.Var)
			return variable
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
	spelled := variable.Name()
	if variable.Pkg() != v.pass.Pkg {
		spelled = variable.Pkg().Name() + "." + variable.Name()
	}
	switch {
	case variable.Pkg() == v.pass.Pkg && v.unsettled[variable] != "":
		return nil, fmt.Sprintf("%s is not known to have its value yet when this runs: %s while the variables of the package are "+
			"initialised, which may run this function first", spelled, v.unsettled[variable])
	case variable.Pkg() != v.pass.Pkg && v.reassigned[variable]:
		return nil, fmt.Sprintf("%s is assigned in this package, so it is not known to hold the error it was declared with", spelled)
	case !v.isSentinel(variable) && variable.Pkg() != v.pass.Pkg:
		return nil, fmt.Sprintf("%s is a variable of package %s that is not known to hold the error it was declared with; only a "+
			"package-level error variable initialised with errors.New or fmt.Errorf, and never assigned, can be read", spelled, variable.Pkg().Path())
	case !v.isSentinel(variable):
		return nil, spelled + " is not a local variable of a supported type"
	}
	v.relied[variable] = true
	sentinel := logic.Const(sentinelName+errorKey(variable), logic.Err)
	v.noteError(sink, sentinel)
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
			for _, fact := range []*logic.Term{
				logic.Implies(logic.IsNil(err), logic.Iff(t, logic.IsNil(target))),
				logic.Implies(logic.IsNil(target), logic.Iff(t, logic.IsNil(err))),
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
// expression is nil, has a known origin, or names a sentinel.
func (v *fnVerifier) comparableError(e ast.Expr) bool {
	if v.isNil(e) || v.knownError(v.originsOf(v.fn.decl.Body), e, -1, map[*types.Var]bool{}) {
		return true
	}
	variable := v.namedVariable(e)
	return variable != nil && variable.Parent() == variable.Pkg().Scope() && v.isSentinel(variable)
}

// compareErrors evaluates x == y or x != y on two errors.
func (v *fnVerifier) compareErrors(x, y ast.Expr, op token.Token, st *state, guard []*logic.Term, pos token.Pos) *logic.Term {
	if !isError(v.info.TypeOf(x)) || !isError(v.info.TypeOf(y)) {
		v.unsupported(pos, fmt.Sprintf("comparing an error with a value of type %s is not supported", v.info.TypeOf(y)))
	}
	same := v.errorsEqual(x, y, v.expr(x, st, guard), v.expr(y, st, guard), pos)
	if op == token.NEQ {
		return logic.Not(same)
	}
	return same
}

// errorsEqual returns whether two evaluated errors are equal, after making
// sure that Go's == on them is equality and cannot panic.
func (v *fnVerifier) errorsEqual(x, y ast.Expr, a, b *logic.Term, pos token.Pos) *logic.Term {
	if !v.comparableError(x) && !v.comparableError(y) {
		v.unsupported(pos, "comparing two errors can panic when both hold the same uncomparable type; one of them must be nil, "+
			"a package-level error variable, or an error made by errors.New or fmt.Errorf")
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
	own := map[string]bool{}
	for variable := range pv.relied {
		own[errorKey(variable)] = true
	}
	if len(own) > 0 {
		pv.pass.ExportPackageFact(&sentinelRelianceFact{Keys: slices.Sorted(maps.Keys(own))})
	}
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
		if write.pos.IsValid() {
			pv.report(write.pos, "%s may be changed here, but proofs in %s rely on it being the error it was declared with", write.Name, which)
			continue
		}
		pv.report(pv.pass.Files[0].Package, "%s is changed at %s in package %s, which this package is built with, but proofs in %s rely on "+
			"it being the error it was declared with", write.Name, write.At, write.Package, which)
	}
}
