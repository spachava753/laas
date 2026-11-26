package vego

import (
	"fmt"
	"go/token"
	"go/types"
	"math/big"
	"slices"

	"github.com/spachava753/laas/vego/internal/logic"
)

// contractFact carries the contract of a verified function to the packages
// that import its package, so that they can call it without trusting it.
type contractFact struct {
	Requires []string
	Ensures  []string
	// Modifies lists what the function may write, as its Modifies clauses
	// spell it.
	Modifies []string
	// Exits is set when the function may end the process without
	// returning, as its Exits annotation says; see exits.go.
	Exits bool
	// Excused is set when the function may fail unpredictably; see
	// reportAlwaysFailing.
	Excused bool
	// Verified is cleared when verification of the function, or of a
	// function of its package that its proof relies on, reported a problem.
	// Its contract is then not established and must not be used.
	Verified bool
	// KnownErrors is set when every error the function returns has a known
	// origin, made or vouched, so that formatting it runs no unknown code;
	// see knownError.
	KnownErrors bool
	// Consts holds the values of the package constants the contract
	// mentions, so that it means the same in every package that reads it.
	Consts map[string]string
	// Errors holds, by how the contract spells them, the keys of the
	// package-level variables it mentions, errors and others; see errorKey.
	Errors map[string]string
	// Packages holds, by the name the contract's file imports it as, the
	// path of each package whose state a Modifies clause names.
	Packages map[string]string
	// Types holds, by how the contract spells them, the keys of the types
	// it names (see typeKeyOf), and under "const " and the name the types
	// of the constants it mentions that have a defined type, so that
	// holds(err, ParseError) and err = ErrSyntax mean the same in every
	// package that reads it.
	Types map[string]string
	// CallsValues is set when running the function may make a call through
	// a function value, itself or in what it calls; see mayCallValues.
	CallsValues bool
	// Receiver names the receiver of the contract of a method of an
	// interface, if it names one.
	Receiver string
	// Vouches names the error results whose errors the contract of a
	// type vouches for; see addVouches. Every package that calls through
	// a value of the type, or makes one, reads it from here.
	Vouches []string
	// DerivedResults is set when every result of the function that holds
	// memory is new or reached from its arguments, and DerivedStores when
	// what it stores into memory is; see memSummary.
	DerivedResults bool
	DerivedStores  bool
	// OwnKeeps says, for each parameter, the receiver first, whether the
	// function may keep it, and OwnResults what each result is, by the
	// analysis of ownership (ownSummary). Nil when it has none.
	OwnKeeps   []bool
	OwnResults []OwnResultFact
}

// OwnResultFact is ownResultFact as it travels.
type OwnResultFact struct {
	Fresh   bool
	From    []int
	Inside  []int
	Unknown bool
}

func (*contractFact) AFact() {}

func (f *contractFact) String() string {
	return fmt.Sprintf("contract(%d requires, %d ensures, verified=%t)", len(f.Requires), len(f.Ensures), f.Verified)
}

// predicatesFact carries the predicate definitions of a package, which the
// contracts of its functions may use.
type predicatesFact struct {
	Decls []string
	// Broken is set when a definition of the package was not accepted.
	Broken bool
}

func (*predicatesFact) AFact() {}

func (f *predicatesFact) String() string { return fmt.Sprintf("predicates(%d)", len(f.Decls)) }

// exportContracts publishes the contracts of the exported functions that
// were verified, and the package's predicates.
func (pv *pkgVerifier) exportContracts(excused map[*funcInfo]bool) {
	if len(pv.predicateTexts) > 0 || pv.predicatesBroken {
		pv.pass.ExportPackageFact(&predicatesFact{Decls: pv.predicateTexts, Broken: pv.predicatesBroken})
	}
	// A proof that used the contract of a function whose own proof failed
	// establishes nothing, so failure spreads from callee to caller until
	// nothing changes; that covers recursion and any order of declaration.
	unverified := map[*funcInfo]bool{}
	for changed := true; changed; {
		changed = false
		for _, fn := range pv.order {
			result := pv.outcomes[fn]
			failed := result == nil || !result.complete || fn.failed || fn.broken || pv.predicatesBroken || pv.unread ||
				(fn.annotated() && slices.ContainsFunc(pv.spreadCallees(fn), func(callee *funcInfo) bool { return unverified[callee] }))
			if fn.annotated() && failed && !unverified[fn] {
				unverified[fn], changed = true, true
			}
		}
	}
	for _, fn := range pv.order {
		if !fn.annotated() || !fn.obj.Exported() {
			continue
		}
		fact := pv.contractFactOf(fn, fn.decl.Pos())
		fact.Excused, fact.Verified, fact.KnownErrors = excused[fn], !unverified[fn], pv.knownReturns[fn]
		fact.CallsValues = pv.mayCallValues(fn.obj)
		summary := pv.memSummary(fn.obj)
		fact.DerivedResults, fact.DerivedStores = summary.results, summary.stores
		if own := pv.ownSummaryOf(fn); own != nil {
			fact.OwnKeeps = own.keeps
			for _, r := range own.results {
				fact.OwnResults = append(fact.OwnResults, OwnResultFact{Fresh: r.fresh, From: r.from, Inside: r.inside, Unknown: r.unknown})
			}
		}
		pv.pass.ExportObjectFact(fn.obj, fact)
	}
}

// contractFactOf records the clauses of a contract written in this package
// as a fact, with the values of the constants they mention and the keys of
// the error variables, as they are seen at a position.
func (pv *pkgVerifier) contractFactOf(fn *funcInfo, at token.Pos) *contractFact {
	fact := &contractFact{Consts: map[string]string{}, Errors: map[string]string{}, Packages: map[string]string{}, Types: map[string]string{}}
	// The constants a contract mentions are recorded with their
	// values, and the error variables with their keys.
	scope := pv.pass.Pkg.Scope().Innermost(at)
	// typeNamed records the key of a type the contract names.
	typeNamed := func(t *logic.TypeName) {
		var obj types.Object
		switch {
		case t.Quoted:
			return
		case t.Qualifier != "":
			if _, pkg := scope.LookupParent(t.Qualifier, at); pkg != nil {
				if name, ok := pkg.(*types.PkgName); ok {
					obj = name.Imported().Scope().Lookup(t.Name)
				}
			}
		default:
			_, obj = scope.LookupParent(t.Name, at)
		}
		if name, ok := obj.(*types.TypeName); ok {
			if key := typeKeyOf(name.Type()); key != "" {
				spelled := t.Name
				if t.Qualifier != "" {
					spelled = t.Qualifier + "." + t.Name
				}
				fact.Types[spelled] = key
			}
		}
	}
	var visit func(n *logic.Node)
	visit = func(n *logic.Node) {
		if constant, ok := pv.pass.Pkg.Scope().Lookup(n.Name).(*types.Const); ok && n.Kind == logic.NIdent {
			if literal, ok := literalOf(constant.Val()); ok {
				fact.Consts[n.Name] = literal.String()
			}
			if key := typeKeyOf(constant.Type()); key != "" {
				fact.Types["const "+n.Name] = key
			}
		}
		if n.Type != nil {
			typeNamed(n.Type)
		}
		if n.Kind == logic.NCall {
			typeNamed(&logic.TypeName{Name: n.Name})
		}
		if _, obj := scope.LookupParent(n.Name, at); n.Kind == logic.NIdent && obj != nil {
			if variable := packageVariableOf(obj, ""); variable != nil {
				fact.Errors[n.Name] = errorKey(variable)
			}
			if name, ok := obj.(*types.PkgName); ok {
				fact.Packages[n.Name] = name.Imported().Path()
			}
		}
		if n.Kind == logic.NField && n.Kids[0].Kind == logic.NIdent {
			if _, obj := scope.LookupParent(n.Kids[0].Name, at); obj != nil {
				if pkg, ok := obj.(*types.PkgName); ok {
					if constant, ok := pkg.Imported().Scope().Lookup(n.Name).(*types.Const); ok && constant.Exported() {
						spelled := n.Kids[0].Name + "." + n.Name
						if literal, ok := literalOf(constant.Val()); ok {
							fact.Consts[spelled] = literal.String()
						}
						if key := typeKeyOf(constant.Type()); key != "" {
							fact.Types["const "+spelled] = key
						}
					}
				}
				if variable := packageVariableOf(obj, n.Name); variable != nil {
					fact.Errors[n.Kids[0].Name+"."+n.Name] = errorKey(variable)
				}
			}
		}
		for _, kid := range n.Kids {
			visit(kid)
		}
	}
	capture := func(c *clause) string {
		if c.node != nil {
			visit(c.node)
		}
		return c.text
	}
	for _, c := range fn.requires {
		fact.Requires = append(fact.Requires, capture(c))
	}
	for _, c := range fn.ensures {
		fact.Ensures = append(fact.Ensures, capture(c))
	}
	for _, m := range fn.modifies {
		fact.Modifies = append(fact.Modifies, m.text)
		// The root of a path may be a package or a variable of one.
		root := &logic.Node{Kind: logic.NIdent, Name: m.name}
		visit(root)
		if len(m.steps) > 0 && m.steps[0].field != "" {
			visit(&logic.Node{Kind: logic.NField, Name: m.steps[0].field, Kids: []*logic.Node{root}})
		}
		// The indices of a path may mention constants too.
		for _, step := range m.steps {
			if step.index != nil {
				visit(step.index)
			}
		}
	}
	if fn.receiver != nil {
		fact.Receiver = fn.receiver.Name()
	}
	fact.Exits = fn.exits
	for i := range fn.results {
		if fn.vouches[i] {
			fact.Vouches = append(fact.Vouches, spelledResult(fn, i))
		}
	}
	return fact
}

// importedContract returns the contract of a function that was verified in
// another package, or nil when that package published none for it.
func (pv *pkgVerifier) importedContract(callee *types.Func) *funcInfo {
	if fn, done := pv.imported[callee]; done {
		return fn
	}
	pv.imported[callee] = nil
	fact := &contractFact{}
	if callee.Pkg() == nil || callee.Pkg() == pv.pass.Pkg || !pv.pass.ImportObjectFact(callee, fact) {
		return nil
	}
	fn := pv.contractFromFact(callee, callee.Pkg(), fact)
	pv.imported[callee] = fn
	return fn
}

// contractFromFact builds the contract that another package published for
// one of its functions or function types, whose signature obj has.
func (pv *pkgVerifier) contractFromFact(obj *types.Func, pkg *types.Package, fact *contractFact) *funcInfo {
	fn := newFuncInfo(obj)
	fn.imported = fact
	if !fact.Verified {
		fn.defect("its verification failed in package %s", pkg.Path())
		return fn
	}
	resolver := pv.foreignResolver(pkg)
	if pv.foreignBroken[pkg] {
		fn.defect("the predicates of package %s could not be understood", pkg.Path())
		return fn
	}
	clauses := func(kind string, texts []string) []*clause {
		var list []*clause
		for _, text := range texts {
			node, err := logic.ParseFormula(text)
			if err != nil {
				fn.defect("its %s %q cannot be read: %v", kind, text, err)
				continue
			}
			list = append(list, &clause{kind: kind, text: text, node: node, pos: obj.Pos(), res: resolver})
		}
		return list
	}
	fn.requires, fn.ensures = clauses("Requires", fact.Requires), clauses("Ensures", fact.Ensures)
	fn.exits = fact.Exits
	for _, name := range fact.Vouches {
		index, isResult := fn.resultNames[name]
		if !isResult {
			fn.defect("its Vouches names %s, which is not a result", name)
			continue
		}
		fn.vouches[index] = true
	}
	for _, text := range fact.Modifies {
		targets, err := logic.ParseTargets(text)
		if err != nil {
			fn.defect("its Modifies %q cannot be read: %v", text, err)
			continue
		}
		fn.modifies = append(fn.modifies, newModTargets(targets, &clause{kind: "Modifies", text: text, pos: obj.Pos(), res: resolver})...)
	}
	return fn
}

// foreignResolver returns a resolver holding the predicates another package
// defined. Their names are prefixed with the package path, so that they
// cannot be confused with predicates of the same name defined here.
func (pv *pkgVerifier) foreignResolver(pkg *types.Package) *logic.Resolver {
	if resolver, ok := pv.foreign[pkg]; ok {
		return resolver
	}
	resolver := logic.NewResolver()
	resolver.Prefix = pkg.Path() + "."
	pv.foreign[pkg] = resolver
	published := &predicatesFact{}
	pv.pass.ImportPackageFact(pkg, published)
	pv.foreignBroken[pkg] = published.Broken
	var decls []*logic.PredDecl
	for _, text := range published.Decls {
		decl, err := logic.ParsePredicate(text)
		if err != nil {
			pv.foreignBroken[pkg] = true
			continue
		}
		decls = append(decls, decl)
	}
	if len(resolver.Define(decls)) > 0 {
		pv.foreignBroken[pkg] = true
	}
	for name, def := range resolver.Preds {
		pv.res.Preds[name] = def
	}
	return resolver
}

// resolverOf returns the resolver an annotation must be read with: that of
// the package it was written in.
func (pv *pkgVerifier) resolverOf(c *clause) *logic.Resolver {
	if c.res != nil {
		return c.res
	}
	return pv.res
}

// contractConstant resolves a name in a contract that is neither a parameter
// nor a result. A contract keeps the meaning it had where it was written: an
// annotation of this package sees this package's constants, an imported one
// the constants its own package recorded, and a trusted one no constants at
// all. All of them see the limits of the integer types unless a constant of
// that name was in scope where they were written.
func (pv *pkgVerifier) contractConstant(fn *funcInfo, name string) (*logic.Term, error) {
	switch {
	case fn.trust != nil:
		return pv.constantNamed(nil, name)
	case fn.imported == nil:
		return pv.constantNamed(pv.pass.Pkg.Scope().Lookup(name), name)
	}
	text, recorded := fn.imported.Consts[name]
	if !recorded {
		return pv.constantNamed(nil, name)
	}
	if number, ok := new(big.Int).SetString(text, 10); ok {
		return logic.BigLit(number), nil
	}
	return logic.BoolLit(text == "True"), nil
}
