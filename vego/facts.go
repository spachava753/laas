package vego

import (
	"fmt"
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
	// Excused is set when the function may fail unpredictably; see
	// reportAlwaysFailing.
	Excused bool
	// Verified is cleared when verification of the function, or of a
	// function of its package that its proof relies on, reported a problem.
	// Its contract is then not established and must not be used.
	Verified bool
	// KnownErrors is set when every error the function returns was made by
	// errors.New or fmt.Errorf, so that formatting it runs no unknown code.
	KnownErrors bool
	// Consts holds the values of the package constants the contract
	// mentions, so that it means the same in every package that reads it.
	Consts map[string]string
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
				slices.ContainsFunc(fn.callees, func(callee *funcInfo) bool { return unverified[callee] })
			if fn.annotated() && failed && !unverified[fn] {
				unverified[fn], changed = true, true
			}
		}
	}
	for _, fn := range pv.order {
		if !fn.annotated() || !fn.obj.Exported() {
			continue
		}
		fact := &contractFact{Excused: excused[fn], Verified: !unverified[fn], KnownErrors: pv.knownReturns[fn], Consts: map[string]string{}}
		// The constants a contract mentions are recorded with their values.
		var visit func(n *logic.Node)
		visit = func(n *logic.Node) {
			if constant, ok := pv.pass.Pkg.Scope().Lookup(n.Name).(*types.Const); ok && n.Kind == logic.NIdent {
				if literal, ok := literalOf(constant.Val()); ok {
					fact.Consts[n.Name] = literal.String()
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
			// The indices of a path may mention constants too.
			for _, step := range m.steps {
				if step.index != nil {
					visit(step.index)
				}
			}
		}
		pv.pass.ExportObjectFact(fn.obj, fact)
	}
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
	fn := newFuncInfo(callee)
	fn.imported = fact
	pv.imported[callee] = fn
	if !fact.Verified {
		fn.defect("its verification failed in package %s", callee.Pkg().Path())
		return fn
	}
	resolver := pv.foreignResolver(callee.Pkg())
	if pv.foreignBroken[callee.Pkg()] {
		fn.defect("the predicates of package %s could not be understood", callee.Pkg().Path())
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
			list = append(list, &clause{kind: kind, text: text, node: node, pos: callee.Pos(), res: resolver})
		}
		return list
	}
	fn.requires, fn.ensures = clauses("Requires", fact.Requires), clauses("Ensures", fact.Ensures)
	for _, text := range fact.Modifies {
		targets, err := logic.ParseTargets(text)
		if err != nil {
			fn.defect("its Modifies %q cannot be read: %v", text, err)
			continue
		}
		fn.modifies = append(fn.modifies, newModTargets(targets, &clause{kind: "Modifies", text: text, pos: callee.Pos(), res: resolver})...)
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
