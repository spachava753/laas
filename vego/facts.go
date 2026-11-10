package vego

import (
	"fmt"
	"go/types"

	"github.com/spachava753/laas/vego/internal/logic"
)

// contractFact carries the contract of a verified function to the packages
// that import its package, so that they can call it without trusting it.
type contractFact struct {
	Requires []string
	Ensures  []string
	// Mutated tells, per parameter, whether the function may write the
	// elements of the slice passed for it.
	Mutated []bool
	// Excused is set when the function may fail unpredictably; see
	// reportAlwaysFailing.
	Excused bool
	// Verified is cleared when verification of the function reported a
	// problem. Its contract is then not established and must not be used.
	Verified bool
}

func (*contractFact) AFact() {}

func (f *contractFact) String() string {
	return fmt.Sprintf("contract(%d requires, %d ensures, verified=%t)", len(f.Requires), len(f.Ensures), f.Verified)
}

// predicatesFact carries the predicate definitions of a package, which the
// contracts of its functions may use.
type predicatesFact struct {
	Decls []string
}

func (*predicatesFact) AFact() {}

func (f *predicatesFact) String() string { return fmt.Sprintf("predicates(%d)", len(f.Decls)) }

// exportContracts publishes the contracts of the exported functions that
// were verified, and the package's predicates.
func (pv *pkgVerifier) exportContracts(excused map[*funcInfo]bool) {
	if len(pv.predicateTexts) > 0 {
		pv.pass.ExportPackageFact(&predicatesFact{Decls: pv.predicateTexts})
	}
	for _, fn := range pv.order {
		if !fn.annotated() || !fn.obj.Exported() || fn.decl.Recv != nil {
			continue
		}
		result := pv.outcomes[fn]
		fact := &contractFact{
			Excused:  excused[fn],
			Verified: result != nil && result.complete && !fn.failed && !fn.broken,
		}
		for _, c := range fn.requires {
			fact.Requires = append(fact.Requires, c.text)
		}
		for _, c := range fn.ensures {
			fact.Ensures = append(fact.Ensures, c.text)
		}
		for _, param := range fn.params {
			fact.Mutated = append(fact.Mutated, pv.mutates(fn, param))
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
	var decls []*logic.PredDecl
	for _, text := range published.Decls {
		if decl, err := logic.ParsePredicate(text); err == nil {
			decls = append(decls, decl)
		}
	}
	resolver.Define(decls)
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
