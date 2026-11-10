package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"slices"

	"github.com/spachava753/laas/vego/internal/logic"
	"github.com/spachava753/laas/vego/internal/solver"
)

// invariantSet holds the invariants declared on a struct type. An invariant
// is short for contract clauses at every boundary: it is assumed on entry
// for each parameter and receiver of the type or of a pointer to it, proved
// on return for the pointers among them and for each result, and proved at
// each call for each argument. Between those points it may be broken. It is
// only ever assumed where a caller has proved it, so it adds no trust.
type invariantSet struct {
	name    *types.TypeName
	clauses []*clause
	// owner gives the clauses their constants: those of this package, or
	// the ones recorded for a type of another package.
	owner *funcInfo
	// broken is set when a declaration could not be read. Nothing can then
	// be verified about the type, here or in a package that imports it.
	broken bool
}

// invariantFact carries the invariants of a type to importing packages.
type invariantFact struct {
	Texts  []string
	Consts map[string]string
	Broken bool
}

func (*invariantFact) AFact() {}

func (f *invariantFact) String() string { return fmt.Sprintf("invariants(%d)", len(f.Texts)) }

// typeDocumented returns the struct type whose declaration a comment group
// documents, if it documents one.
func (pv *pkgVerifier) typeDocumented(file *ast.File, group *ast.CommentGroup) (*types.TypeName, bool) {
	for _, decl := range file.Decls {
		gen, ok := decl.(*ast.GenDecl)
		if !ok || gen.Tok != token.TYPE {
			continue
		}
		for _, spec := range gen.Specs {
			spec := spec.(*ast.TypeSpec)
			if spec.Doc != group && (gen.Doc != group || len(gen.Specs) != 1) {
				continue
			}
			name, _ := pv.info.Defs[spec.Name].(*types.TypeName)
			return name, true
		}
	}
	return nil, false
}

// addInvariant records an invariant written in the doc comment of a type.
func (pv *pkgVerifier) addInvariant(name *types.TypeName, c *clause) {
	_, isStruct := name.Type().Underlying().(*types.Struct)
	named, isNamed := name.Type().(*types.Named)
	switch {
	case c.kind != "Invariant":
		pv.report(c.pos, "%s annotations do not belong on a type; a type can only have Invariant annotations", c.kind)
		return
	case !isStruct || !isNamed || named.TypeParams() != nil:
		pv.report(c.pos, "an Invariant can only be declared on a struct type without type parameters")
		return
	}
	set := pv.invariants[name]
	if set == nil {
		set = &invariantSet{name: name, owner: &funcInfo{}}
		pv.invariants[name] = set
	}
	node, err := logic.ParseFormula(c.text)
	if err != nil {
		pv.report(c.pos, "syntax error in Invariant annotation: %v", err)
		set.broken = true
		return
	}
	c.node = node
	set.clauses = append(set.clauses, c)
}

// invariantsOf returns the invariants that hold of a value of type t at a
// boundary: those of t when it is a struct type with invariants, or of the
// struct t points to. The second result tells the two apart.
func (pv *pkgVerifier) invariantsOf(t types.Type) (set *invariantSet, viaPointer bool) {
	object, viaPointer := pointee(t)
	if !viaPointer {
		object = t
	}
	named, ok := types.Unalias(object).(*types.Named)
	if !ok {
		return nil, false
	}
	name := named.Origin().Obj()
	if set, known := pv.invariants[name]; known {
		return set, viaPointer
	}
	pv.invariants[name] = nil
	published := &invariantFact{}
	if name.Pkg() == nil || name.Pkg() == pv.pass.Pkg || !pv.pass.ImportObjectFact(name, published) {
		return nil, false
	}
	set = &invariantSet{name: name, owner: &funcInfo{imported: &contractFact{Consts: published.Consts}}, broken: published.Broken}
	resolver := pv.foreignResolver(name.Pkg())
	for _, text := range published.Texts {
		node, err := logic.ParseFormula(text)
		if err != nil {
			set.broken = true
			continue
		}
		set.clauses = append(set.clauses, &clause{kind: "Invariant", text: text, node: node, pos: name.Pos(), res: resolver})
	}
	pv.invariants[name] = set
	return set, viaPointer
}

// exportInvariants publishes the invariants of the types of this package,
// with the values of the constants they mention.
func (pv *pkgVerifier) exportInvariants() {
	for name, set := range pv.invariants {
		if set == nil || name.Pkg() != pv.pass.Pkg || name.Parent() != pv.pass.Pkg.Scope() {
			continue
		}
		fact := &invariantFact{Consts: map[string]string{}, Broken: set.broken}
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
		for _, c := range set.clauses {
			fact.Texts = append(fact.Texts, c.text)
			visit(c.node)
		}
		pv.pass.ExportObjectFact(name, fact)
	}
}

// checkInvariantsDeclared resolves every invariant of this package once, so
// that one that cannot be read, or that no value can satisfy, is reported
// even if no verified function uses the type.
func (pv *pkgVerifier) checkInvariantsDeclared() {
	names := make([]*types.TypeName, 0, len(pv.invariants))
	for name, set := range pv.invariants {
		if set != nil {
			names = append(names, name)
		}
	}
	slices.SortFunc(names, func(a, b *types.TypeName) int { return int(a.Pos() - b.Pos()) })
	for _, name := range names {
		set := pv.invariants[name]
		if set.broken {
			continue
		}
		pv.run(&funcInfo{obj: types.NewFunc(name.Pos(), pv.pass.Pkg, name.Name(), types.NewSignatureType(nil, nil, nil, nil, nil, false))}, func(v *fnVerifier) {
			v.misreadAs = func(c *clause, err error) {
				set.broken = true
				pv.report(c.pos, "in %s annotation: %v", c.kind, err)
			}
			st := &state{vals: map[*types.Var]value{}, mem: memory{}, brk: logic.Const("brk", logic.Ref), noted: map[string]bool{}}
			self := v.unknown("self", name.Type(), st)
			v.assumeInvariants(st, nil, st.mem, self, name.Type())
			opts := solver.Options{Preds: pv.res.Preds, MaxSteps: pv.maxSteps}
			if solver.Prove(st.hyps, logic.False(), opts) == solver.Proved {
				set.broken = true
				pv.report(set.clauses[0].pos, "the invariants of %s contradict each other, so no value of the type could exist", name.Name())
			}
		})
	}
}

// invariantEnv gives meaning to the names in an invariant: the fields of the
// value it is stated of, which is self when the value is a struct and what
// self points to when it is a pointer. A type whose invariants could not be
// read cannot be used at a boundary at all.
func (v *fnVerifier) invariantEnv(set *invariantSet, sink *state, mem memory, self value, t types.Type) *specEnv {
	if set.broken {
		v.unsupported(v.fn.obj.Pos(), fmt.Sprintf("the invariants of %s could not be understood", set.name.Name()))
	}
	return &specEnv{v: v, sink: sink, fn: set.owner, now: mem, self: self, selfType: t}
}

// assumeInvariants adds the invariants of a value to the state, for a
// pointer on condition that it is not nil.
func (v *fnVerifier) assumeInvariants(st *state, guard []*logic.Term, mem memory, val value, t types.Type) {
	set, viaPointer := v.invariantsOf(t)
	if set == nil {
		return
	}
	if viaPointer {
		guard = append(slices.Clip(guard), logic.Lt(logic.IntLit(0), val[0]))
	}
	env := v.invariantEnv(set, st, mem, val, t)
	for _, c := range set.clauses {
		st.assume(logic.Implies(logic.And(guard...), v.formula(c, c.node, env)))
	}
}

// checkInvariants proves the invariants of a value, for a pointer on
// condition that it is not nil.
func (v *fnVerifier) checkInvariants(st *state, guard []*logic.Term, mem memory, val value, t types.Type, pos token.Pos, what string) {
	set, viaPointer := v.invariantsOf(t)
	if set == nil {
		return
	}
	if viaPointer {
		guard = append(slices.Clip(guard), logic.Lt(logic.IntLit(0), val[0]))
	}
	env := v.invariantEnv(set, st, mem, val, t)
	for _, c := range set.clauses {
		v.checkClause(c, env, st, guard, pos, fmt.Sprintf("invariant of %s may not hold for %s", set.name.Name(), what))
	}
}

// invariantsHold reports whether the invariants of a value can be proved,
// without reporting anything.
func (v *fnVerifier) invariantsHold(st *state, mem memory, val value, t types.Type) bool {
	set, viaPointer := v.invariantsOf(t)
	if set == nil {
		return true
	}
	var guard []*logic.Term
	if viaPointer {
		guard = []*logic.Term{logic.Lt(logic.IntLit(0), val[0])}
	}
	env := v.invariantEnv(set, st, mem, val, t)
	for _, c := range set.clauses {
		if !v.prove(st, guard, v.formula(c, c.node, env)) {
			return false
		}
	}
	return true
}
