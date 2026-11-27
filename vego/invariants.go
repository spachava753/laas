package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"slices"

	"github.com/spachava753/laas/vego/internal/logic"
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
	// group is set for the invariants of a group of package-level
	// variables, which no value carries: the frame pairs their reads as
	// it pairs a type's (varinv.go).
	group *varGroup
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
		// The clause is read by nobody; it may have been meant for the
		// function below the type.
		pv.unread = true
		pv.report(c.pos, rAnnotationFault, "%s annotations do not belong on a type; a type can only have Invariant and Owns annotations", c.kind)
		return
	case !isStruct || !isNamed || named.TypeParams() != nil:
		pv.unread = true
		pv.report(c.pos, rAnnotationFault, "an Invariant can only be declared on a struct type without type parameters")
		return
	}
	set := pv.invariants[name]
	if set == nil {
		set = &invariantSet{name: name, owner: &funcInfo{}}
		pv.invariants[name] = set
	}
	node, err := logic.ParseFormula(c.text)
	if err != nil {
		pv.report(c.pos, rAnnotationFault, "syntax error in Invariant annotation: %v", err)
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
	set.broken = set.broken || pv.foreignBroken[name.Pkg()]
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
		fact := &invariantFact{Consts: map[string]string{}, Broken: set.broken || pv.predicatesBroken || pv.unread}
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
				pv.report(c.pos, rAnnotationFault, "in %s annotation: %v", c.kind, err)
			}
			st := &state{vals: map[*types.Var]value{}, mem: memory{}, brk: logic.Const("brk", logic.Ref), noted: map[string]bool{}}
			self := v.unknown("self", name.Type(), st)
			v.assumeInvariants(st, nil, st.mem, self, name.Type(), "")
			if pv.contradictory(st.hyps) {
				set.broken = true
				pv.report(set.clauses[0].pos, rAnnotationFault, "the invariants of %s contradict each other, so no value of the type could exist", name.Name())
			}
		})
	}
}

// invariantEnv gives meaning to the names in an invariant: the fields of the
// value it is stated of, which is self when the value is a struct and what
// self points to when it is a pointer.
func (v *fnVerifier) invariantEnv(set *invariantSet, sink *state, mem memory, self value, t types.Type) *specEnv {
	if set.group != nil {
		return &specEnv{v: v, sink: sink, now: mem, pos: set.group.clauses[0].pos}
	}
	return &specEnv{v: v, sink: sink, fn: set.owner, now: mem, self: self, selfType: t}
}

// unusableInvariants reports, where the invariants of a type whose
// declaration could not be read are used, that they are neither assumed
// nor proved there. Leaving out an assumption only weakens what is known,
// and the function has failed at the report, so its other faults are
// still reported.
func (v *fnVerifier) unusableInvariants(set *invariantSet, pos token.Pos) {
	if v.unusableSets == nil {
		v.unusableSets = map[*invariantSet]bool{}
	}
	if v.unusableSets[set] {
		return
	}
	v.unusableSets[set] = true
	why := "an Invariant annotation of " + set.name.Name() + " could not be read, or they contradict each other, as reported at them"
	if set.name.Pkg() != v.pass.Pkg {
		why = "the annotations of package " + set.name.Pkg().Path() + " could not all be read"
	}
	v.report(pos, rAnnotationFault, "the invariants of %s cannot be used: %s, so they are neither assumed nor proved here", set.name.Name(), why)
}

// invariantStep is one struct whose invariants a value's invariants
// include: the value itself, and through each owned pointer field and
// each owner held by value, the struct reached there (C4 of ownership in
// source). guard holds when the struct exists: every pointer on the way is
// not nil. through spells the owned fields on the way, empty for the value
// itself.
type invariantStep struct {
	set     *invariantSet
	val     value
	t       types.Type
	guard   []*logic.Term
	through string
}

// invariantSteps returns the structs whose invariants hold of a value at
// a boundary: its own type's, and, recursively, those of what its owned
// pointer fields point to and of the owners it holds by value. A type that
// owns itself is refused where it is declared, so the walk ends; seen
// guards it anyway.
func (v *fnVerifier) invariantSteps(sink *state, mem memory, val value, t types.Type, guard []*logic.Term, through string, seen map[types.Type]bool) []invariantStep {
	object, viaPointer := pointee(t)
	if !viaPointer {
		object = t
	}
	if viaPointer {
		guard = append(slices.Clip(guard), logic.Lt(logic.IntLit(0), val[0]))
	}
	var steps []invariantStep
	if set, _ := v.invariantsOf(t); set != nil {
		steps = append(steps, invariantStep{set: set, val: val, t: t, guard: guard, through: through})
	}
	u, isStruct := object.Underlying().(*types.Struct)
	if !isStruct || seen[object] {
		return steps
	}
	seen[object] = true
	defer delete(seen, object)
	owned := sourceOwnedFields(object)
	for index := range u.NumFields() {
		field := u.Field(index)
		_, inline := field.Type().Underlying().(*types.Struct)
		ownedPointer := slices.Contains(owned, index) && !isSlice(field.Type()) && !isMap(field.Type()) && !isIface(field.Type())
		if !ownedPointer && !(inline && len(sourceOwnedFields(field.Type())) > 0) {
			continue
		}
		at := field.Name()
		if through != "" {
			at = through + "." + at
		}
		if ownedPointer {
			fv, ft, ok := v.member(sink, mem, val, t, index)
			if ok {
				steps = append(steps, v.invariantSteps(sink, mem, fv, ft, guard, at, seen)...)
			}
			continue
		}
		// An owner held by value lies inside the struct: through a
		// pointer it is a pointer at the field's offset, and in a value
		// the field's leaves.
		if viaPointer {
			inner := value{val[0], logic.Add(val[1], logic.IntLit(v.fieldOffset(object, index)))}
			steps = append(steps, v.invariantSteps(sink, mem, inner, types.NewPointer(field.Type()), guard, at, seen)...)
			continue
		}
		// In a value, the field's leaves. Boundaries never meet one, since
		// the copy rule refuses a struct that holds an owner by value, but
		// the check that a type's invariants do not contradict each other
		// asks them of a value of the type (F27 of the review of step 2).
		if lo, hi, ok := fieldLeaves(object, index); ok {
			steps = append(steps, v.invariantSteps(sink, mem, val[lo:hi], field.Type(), guard, at, seen)...)
		}
	}
	return steps
}

// assumeInvariants adds the invariants of a value to the state, for a
// pointer on condition that it is not nil, with those of what it owns.
//
// With from, which says where, at a point where the path of st assumes
// them with no condition of evaluation around them, each step is kept for
// a frame (frames.go).
func (v *fnVerifier) assumeInvariants(st *state, guard []*logic.Term, mem memory, val value, t types.Type, from string) {
	for _, step := range v.invariantSteps(st, mem, val, t, guard, "", map[types.Type]bool{}) {
		if step.set.broken {
			v.unusableInvariants(step.set, v.fn.obj.Pos())
			continue
		}
		env := v.invariantEnv(step.set, st, mem, step.val, step.t)
		for _, c := range step.set.clauses {
			st.assume(logic.Implies(logic.And(step.guard...), v.formula(c, c.node, env)))
		}
		if from != "" && len(guard) == 0 {
			st.keep(step, mem, from)
		}
	}
}

// checkInvariants proves the invariants of a value, for a pointer on
// condition that it is not nil, with those of what it owns.
func (v *fnVerifier) checkInvariants(st *state, guard []*logic.Term, mem memory, val value, t types.Type, pos token.Pos, what string) {
	for _, step := range v.invariantSteps(st, mem, val, t, guard, "", map[types.Type]bool{}) {
		if step.set.broken {
			v.unusableInvariants(step.set, pos)
			continue
		}
		env := v.invariantEnv(step.set, st, mem, step.val, step.t)
		for _, c := range step.set.clauses {
			// A struct reached through what the value owns is named by
			// where it lies.
			about := what
			if step.through != "" {
				about = fmt.Sprintf("%s, in what it owns at %s", what, step.through)
			}
			v.checkClauseFramed(c, env, st, step.guard, pos, fmt.Sprintf("invariant of %s may not hold for %s", step.set.name.Name(), about),
				func(node *logic.Node, _ *logic.Term) bool { return v.framedStep(st, step, mem, c, node) })
		}
	}
}

// invariantsHold reports whether the invariants of a value, with those of
// what it owns, can be proved, without reporting anything.
func (v *fnVerifier) invariantsHold(st *state, mem memory, val value, t types.Type) bool {
	for _, step := range v.invariantSteps(st, mem, val, t, nil, "", map[types.Type]bool{}) {
		if step.set.broken {
			return false
		}
		env := v.invariantEnv(step.set, st, mem, step.val, step.t)
		for _, c := range step.set.clauses {
			if !v.prove(st, step.guard, v.formula(c, c.node, env)) {
				return false
			}
		}
	}
	return true
}
