package vego

import (
	"fmt"
	"go/types"
	"math/big"
	"slices"
	"strconv"
	"strings"

	"github.com/spachava753/laas/vego/internal/logic"
)

// Dynamic types in formulas (S2 of F33): holds(err, T), err.(T), the
// conversion T(v), and an error compared with a value of a concrete type
// that Go converts to error, as in err = ErrSyntax.

var _ logic.Typer = (*specEnv)(nil)

// lookupName finds what a name means where the annotation was written: in
// a body, the scope at the annotation; in a contract of this package, the
// scope of the declaration; in a contract another package published, the
// key it recorded for the spelling (contractFact.Types); in a trust entry,
// the function's own package.
func (e *specEnv) lookupName(name string) types.Object {
	if e.fn == nil && e.selfType == nil {
		if scope := e.v.scopeAt(e.pos); scope != nil {
			_, obj := scope.LookupParent(name, e.pos)
			return obj
		}
		return nil
	}
	if e.selfType != nil {
		if pkg := e.writtenIn(); pkg != nil {
			return pkg.Scope().Lookup(name)
		}
		return nil
	}
	f := e.fn.spelling()
	switch {
	case f.imported != nil:
		return e.v.objectByKey(f.imported.Types[name])
	case f.trust != nil:
		if f.obj != nil && f.obj.Pkg() != nil {
			if obj := f.obj.Pkg().Scope().Lookup(name); obj != nil {
				return obj
			}
		}
		return types.Universe.Lookup(name)
	}
	pkg := f.writtenIn()
	if pkg == nil {
		return types.Universe.Lookup(name)
	}
	if pkg != e.v.pass.Pkg || f.obj == nil {
		if obj := pkg.Scope().Lookup(name); obj != nil {
			return obj
		}
		return types.Universe.Lookup(name)
	}
	pos := f.obj.Pos()
	if f.decl != nil {
		pos = f.decl.Pos()
	}
	_, obj := e.v.pass.Pkg.Scope().Innermost(pos).LookupParent(name, pos)
	return obj
}

// qualifiedConst returns the value and the type of a constant of another
// package that a formula names by the name of its package, as in
// s2.ErrSyntax; in a contract another package published, as it recorded
// them.
func (e *specEnv) qualifiedConst(pkg, name string) (*logic.Term, types.Type, bool) {
	spelled := pkg + "." + name
	if e.fn != nil && e.fn.spelling().imported != nil {
		imported := e.fn.spelling().imported
		text, ok := imported.Consts[spelled]
		if !ok {
			return nil, nil, false
		}
		var t types.Type
		if obj, isType := e.v.objectByKey(imported.Types["const "+spelled]).(*types.TypeName); isType {
			t = obj.Type()
		}
		if number, isNumber := new(big.Int).SetString(text, 10); isNumber {
			return logic.BigLit(number), t, true
		}
		return logic.BoolLit(text == "True"), t, true
	}
	name2, ok := e.lookupName(pkg).(*types.PkgName)
	if !ok {
		return nil, nil, false
	}
	c, ok := name2.Imported().Scope().Lookup(name).(*types.Const)
	if !ok || !c.Exported() {
		return nil, nil, false
	}
	literal, ok := literalOf(c.Val())
	if !ok {
		return nil, nil, false
	}
	return literal, c.Type(), true
}

// objectByKey finds the object of a key that typeKeyOf made, in the
// packages this package is built with.
func (pv *pkgVerifier) objectByKey(key string) types.Object {
	path, rest, err := cutQuoted(key)
	if err != nil {
		return nil
	}
	pkg := pv.packageByPath(path)
	if pkg == nil {
		return nil
	}
	return pkg.Scope().Lookup(strings.TrimPrefix(rest, "."))
}

// cutQuoted splits a quoted path at the start of a text from the rest.
func cutQuoted(text string) (path, rest string, err error) {
	quoted, err := strconv.QuotedPrefix(text)
	if err != nil {
		return "", "", err
	}
	path, err = strconv.Unquote(quoted)
	return path, text[len(quoted):], err
}

// packageByPath finds a package this package is built with by its path.
func (pv *pkgVerifier) packageByPath(path string) *types.Package {
	seen := map[*types.Package]bool{}
	queue := []*types.Package{pv.pass.Pkg}
	for len(queue) > 0 {
		pkg := queue[0]
		queue = queue[1:]
		if seen[pkg] {
			continue
		}
		seen[pkg] = true
		if pkg.Path() == path {
			return pkg
		}
		queue = append(queue, pkg.Imports()...)
	}
	return nil
}

// typeKeyOf names a defined type of a package by the quoted path of its
// package and its name, which objectByKey reads back; "" for any other.
func typeKeyOf(t types.Type) string {
	named, ok := types.Unalias(t).(*types.Named)
	if !ok || named.Obj().Pkg() == nil || named.TypeArgs() != nil || named.Obj().Pkg().Scope().Lookup(named.Obj().Name()) != named.Obj() {
		return ""
	}
	return strconv.Quote(named.Obj().Pkg().Path()) + "." + named.Obj().Name()
}

// resolveType finds the type a formula names: a defined type of the
// package, of an imported package by its name, or of any package in the
// build by its path in quotes, or a pointer to one.
func (e *specEnv) resolveType(t logic.TypeName) (types.Type, error) {
	if found, ok := t.Resolved.(types.Type); ok {
		return found, nil
	}
	var obj types.Object
	switch {
	case t.Quoted:
		if pkg := e.v.packageByPath(t.Qualifier); pkg != nil {
			obj = pkg.Scope().Lookup(t.Name)
		}
	case t.Qualifier != "":
		spelled := t.Qualifier + "." + t.Name
		if e.fn != nil && e.fn.spelling().imported != nil {
			obj = e.v.objectByKey(e.fn.spelling().imported.Types[spelled])
			break
		}
		if name, ok := e.lookupName(t.Qualifier).(*types.PkgName); ok {
			obj = name.Imported().Scope().Lookup(t.Name)
		}
	default:
		obj = e.lookupName(t.Name)
	}
	name, ok := obj.(*types.TypeName)
	if !ok {
		return nil, fmt.Errorf("%s is not a type here", t)
	}
	found := name.Type()
	if t.Pointer {
		found = types.NewPointer(found)
	}
	return found, nil
}

// IsType reports whether a name is a type where the formula stands.
func (e *specEnv) IsType(t logic.TypeName) bool {
	_, err := e.resolveType(t)
	return err == nil
}

// Convertible reports whether a name is a type whose values a formula can
// convert to: an integer, string, or boolean type.
func (e *specEnv) Convertible(t logic.TypeName) bool {
	found, err := e.resolveType(t)
	if err != nil {
		return false
	}
	basic, ok := found.Underlying().(*types.Basic)
	return ok && basic.Info()&(types.IsInteger|types.IsString|types.IsBoolean) != 0
}

// PathType returns the Go type of what a path leads to, or of a constant
// of a defined type, or nil.
func (e *specEnv) PathType(root string, steps []logic.Step, when logic.When) any {
	if len(steps) == 0 {
		if c, ok := e.lookupConst(root); ok {
			return c
		}
	}
	if len(steps) == 1 && steps[0].Field != "" {
		if _, t, ok := e.qualifiedConst(root, steps[0].Field); ok && t != nil {
			return t
		}
	}
	steps, err := e.resolveSteps(steps)
	if err != nil {
		return nil
	}
	found, err := e.locate(root, steps, when)
	if err != nil || found.constant != nil {
		return nil
	}
	return found.typ
}

// lookupConst returns the type of a constant a formula names, when it is a
// constant of a defined type; in a contract of another package, from the
// key it recorded.
func (e *specEnv) lookupConst(name string) (types.Type, bool) {
	if e.fn != nil && e.fn.spelling().imported != nil {
		if key, ok := e.fn.spelling().imported.Types["const "+name]; ok {
			if obj, ok := e.v.objectByKey(key).(*types.TypeName); ok {
				return obj.Type(), true
			}
		}
		return nil, false
	}
	if c, ok := e.lookupName(name).(*types.Const); ok {
		if _, named := types.Unalias(c.Type()).(*types.Named); named {
			return c.Type(), true
		}
	}
	return nil, false
}

// ErrorType returns the type of what a path leads to when it is a concrete
// type that implements error.
func (e *specEnv) ErrorType(root string, steps []logic.Step, when logic.When) (logic.TypeName, bool) {
	t, ok := e.PathType(root, steps, when).(types.Type)
	if !ok || t == nil || types.IsInterface(t) || !types.Implements(t, errorType) {
		return logic.TypeName{}, false
	}
	return logic.TypeName{Name: types.TypeString(t, types.RelativeTo(e.v.pass.Pkg)), Resolved: t}, true
}

// Convert returns T(v): v itself, for a string or a boolean, and for an
// integer when every value v can have is a value of T. A constant must lie in T's range, and a path must
// have an integer type whose range lies in T's; anything else may not fit,
// and Go would then wrap it, which a formula does not.
func (e *specEnv) Convert(t logic.TypeName, arg *logic.Term, argType any, literal bool) (*logic.Term, error) {
	target, err := e.resolveType(t)
	if err != nil {
		return nil, err
	}
	from, _ := argType.(types.Type)
	if basic, isBasic := target.Underlying().(*types.Basic); isBasic && basic.Info()&types.IsString != 0 {
		// Go converts a string or a []byte to a string by its bytes; a
		// slice of runes or of other integers it converts otherwise, or
		// not at all (F16 of the review of S2).
		ok := arg.Sort == logic.IntSeq && (literal || from != nil && (isString(from) || isSlice(from) && types.Identical(elemType(from).Underlying(), types.Typ[types.Uint8])))
		if !ok {
			return nil, fmt.Errorf("%s(...) converts a string or a []byte, as a formula reads their bytes; Go converts a value of another type otherwise", t)
		}
		return arg, nil
	}
	if basic, isBasic := target.Underlying().(*types.Basic); isBasic && basic.Info()&types.IsBoolean != 0 {
		if arg.Sort != logic.Bool {
			return nil, fmt.Errorf("%s(...) converts a boolean, and is given a %s", t, arg.Sort)
		}
		return arg, nil
	}
	lo, hi, ok := e.integerRange(target)
	if !ok {
		return nil, fmt.Errorf("%s(...) converts to a type whose values are not integers, strings, or booleans, which a formula cannot convert to", t)
	}
	if arg.Sort != logic.Int {
		return nil, fmt.Errorf("%s(...) converts an integer, and is given a %s", t, arg.Sort)
	}
	if value, isLiteral := groundValue(arg); isLiteral {
		if value.Cmp(lo) < 0 || value.Cmp(hi) > 0 {
			return nil, fmt.Errorf("%s(%s): %s is not a value of %s", t, value, value, t)
		}
		return arg, nil
	}
	from, isType := argType.(types.Type)
	if !isType || from == nil {
		return nil, fmt.Errorf("%s(...) takes a constant or a value read from a variable, whose type says that it fits %s", t, t)
	}
	flo, fhi, ok := e.integerRange(from)
	if !ok || flo.Cmp(lo) < 0 || fhi.Cmp(hi) > 0 {
		return nil, fmt.Errorf("%s(...) of a value of type %s, which may not fit %s; a formula does not wrap, so convert only values whose type fits", t, from, t)
	}
	return arg, nil
}

// integerRange returns the least and the greatest value of an integer
// type on the target.
func (e *specEnv) integerRange(t types.Type) (lo, hi *big.Int, ok bool) {
	basic, isBasic := t.Underlying().(*types.Basic)
	if !isBasic || basic.Info()&types.IsInteger == 0 || basic.Info()&types.IsUntyped != 0 {
		return nil, nil, false
	}
	bits := uint(8 * e.v.pass.TypesSizes.Sizeof(t))
	if basic.Info()&types.IsUnsigned != 0 {
		return big.NewInt(0), new(big.Int).Sub(new(big.Int).Lsh(big.NewInt(1), bits), big.NewInt(1)), true
	}
	half := new(big.Int).Lsh(big.NewInt(1), bits-1)
	return new(big.Int).Neg(half), new(big.Int).Sub(half, big.NewInt(1)), true
}

// typedTarget resolves the type of a value beside an error, which must be
// a concrete type that implements error, with a canonical name.
func (e *specEnv) typedTarget(t logic.TypeName) (types.Type, string, error) {
	target, err := e.resolveType(t)
	if err != nil {
		return nil, "", err
	}
	if types.IsInterface(target) || !types.Implements(target, errorType) {
		return nil, "", fmt.Errorf("%s does not implement error, so it cannot be compared with an error", t)
	}
	name, ok := canonicalName(target)
	if !ok {
		return nil, "", fmt.Errorf("%s is declared inside a function, and nothing tells it apart from another type there", t)
	}
	return target, name, nil
}

// formulaLeaves returns the leaves of a value of a type as a formula reads
// it: one term, or a pointer, whose position is zero when it is nil.
func formulaLeaves(t types.Type, v *logic.Term) (value, bool) {
	if v.Op == logic.OpPair {
		at := v.Args[1]
		if at == nil {
			return nil, false
		}
		return value{v.Args[0], logic.Ite(logic.Eq(v.Args[0], logic.RefLit(0)), logic.IntLit(0), at)}, true
	}
	if v.Sort == logic.Ref && v.Op == logic.OpIntLit && v.Val == 0 {
		// nil of a pointer type.
		return value{v, logic.IntLit(0)}, true
	}
	if _, single := sortOf(t); single {
		return value{v}, true
	}
	return nil, false
}

// TypedEquals returns err = error(T(v)), Go's == of the two: for a type
// whose errors are terms of their values, equality with that term, whose
// facts are noted where it is built; for another type on which == is
// identity, whether err holds T and the value v. A type on which == is not
// identity is refused, since == may panic or say false of a value and
// itself.
func (e *specEnv) TypedEquals(t logic.TypeName, err, v *logic.Term) (*logic.Term, error) {
	target, name, failure := e.typedTarget(t)
	if failure != nil {
		return nil, failure
	}
	layout, _ := layoutOf(target)
	if !e.v.identityEq(target) || !capturesValue(layout) {
		return nil, fmt.Errorf("== on values of %s is not identity, so an error cannot be compared with one in a formula", t)
	}
	leaves, ok := formulaLeaves(target, v)
	if !ok {
		return nil, fmt.Errorf("a value of %s is a struct, and a formula cannot compare a struct or use it as a whole; compare what the error holds field by field, as in err.(%s).f", t, t)
	}
	if canonical := e.v.canonicalError(target, leaves); canonical != nil {
		e.noteCanonical(canonical, target, leaves)
		return logic.Eq(err, canonical), nil
	}
	tag, _ := typeTag(target)
	ref := logic.ErrRef(err)
	e.v.meetType(e.sink, target)
	return logic.And(logic.Not(logic.IsNil(err)), logic.Eq(dynTag(ref), tag), eqLeaf(logic.Select(heldTable(name, 0, layout[0]), ref), leaves[0])), nil
}

// TypedError returns the error that holds v, for a type whose errors are
// terms of their values.
func (e *specEnv) TypedError(t logic.TypeName, v *logic.Term) (*logic.Term, error) {
	target, _, failure := e.typedTarget(t)
	if failure != nil {
		return nil, failure
	}
	leaves, ok := formulaLeaves(target, v)
	var canonical *logic.Term
	if ok {
		canonical = e.v.canonicalError(target, leaves)
	}
	if canonical == nil {
		return nil, fmt.Errorf("an error that holds a value of %s is not one term of the value, so it cannot be the target of is; only one of an integer or a pointer type on which == is identity can", t)
	}
	e.noteCanonical(canonical, target, leaves)
	return canonical, nil
}

// noteCanonical states what an error that is a term of a value holds,
// where a formula builds it (F8 of the design review): in the state the
// formula is read in, or, when the value mentions a variable a quantifier
// binds, as one fact for every value of the type, which no ground fact
// could state.
func (e *specEnv) noteCanonical(err *logic.Term, t types.Type, leaves value) {
	sink := e.sink
	if sink == nil {
		return
	}
	bound := false
	for _, leaf := range leaves {
		bound = bound || hasBound(leaf)
	}
	if !bound {
		e.v.noteHeld(sink, err, t, leaves)
		return
	}
	name, _ := canonicalName(t)
	if note := "canonical " + name; sink.noted[note] {
		return
	}
	sink.noted["canonical "+name] = true
	layout, _ := layoutOf(t)
	vars := make([]*logic.Term, len(layout))
	for i := range layout {
		vars[i] = logic.Bound(fmt.Sprintf("canonical#%d", i), layout[i].sort)
	}
	quantified := value(vars)
	if len(layout) == 2 {
		quantified = value{vars[0], logic.Ite(logic.Eq(vars[0], logic.RefLit(0)), logic.IntLit(0), vars[1])}
	}
	general := e.v.canonicalError(t, quantified)
	tag, _ := typeTag(t)
	ref := logic.ErrRef(general)
	body := []*logic.Term{logic.Not(logic.IsNil(general)), logic.Eq(dynTag(ref), tag)}
	for i, lf := range layout {
		body = append(body, eqLeaf(logic.Select(heldTable(name, i, lf), ref), quantified[i]))
	}
	fact := logic.And(body...)
	for i := len(vars) - 1; i >= 0; i-- {
		fact = logic.Forall(vars[i], fact)
	}
	e.v.typedMet = true
	for _, made := range e.v.distinct {
		e.v.noteMadeTag(sink, made)
	}
	e.v.meetType(sink, t)
	e.v.fact(sink, fact)
}

// resolveSteps resolves the types of the steps of a path that read what an
// error holds, which plan reads from Resolved.
func (e *specEnv) resolveSteps(steps []logic.Step) ([]logic.Step, error) {
	var out []logic.Step
	for i, step := range steps {
		if step.Assert == nil && step.Holds == nil {
			continue
		}
		if out == nil {
			out = slices.Clone(steps)
		}
		for _, named := range []**logic.TypeName{&out[i].Assert, &out[i].Holds} {
			if *named == nil || (*named).Resolved != nil {
				continue
			}
			found, err := e.resolveType(**named)
			if err != nil {
				return nil, err
			}
			resolved := **named
			resolved.Resolved = found
			*named = &resolved
		}
	}
	if out == nil {
		return steps, nil
	}
	return out, nil
}

// holdsPath resolves holds(x, T): x is not nil and holds a value of T.
func (e *specEnv) holdsPath(name string, steps []logic.Step, t *logic.TypeName, when logic.When) (*logic.Term, error) {
	found, err := e.locate(name, steps, when)
	switch {
	case err != nil:
		return nil, err
	case found.constant != nil && found.constant.Sort != logic.Err:
		return nil, fmt.Errorf("holds(%s, ...): %s is not an error", spell(name, steps), spell(name, steps))
	case found.constant == nil && !isError(found.typ):
		if isIface(found.typ) {
			return nil, fmt.Errorf("holds(%s, ...) of an interface value other than an error is not supported yet", spell(name, steps))
		}
		return nil, fmt.Errorf("holds(%s, ...): %s is not an error", spell(name, steps), spell(name, steps))
	}
	err2 := found.constant
	if err2 == nil {
		err2 = found.val[0]
	}
	target := t.Resolved.(types.Type)
	if types.IsInterface(target) {
		return nil, fmt.Errorf("holds(%s, %s): %s is an interface, and asking whether an error holds a value that implements one is not supported yet", spell(name, steps), t, t)
	}
	tag, ok := typeTag(target)
	if !ok {
		return nil, fmt.Errorf("holds(%s, %s): %s is declared inside a function, and nothing tells it apart from another type there", spell(name, steps), t, t)
	}
	e.v.meetType(e.sink, target)
	return logic.And(logic.Not(logic.IsNil(err2)), logic.Eq(errorTag(err2), tag)), nil
}

// heldRead returns the leaves of what an error holds as a value of a type,
// with what the type guarantees of them noted (F8 of the design review).
func (v *fnVerifier) heldRead(sink *state, err *logic.Term, t types.Type) value {
	name, _ := canonicalName(t)
	layout, _ := layoutOf(t)
	ref := logic.ErrRef(err)
	held := make(value, len(layout))
	for i, lf := range layout {
		held[i] = logic.Select(heldTable(name, i, lf), ref)
	}
	if sink != nil {
		v.noteTyped(sink, held, t)
		// A nil pointer is held at position zero.
		for i, lf := range layout {
			if lf.part == partAt && i > 0 && layout[i-1].part == partPtr {
				fact := logic.Implies(logic.Eq(held[i-1], logic.RefLit(0)), logic.Eq(held[i], logic.IntLit(0)))
				if note := "held " + fact.String(); !sink.noted[note] {
					sink.noted[note] = true
					sink.assume(fact)
				}
			}
		}
	}
	return held
}
