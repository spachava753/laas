package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"slices"
	"strings"
	"sync"

	"github.com/spachava753/laas/vego/internal/logic"
	"github.com/spachava753/laas/vego/internal/solver"
)

// Ownership declared in source (F27). `// @Owns items, m` in the doc
// comment of a struct type of the project says that a value of the type
// owns the memory those fields refer to: Modifies of a pointer to it covers
// that memory, as it covers what a shipped owner owns (ownedParts), and an
// owned field may come to refer only to memory made since the running
// function was entered, or to part of what it referred to just before (the
// growth rule G, checkOwnedStore). An owned field must be unexported, so
// that only its package can store into it, and so that every struct type
// identical to the owner lies in that package.
//
// What a type owns is needed wherever a type is looked at, the copy rule
// included, which has no package at hand, so the declarations of the
// project are kept in a registry of the process: a package registers its
// own when it collects them, and those of its imports from their facts
// when it starts (importOwns). Every package of a build reads one
// declaration of a type, the one in its source.

// ownsFact carries what a struct type of the project owns to importing
// packages.
type ownsFact struct {
	Fields []string
}

func (*ownsFact) AFact() {}

func (f *ownsFact) String() string { return "owns(" + strings.Join(f.Fields, ", ") + ")" }

// ownedType is one registered declaration.
type ownedType struct {
	name   *types.TypeName
	fields []string
}

var sourceOwns = struct {
	sync.RWMutex
	byPkg map[*types.Package][]ownedType
}{byPkg: map[*types.Package][]ownedType{}}

// registerOwns records what a type owns, replacing an earlier record of
// the same type.
func registerOwns(name *types.TypeName, fields []string) {
	sourceOwns.Lock()
	defer sourceOwns.Unlock()
	// A list is never changed once it is published: a reader iterates the
	// list it took after the lock is released, and a speculative verifier
	// collects the package again beside it (F19 of the review of step 1).
	list := sourceOwns.byPkg[name.Pkg()]
	next := make([]ownedType, 0, len(list)+1)
	for _, known := range list {
		if known.name == name {
			if slices.Equal(known.fields, fields) {
				return
			}
			continue
		}
		next = append(next, known)
	}
	sourceOwns.byPkg[name.Pkg()] = append(next, ownedType{name: name, fields: fields})
}

// sourceOwnedFields returns the indices of the fields of a struct type that
// a declaration in source says it owns, matched by the underlying struct,
// tags ignored, as the shipped declarations are (F1 of F26): a type defined
// over an owner owns what the owner owns.
func sourceOwnedFields(t types.Type) []int {
	u, isStruct := types.Unalias(t).Underlying().(*types.Struct)
	if !isStruct {
		return nil
	}
	var home *types.Package
	for field := range u.Fields() {
		if !field.Exported() && field.Pkg() != nil {
			home = field.Pkg()
			break
		}
	}
	if home == nil {
		return nil
	}
	sourceOwns.RLock()
	list := sourceOwns.byPkg[home]
	sourceOwns.RUnlock()
	if len(list) == 0 {
		return nil
	}
	plain := untagged(u)
	for _, known := range list {
		if !types.Identical(plain, untagged(known.name.Type().Underlying())) {
			continue
		}
		var indices []int
		for _, name := range known.fields {
			for i := range u.NumFields() {
				if u.Field(i).Name() == name {
					indices = append(indices, i)
				}
			}
		}
		return indices
	}
	return nil
}

// ownsDeclaredBy returns the type whose Owns declaration a struct type
// owns by, when it is not the type itself: a type with the fields of an
// owner owns what the owner owns (F25 of the review of step 2).
func ownsDeclaredBy(t types.Type) *ownedType {
	u, isStruct := types.Unalias(t).Underlying().(*types.Struct)
	if !isStruct {
		return nil
	}
	var home *types.Package
	for field := range u.Fields() {
		if !field.Exported() && field.Pkg() != nil {
			home = field.Pkg()
			break
		}
	}
	sourceOwns.RLock()
	list := sourceOwns.byPkg[home]
	sourceOwns.RUnlock()
	named, _ := types.Unalias(t).(*types.Named)
	for _, known := range list {
		if types.Identical(untagged(u), untagged(known.name.Type().Underlying())) {
			if named != nil && named.Obj() == known.name {
				return nil
			}
			return &known
		}
	}
	return nil
}

// ownsDeclSource is a declaration of this package while it is collected.
type ownsDeclSource struct {
	name   *types.TypeName
	fields []string
	pos    token.Pos
	broken bool
}

// importOwns registers what the types of the packages this one imports
// own, from their facts.
func (pv *pkgVerifier) importOwns() {
	for _, fact := range pv.pass.AllObjectFacts() {
		if owns, ok := fact.Fact.(*ownsFact); ok {
			if name, isType := fact.Object.(*types.TypeName); isType && name.Pkg() != pv.pass.Pkg {
				registerOwns(name, owns.Fields)
			}
		}
	}
}

// addOwns reads an Owns annotation on a struct type: a list of fields,
// each unexported and holding a pointer to a struct, a slice, or a map.
func (pv *pkgVerifier) addOwns(name *types.TypeName, c *clause) {
	u, isStruct := name.Type().Underlying().(*types.Struct)
	named, isNamed := name.Type().(*types.Named)
	if !isStruct || !isNamed || named.TypeParams() != nil {
		pv.report(c.pos, "an Owns can only be declared on a struct type without type parameters")
		return
	}
	if pv.ownsSource == nil {
		pv.ownsSource = map[*types.TypeName]*ownsDeclSource{}
	}
	decl := pv.ownsSource[name]
	if decl == nil {
		decl = &ownsDeclSource{name: name, pos: c.pos}
		pv.ownsSource[name] = decl
		pv.ownsOrder = append(pv.ownsOrder, name)
	}
	for _, part := range strings.Split(c.text, ",") {
		field := strings.TrimSpace(part)
		if !token.IsIdentifier(field) {
			pv.report(c.pos, "an Owns annotation lists fields of the struct, separated by commas, as in // @Owns items, m")
			decl.broken = true
			return
		}
		index := slices.IndexFunc(slices.Collect(u.Fields()), func(f *types.Var) bool { return f.Name() == field })
		switch {
		case index < 0:
			pv.report(c.pos, "%s has no field %s to own", name.Name(), field)
			decl.broken = true
			continue
		case slices.Contains(decl.fields, field):
			pv.report(c.pos, "%s is owned twice", field)
			decl.broken = true
			continue
		}
		f := u.Field(index)
		if f.Exported() {
			pv.report(c.pos, "%s cannot be owned: it is exported, and a field can be owned only when it is unexported, "+
				"so that only package %s can change what it refers to; unexport it, or leave it unowned", field, pv.pass.Pkg.Name())
			decl.broken = true
			continue
		}
		object, isPointer := pointee(f.Type())
		toStruct := false
		if isPointer {
			_, toStruct = types.Unalias(object).Underlying().(*types.Struct)
		}
		switch {
		case isPointer && toStruct, isSlice(f.Type()), isMap(f.Type()), isIface(f.Type()):
		default:
			held := types.TypeString(f.Type(), types.RelativeTo(pv.pass.Pkg))
			article := "a"
			if strings.ContainsRune("aeiou", rune(held[0])) {
				article = "an"
			}
			pv.report(c.pos, "%s cannot be owned: it holds %s %s, and a field can be owned when it holds a pointer to a struct, a slice, a map, or an interface value",
				field, article, held)
			decl.broken = true
			continue
		}
		decl.fields = append(decl.fields, field)
	}
}

// checkOwnsDeclared refuses a type that would own itself through owned
// pointer fields and owners held by value, and registers every declaration
// that stands. It runs once every declaration of the package is read; a
// chain cannot leave the package and come back, since imports are acyclic.
func (pv *pkgVerifier) checkOwnsDeclared() {
	for _, name := range pv.ownsOrder {
		decl := pv.ownsSource[name]
		if decl.broken {
			continue
		}
		if chain := pv.ownsItself(name); chain != "" {
			pv.report(decl.pos, "%s", chain)
			decl.broken = true
		}
	}
	for _, name := range pv.ownsOrder {
		if decl := pv.ownsSource[name]; !decl.broken {
			registerOwns(name, decl.fields)
		}
	}
}

// ownsItself returns the message for a type that owns itself, or "".
func (pv *pkgVerifier) ownsItself(start *types.TypeName) string {
	type step struct {
		owner *types.TypeName
		field string
		to    types.Type
	}
	ownedOf := func(t types.Type) []string {
		named, ok := types.Unalias(t).(*types.Named)
		if !ok {
			return nil
		}
		if decl := pv.ownsSource[named.Obj()]; decl != nil && !decl.broken {
			return decl.fields
		}
		var names []string
		u, _ := t.Underlying().(*types.Struct)
		for _, i := range sourceOwnedFields(t) {
			names = append(names, u.Field(i).Name())
		}
		return names
	}
	var path []step
	seen := map[types.Type]bool{}
	var walk func(t types.Type) bool
	walk = func(t types.Type) bool {
		u, isStruct := types.Unalias(t).Underlying().(*types.Struct)
		if !isStruct || seen[t] {
			return false
		}
		seen[t] = true
		defer delete(seen, t)
		named, _ := types.Unalias(t).(*types.Named)
		owned := ownedOf(t)
		for field := range u.Fields() {
			var next types.Type
			if slices.Contains(owned, field.Name()) {
				next, _ = pointee(field.Type())
			} else if _, inline := field.Type().Underlying().(*types.Struct); inline {
				next = field.Type()
			}
			if next == nil {
				continue
			}
			var owner *types.TypeName
			if named != nil {
				owner = named.Obj()
			}
			path = append(path, step{owner: owner, field: field.Name(), to: next})
			if types.Identical(untagged(next.Underlying()), untagged(start.Type().Underlying())) || walk(next) {
				return true
			}
			path = path[:len(path)-1]
		}
		return false
	}
	if !walk(start.Type()) {
		return ""
	}
	q := types.RelativeTo(pv.pass.Pkg)
	if len(path) == 1 {
		return fmt.Sprintf("%s cannot own %s: %s points to a %s, so a %s would own itself; "+
			"a linked structure cannot be declared with Owns; leave %s unowned",
			start.Name(), path[0].field, path[0].field, types.TypeString(path[0].to, q), start.Name(), path[0].field)
	}
	var links []string
	for i, s := range path {
		owner := start.Name()
		if s.owner != nil {
			owner = s.owner.Name()
		}
		link := fmt.Sprintf("%s owns %s through %s", owner, types.TypeString(s.to, q), s.field)
		if i > 0 && i == len(path)-1 {
			link = "and " + link
		}
		links = append(links, link)
	}
	return fmt.Sprintf("%s would own itself: %s; a linked structure cannot be declared with Owns; leave one of these fields unowned",
		start.Name(), strings.Join(links, ", "))
}

// ownedStore describes an assignment target that is an owned field: the
// struct type that declares it and the field's index.
type ownedStore struct {
	holder types.Type
	index  int
	// off is where the struct that holds the field lies from where the
	// target's pointer, element, or variable starts.
	off int64
}

// ownedFieldAt reports whether a field of a struct type is owned by a
// declaration in source. What a shipped owner owns lies in unexported
// fields of another module, which verified code cannot assign.
func ownedFieldAt(t types.Type, index int) bool {
	return slices.Contains(sourceOwnedFields(t), index)
}

// allocates reports whether an expression makes the memory it yields
// where it stands: a composite literal, its address, make, new, append,
// and a conversion of a string to a slice.
func (v *fnVerifier) allocates(e ast.Expr) bool {
	switch x := ast.Unparen(e).(type) {
	case *ast.CompositeLit:
		return true
	case *ast.UnaryExpr:
		_, literal := ast.Unparen(x.X).(*ast.CompositeLit)
		return x.Op == token.AND && literal
	case *ast.CallExpr:
		if isBuiltin(v.info, x, "make") || isBuiltin(v.info, x, "new") || isBuiltin(v.info, x, "append") {
			return true
		}
		if tv, ok := v.info.Types[x.Fun]; ok && tv.IsType() && len(x.Args) == 1 {
			return isSlice(tv.Type) && isString(v.info.TypeOf(x.Args[0]))
		}
	}
	return false
}

// storedCall describes the call a value stored into an owned field comes
// from, when it does: the contract, and whether the callee keeps nothing
// of what it is handed, so that its result may lie within the field (F11
// of the design review). Only the entry of a trusted function says that in
// this step: a shipped function or one of the trust file, with no keeps.
type storedCall struct {
	fn       *funcInfo
	name     string
	keepsNot bool
	verified bool
}

// storedCallOf returns the call a value stored into an owned field comes
// from, or nil when the expression is no call or allocates where it
// stands. A conversion is seen through to what it converts. A trusted
// callee whose entry lists no keeps keeps nothing, and a verified callee
// whose contract says fresh(result) is marked until step 3, which reads
// what it keeps from its summary.
func (v *fnVerifier) storedCallOf(e ast.Expr) *storedCall {
	call, ok := ast.Unparen(e).(*ast.CallExpr)
	if !ok || v.allocates(e) {
		return nil
	}
	if tv, ok := v.info.Types[call.Fun]; ok && tv.IsType() {
		if len(call.Args) == 1 {
			return v.storedCallOf(call.Args[0])
		}
		return nil
	}
	fn := v.memCallee(call)
	sc := &storedCall{fn: fn, name: types.ExprString(call.Fun)}
	if fn != nil && fn.trust != nil && len(fn.trust.keeps) == 0 {
		sc.keepsNot = true
	}
	// A verified callee keeps nothing of what it is handed when its
	// summary says so of every parameter (R4).
	if summary := v.pkgVerifier.ownSummaryOf(fn); summary != nil && !slices.Contains(summary.keeps, true) {
		sc.keepsNot, sc.verified = true, true
	}
	return sc
}

// ownedNothing states that a value of an owned field's type refers to no
// memory: a slice without capacity, a nil map or pointer.
func ownedNothing(val value, t types.Type) *logic.Term {
	if isSlice(t) {
		return logic.Le(val[3], logic.IntLit(0))
	}
	return logic.Eq(val[0], logic.RefLit(0))
}

// ownedWithin states that a value lies within what another value of an
// owned field's type refers to: a slice in the same array inside its
// stretch, the same map, the same pointer.
func (v *fnVerifier) ownedWithin(val, cur value, t types.Type) *logic.Term {
	switch {
	case isSlice(t):
		lo, hi := v.extent(val, t)
		curLo, curHi := v.extent(cur, t)
		return logic.And(logic.Eq(val[0], cur[0]), logic.Le(curLo, lo), logic.Le(hi, curHi))
	case isMap(t), isIface(t):
		return logic.Eq(val[0], cur[0])
	}
	return logic.And(logic.Eq(val[0], cur[0]), logic.Eq(val[1], cur[1]))
}

// ownedMadeSince states that what a value of an owned field's type refers
// to was allocated at or past a bound. For a pointer to an owner, what the
// struct owns was then made at or past the bound too, by G itself: every
// store into an owned field of a struct made since the bound stores
// nothing, part of what the field held, or memory made since its own
// statement began, which is past the bound, and nothing else stores into
// an owned field of the project. So it is not read, which inside the
// evaluation of an expression could not be.
func ownedMadeSince(val value, bound *logic.Term) *logic.Term {
	return logic.Le(bound, val[0])
}

// checkOwnedStore requires that what is stored into an owned field keeps
// what the owner owns placed (G) and referred to only through the field
// (R1 of the design, as far as this step builds it). The value must refer
// to nothing; lie within what the field refers to just before the store,
// unless it comes from a call that may keep what it is handed; or, when
// the expression makes it there or a trusted call that keeps nothing
// returns it, have been made since the statement began. cur is what the
// field holds just before the store, and before the bound when the
// statement began.
func (v *fnVerifier) checkOwnedStore(st *state, guard []*logic.Term, val, cur value, t, holder types.Type, rhs, key ast.Expr, before *logic.Term, field string, example func(making string) string, pos token.Pos) {
	options := []*logic.Term{ownedNothing(val, t)}
	call := v.storedCallOf(rhs)
	if cur != nil && (call == nil || call.keepsNot) {
		options = append(options, v.ownedWithin(val, cur, t))
	}
	// Memory a built-in or a literal makes in this statement, or a trusted
	// call that keeps nothing returns, nothing else refers to; nor new
	// memory that the analysis of ownership finds made of tags that are
	// all new (R1), made since the function was entered.
	// A value converted to an interface where it is stored is a new
	// interface value, whose footprint must be new too.
	converted := rhs != nil && isIface(t) && !isIface(v.info.TypeOf(rhs))
	if isIface(t) {
		if converted || rhs != nil && v.allocates(rhs) || call != nil && call.keepsNot && !call.verified && !v.targetsHoldReferences(call.fn) {
			options = append(options, logic.And(logic.Le(before, home(val[0])), v.rowNewOrIn(st.mem, home(val[0]), before, nil, nil)))
		}
	} else if rhs != nil && v.allocates(rhs) || call != nil && call.keepsNot && !call.verified && !v.targetsHoldReferences(call.fn) {
		options = append(options, ownedMadeSince(val, before))
	}
	flowMade := false
	fl := v.ownOrigins()
	if fl == nil {
		fl = &ownFlow{}
	}
	if key != nil && fl.made[key] {
		flowMade = true
		if isIface(t) {
			// A value converted from new memory nothing else refers to,
			// here or into a variable, has a new home and a new row (F34
			// of the review of step 3b).
			options = append(options, logic.And(logic.Le(v.entryBrk, home(val[0])), v.rowNewOrIn(st.mem, home(val[0]), v.entryBrk, nil, nil)))
		} else {
			options = append(options, ownedMadeSince(val, v.entryBrk))
		}
	}
	result := v.attempt(st, guard, logic.Or(options...))
	// What follows is verified as if the store were one of those, as after
	// any check, so that a refused store draws no second report from what
	// it would bring in.
	defer st.assume(logic.Implies(logic.And(guard...), logic.Or(options...)))
	if result == solver.Proved {
		return
	}
	// What works today, by the kind of the field.
	making, copied := "make(...)", "copy it into new memory, as slices.Clone does"
	if object, isPointer := pointee(t); isPointer {
		making = "&" + types.TypeString(object, types.RelativeTo(v.pass.Pkg)) + "{...}"
		copied = "copy it into a struct made with " + making
	} else if isMap(t) {
		copied = "copy it into new memory, as maps.Clone does"
	} else if isIface(t) {
		making, copied = "a value made here, as &T{...}", "make the value it holds where it is stored"
	}
	// What is not new since the function was entered is memory the owner
	// did not own, which no form of the store may bring in.
	newSinceEntry := ownedMadeSince(val, v.entryBrk)
	if isIface(t) {
		newSinceEntry = logic.And(logic.Le(v.entryBrk, home(val[0])), v.rowNewOrIn(st.mem, home(val[0]), v.entryBrk, nil, nil))
	}
	old := !v.quickly(st, guard, logic.Or(ownedNothing(val, t), newSinceEntry))
	switch {
	case flowMade && call != nil && !promisesFresh(call.fn, 0):
		v.report(pos, "what is stored into %s comes from the call of %s, which returns memory nothing else refers to, but its contract does not say "+
			"fresh(result), so it may be memory that existed; say so in the contract of %s%s", field, call.name, call.name, limitNote(result))
	case call != nil && !call.keepsNot:
		what := "a function whose contract does not say that it keeps nothing of what it is handed"
		if call.fn != nil && call.fn.trust == nil && call.fn.valueOf == nil && call.fn.methodOf == nil {
			what = "a verified function"
		}
		v.report(pos, "what is stored into %s comes from the call of %s, %s; storing the result of such a call into an owned field "+
			"is not supported yet%s", field, call.name, what, limitNote(result))
	case old:
		undeclare := ", or do not declare the field owned"
		if known := ownsDeclaredBy(holder); known != nil {
			shown := types.TypeString(holder, types.RelativeTo(v.pass.Pkg))
			owned := strings.Join(known.fields, ", ")
			undeclare = fmt.Sprintf(". %s owns %s because it has the fields of %s, which declares // @Owns %s; to store it as it is, give %s a field of its own, or use %s",
				shown, owned, known.name.Name(), owned, shown, known.name.Name())
		}
		v.report(pos, "%s may come to refer to memory that existed when %s was called and that it did not own; an owned field may refer only "+
			"to memory made since, or to part of what it referred to then; %s%s%s", field, v.fn.obj.Name(), copied, undeclare, limitNote(result))
	default:
		v.report(pos, "what is stored into %s is new memory that something else may refer to%s; make it where it is stored, as in %s, "+
			"or copy it there%s", field, fl.why[key], example(making), limitNote(result))
	}
}

// checkOwnedTarget checks a store into an assignment target that is an
// owned field (checkOwnedStore), reading what the field holds just before
// the store. A map value is never one: a field of a map value cannot be
// assigned.
func (v *fnVerifier) checkOwnedTarget(st *state, lv lvalue, val value, rhs ast.Expr, before *logic.Term) {
	if lv.owned == nil || lv.kind == placeBlank {
		return
	}
	var cur value
	switch lv.kind {
	case placeLocal:
		if whole := st.vals[lv.local]; whole != nil {
			cur = whole[lv.lo : lv.lo+len(lv.leaves)]
		} else {
			cur = zeroValue(lv.typ)
		}
	case placeMem:
		if lv.declares {
			cur = zeroValue(lv.typ)
		} else {
			cur = v.loadIn(lv, st, st.mem)
		}
	}
	v.checkOwnedStore(st, nil, val, cur, lv.typ, lv.owned.holder, rhs, ast.Unparen(lv.expr), before, lv.text, func(making string) string { return lv.text + " = " + making }, lv.pos)
}

// ownerRoot returns, for a store into an owned field through a pointer
// expression, the local variable the owner is rooted at, with the type of
// a pointer to the owner there and its offset from where the variable
// points: the variable itself, when it points to the struct that holds the
// field, or the outermost owner when the pointer is read through owned
// pointer fields from one, as s.p in s.p.items, whose growth covers that
// of what s.p points to.
func (v *fnVerifier) ownerRoot(pointer ast.Expr, owned *ownedStore) (*types.Var, types.Type, int64, bool) {
	if variable := v.localVar(pointer); variable != nil && !v.boxed[variable] {
		return variable, types.NewPointer(owned.holder), owned.off, true
	}
	root, owner, ok := v.ownedPathRoot(pointer)
	return root, owner, 0, ok
}

// reachesSourceOwner returns a struct type that owns memory by a
// declaration in source and that a value of type t is or reaches through
// pointers, slices, maps, and fields, not through an interface value, or
// nil.
func reachesSourceOwner(t types.Type, seen map[types.Type]bool) types.Type {
	if seen[t] {
		return nil
	}
	seen[t] = true
	if object, isPointer := pointee(t); isPointer {
		return reachesSourceOwner(object, seen)
	}
	switch u := t.Underlying().(type) {
	case *types.Slice:
		return reachesSourceOwner(u.Elem(), seen)
	case *types.Array:
		return reachesSourceOwner(u.Elem(), seen)
	case *types.Map:
		if found := reachesSourceOwner(u.Key(), seen); found != nil {
			return found
		}
		return reachesSourceOwner(u.Elem(), seen)
	case *types.Struct:
		if len(sourceOwnedFields(t)) > 0 {
			return t
		}
		for field := range u.Fields() {
			if found := reachesSourceOwner(field.Type(), seen); found != nil {
				return found
			}
		}
	}
	return nil
}

// ownedPathRoot returns, for an expression that reads a pointer through an
// owned pointer field of what a local variable points to, as s.store, the
// variable and its type: what the expression points to is part of what the
// variable's owner owns.
func (v *fnVerifier) ownedPathRoot(e ast.Expr) (*types.Var, types.Type, bool) {
	sel, ok := ast.Unparen(e).(*ast.SelectorExpr)
	if !ok {
		return nil, nil, false
	}
	selection := v.info.Selections[sel]
	if selection == nil || selection.Kind() != types.FieldVal || len(selection.Index()) != 1 {
		return nil, nil, false
	}
	object, viaPointer := pointee(v.info.TypeOf(sel.X))
	if !viaPointer || !ownedFieldAt(object, selection.Index()[0]) {
		return nil, nil, false
	}
	root := v.localVar(sel.X)
	if root == nil || v.boxed[root] {
		return nil, nil, false
	}
	return root, v.info.TypeOf(sel.X), true
}

// partCells returns a test of the cells a structural part of an owner
// refers to on entry: the array of a slice inside its stretch, a map, or a
// struct; nil for a row.
func partCells(t target) func(ref, position *logic.Term) *logic.Term {
	switch {
	case t.fp || t.row:
		return nil
	case t.mapType != nil:
		return func(ref, position *logic.Term) *logic.Term {
			return logic.And(logic.Ne(t.ref, logic.RefLit(0)), logic.Eq(ref, t.ref), logic.Eq(position, logic.IntLit(0)))
		}
	}
	return func(ref, position *logic.Term) *logic.Term {
		return logic.And(logic.Ne(t.ref, logic.RefLit(0)), logic.Eq(ref, t.ref), logic.Le(t.lo, position), logic.Lt(position, t.hi))
	}
}

// separatePart completes the separation of the part of an owner that the
// frame's target i is (C3): what the owner parameter refers to directly,
// its struct, is reached as the other parameters are, and so are the
// owner's other parts; and the reach does not follow the owned cells of
// the owner's struct and of the structs it owns, which are what holds the
// parts. Why that is the claim HI and E give: a reference to a part stored
// in memory lies only in the owned cell that holds it, no two owned fields
// overlap, and no parameter's value is a part of an owner a parameter
// reaches.
func (v *fnVerifier) separatePart(r *separation, i int, owner *types.Var) {
	t := v.frame[i]
	r.contains = partCells(t)
	r.direct = append(r.direct, passedValue{val: v.entry[owner], t: owner.Type()})
	for j, other := range v.frame {
		if j == i || !other.part || other.mod != t.mod || !other.sourcePart {
			continue
		}
		if cells := partCells(other); cells != nil {
			r.parts = append(r.parts, cells)
		}
	}
	r.cuts = v.ownedCells(v.entry[owner], owner.Type(), map[types.Type]bool{})
}

// ownedCells returns where, on entry, the owned cells of the struct a
// pointer to an owner of the project points to lie, and those of the
// structs it owns through owned pointer fields and holds by value.
func (v *fnVerifier) ownedCells(ptr value, t types.Type, seen map[types.Type]bool) [][2]*logic.Term {
	object, isPointer := pointee(t)
	if !isPointer || seen[object] {
		return nil
	}
	seen[object] = true
	defer delete(seen, object)
	var cuts [][2]*logic.Term
	for _, field := range v.inlineOwners(object) {
		cuts = append(cuts, v.ownedCells(field.at(ptr), field.ptr, seen)...)
	}
	cells := v.cellsOf(object)
	for _, index := range sourceOwnedFields(object) {
		lo, _, ok := fieldLeaves(object, index)
		if !ok || lo >= len(cells) {
			continue
		}
		cuts = append(cuts, [2]*logic.Term{ptr[0], logic.Add(ptr[1], logic.IntLit(cells[lo].off))})
		if ft := object.Underlying().(*types.Struct).Field(index).Type(); !isIface(ft) {
			if _, isPtr := pointee(ft); isPtr {
				if inner, _, ok := v.member(nil, memory{}, ptr, t, index); ok {
					cuts = append(cuts, v.ownedCells(inner, ft, seen)...)
				}
			}
		}
	}
	return cuts
}

// hasSourcePart reports whether a layer's targets hold a part of an owner
// of the project, at whose cells the separations are stated as for a
// footprint.
func hasSourcePart(targets []target) bool {
	return slices.ContainsFunc(targets, func(t target) bool { return t.sourcePart })
}

// partApartFromParams states, on entry, the direct cases of C3 for a part
// of an owner the function lists: the memory another parameter refers to
// directly, as a slice's stretch, a map, or a struct of the part's type,
// is not the part. The reach of separatePart says the same at a cell that
// a layer is asked about; these are what a store written directly, which
// no layer sees, needs.
func (v *fnVerifier) partApartFromParams(st *state, t target, owner *types.Var) {
	zero := logic.RefLit(0)
	for _, other := range v.fn.params {
		val := v.entry[other]
		if other == owner || val == nil {
			continue
		}
		ot := other.Type()
		var fact *logic.Term
		switch {
		case t.mapType != nil:
			if isMap(ot) && types.Identical(ot, t.mapType) {
				fact = logic.Or(logic.Eq(val[0], zero), logic.Eq(t.ref, zero), logic.Ne(val[0], t.ref))
			}
		case t.fp || t.row:
		case isSlice(ot) && t.elem != nil && types.Identical(elemType(ot), t.elem):
			lo, hi := v.extent(val, ot)
			fact = logic.Or(logic.Le(val[3], logic.IntLit(0)), logic.Eq(t.ref, zero), logic.Ne(val[0], t.ref), logic.Le(hi, t.lo), logic.Le(t.hi, lo))
		default:
			object, isPointer := pointee(ot)
			if !isPointer || !isStructType(object) {
				continue
			}
			inPart := logic.And(logic.Eq(val[0], t.ref), logic.Le(t.lo, val[1]), logic.Lt(val[1], t.hi))
			if t.base != nil && !types.Identical(untagged(object.Underlying()), untagged(t.base.t.Underlying())) && t.elem == nil {
				continue
			}
			fact = logic.Or(logic.Eq(val[0], zero), logic.Eq(t.ref, zero), logic.Not(inPart))
		}
		if fact != nil {
			st.assume(fact)
		}
	}
}

// checkOwnArguments proves E at a call of a verified function: no argument
// is memory that an owner owns where an owner whose parts can hold it is
// reached by any argument, itself included (R6; F2 of the design review).
// An argument that is outside or new, or a parameter of the caller, which
// the caller's own E covers, is no such memory, by HI; an inside argument,
// or one of no known origin, is refused unless the types show that no
// argument reaches an owner whose parts can hold it.
func (v *fnVerifier) checkOwnArguments(call *ast.CallExpr, name string) {
	fl := v.ownOrigins()
	if fl == nil {
		return
	}
	operands := fl.operands[call]
	owners := map[types.Type]bool{}
	typeOf := func(op ownOperand) types.Type {
		if t := v.info.TypeOf(op.expr); op.addr && t != nil {
			return types.NewPointer(t)
		}
		return v.info.TypeOf(op.expr)
	}
	for _, op := range operands {
		collectOwners(typeOf(op), owners, map[types.Type]bool{})
	}
	if len(owners) == 0 {
		return
	}
	for _, op := range operands {
		t := typeOf(op)
		if t == nil || !holdsMemory(t) || len(op.kind.inside) == 0 && op.kind.unknown == "" {
			continue
		}
		owner := ownerHolding(owners, t)
		if owner == nil {
			continue
		}
		what := "memory that an owner may own: " + op.kind.unknown
		for root := range op.kind.inside {
			what = "memory that " + v.rootName(root) + " owns"
			break
		}
		v.report(op.expr.Pos(), "%s is %s, and %s is handed what reaches a %s, which can own it; %s assumes that nothing it is handed is what "+
			"an owner it is handed owns: copy it, or pass it alone", types.ExprString(op.expr), what, name,
			types.TypeString(owner, types.RelativeTo(v.pass.Pkg)), name)
	}
}

// collectOwners adds the struct types that own memory by a declaration in
// source and that a value of type t is or reaches, through pointers,
// slices, maps, and fields, not through interface values.
func collectOwners(t types.Type, owners, seen map[types.Type]bool) {
	if t == nil || seen[t] {
		return
	}
	seen[t] = true
	if object, isPointer := pointee(t); isPointer {
		collectOwners(object, owners, seen)
		return
	}
	switch u := t.Underlying().(type) {
	case *types.Slice:
		collectOwners(u.Elem(), owners, seen)
	case *types.Map:
		collectOwners(u.Key(), owners, seen)
		collectOwners(u.Elem(), owners, seen)
	case *types.Struct:
		if len(sourceOwnedFields(t)) > 0 {
			owners[t] = true
		}
		for field := range u.Fields() {
			collectOwners(field.Type(), owners, seen)
		}
	}
}

// ownerHolding returns an owner among owners whose parts a value of type
// t can be or hold directly: a slice of an owned slice's type or a pointer
// to its elements, an owned map's type, a pointer of an owned pointer's
// type; a struct value by its fields.
func ownerHolding(owners map[types.Type]bool, t types.Type) types.Type {
	for owner := range owners {
		u := owner.Underlying().(*types.Struct)
		for _, index := range sourceOwnedFields(owner) {
			ft := u.Field(index).Type()
			switch {
			case types.Identical(ft, t):
				return owner
			case isSlice(ft):
				if object, isPointer := pointee(t); isPointer && types.Identical(object, elemType(ft)) {
					return owner
				}
			}
		}
	}
	if u, isStruct := t.Underlying().(*types.Struct); isStruct {
		for field := range u.Fields() {
			if holdsMemory(field.Type()) {
				if owner := ownerHolding(owners, field.Type()); owner != nil {
					return owner
				}
			}
		}
	}
	return nil
}
