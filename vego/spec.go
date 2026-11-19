package vego

import (
	"errors"
	"fmt"
	"go/token"
	"go/types"
	"strings"

	"github.com/spachava753/laas/vego/internal/logic"
)

// specEnv gives meaning to the names in an annotation. In a contract, a
// parameter denotes the value passed in and what it referred to on entry, a
// primed path what it refers to on return, and a result the returned value.
// Inside a body, a name denotes the current value of the variable in scope.
type specEnv struct {
	v *fnVerifier
	// sink receives what is learned by reading memory; it may be nil.
	sink *state
	// fn is the function whose contract is read, and args and results the
	// values of its parameters and results. results is nil where results may
	// not be mentioned. given and givenPost replace what a parameter denotes,
	// plain and primed, by a ready-made term, and givenResults what a result
	// denotes.
	fn           *funcInfo
	args         map[*types.Var]value
	results      []value
	given        map[*types.Var]*logic.Term
	givenPost    map[*types.Var]*logic.Term
	givenResults []*logic.Term
	// now is the memory plain paths are read from, and post the memory
	// primed paths and results are read from, nil where there is none.
	now, post memory
	// before is the number below which everything that existed before the
	// call lies, for fresh.
	before *logic.Term
	// self and selfType are set for an invariant: names are the fields of
	// the struct self is, or points to.
	self     value
	selfType types.Type
	// st and pos are set inside a body: names are looked up in the scope at
	// pos and denote their values in st.
	st  *state
	pos token.Pos
	// applied holds, for each function parameter of a trusted contract
	// that its ensures applies, the sequence of what it returns for each
	// argument; see Apply.
	applied map[*types.Var]*logic.Term
}

// Apply resolves f(x) in an ensures of a trusted contract, for a function
// parameter f with a contract under calls: what f returns for x, as the
// element x of a sequence that stands for f during the call. Any other
// name is a predicate.
func (e *specEnv) Apply(name string, args []*logic.Term) (*logic.Term, bool, error) {
	if e.fn == nil || e.fn.calls == nil {
		return nil, false, nil
	}
	param := e.fn.paramNames[name]
	cb := e.fn.calls[param]
	switch {
	case cb == nil:
		return nil, false, nil
	case !cb.applied:
		return nil, true, fmt.Errorf("%s cannot be applied here", name)
	case e.results == nil && e.givenResults == nil:
		return nil, true, fmt.Errorf("%s(...) can only be used in ensures", name)
	case len(args) != 1 || args[0].Sort != logic.Int:
		return nil, true, fmt.Errorf("%s takes one integer", name)
	}
	if e.applied == nil {
		e.applied = map[*types.Var]*logic.Term{}
	}
	if e.applied[param] == nil {
		sort, _ := sortOf(cb.sig.Results().At(0).Type())
		e.applied[param] = e.v.fresh("returns of "+name, logic.SeqOf(sort))
	}
	return logic.Select(e.applied[param], args[0]), true, nil
}

var errNoValue = errors.New("value of unsupported type")

// root resolves the name a path starts from. It returns either a value and
// its type or, for a constant, a finished term.
func (e *specEnv) root(name string) (val value, t types.Type, isResult bool, constant *logic.Term, err error) {
	if e.fn == nil {
		scope := e.v.pass.Pkg.Scope().Innermost(e.pos)
		if scope == nil {
			return nil, nil, false, nil, fmt.Errorf("unknown name %s", name)
		}
		_, obj := scope.LookupParent(name, e.pos)
		if variable, ok := obj.(*types.Var); ok {
			if val := e.st.vals[variable]; val != nil {
				if e.v.boxed[variable] {
					// The variable lives in memory and holds a pointer to
					// its value.
					val = e.v.fetch(e.sink, e.now, e.v.cellsOf(variable.Type()), val[0], val[1])
				}
				return val, variable.Type(), false, nil, nil
			}
			return nil, nil, false, nil, fmt.Errorf("%s cannot be used in annotations: its type %s is not supported", name, variable.Type())
		}
		constant, err = e.v.constantNamed(obj, name)
		return nil, nil, false, constant, err
	}
	if param, ok := e.fn.paramNames[name]; ok {
		if e.args[param] == nil {
			return nil, nil, false, nil, fmt.Errorf("parameter %s has type %s, which cannot be used in a contract", name, param.Type())
		}
		return e.args[param], param.Type(), false, nil, nil
	}
	if index, ok := e.fn.resultNames[name]; ok {
		if e.results == nil {
			return nil, nil, false, nil, fmt.Errorf("result %s can only be used in Ensures", name)
		}
		if e.results[index] == nil {
			return nil, nil, false, nil, errNoValue
		}
		return e.results[index], e.fn.results[index].Type(), true, nil, nil
	}
	constant, err = e.v.contractConstant(e.fn, name)
	return nil, nil, false, constant, err
}

// errorVariable resolves a name that, with the field after it for a
// package name, is a package-level error variable: one of this package, as
// ErrEmpty, or of another, as io.EOF. It reports whether the name is one.
// A contract keeps the meaning it had where it was written: a verified
// function sees the names of its file, an imported contract the variables
// its package recorded for its spellings, and a trusted contract the
// variables of the function's own package by name and those of any package
// in the build by its path; see trustedErrorVariable.
func (e *specEnv) errorVariable(name string, steps []logic.Step, when logic.When) (*logic.Term, bool, error) {
	var variable *types.Var
	rest := steps
	isResult := false
	if e.fn != nil {
		_, isResult = e.fn.resultNames[name]
	}
	switch {
	case e.fn == nil:
		scope := e.v.pass.Pkg.Scope().Innermost(e.pos)
		if scope == nil {
			return nil, false, nil
		}
		_, obj := scope.LookupParent(name, e.pos)
		variable, rest = e.v.packageErrorVariable(obj, steps)
	case e.fn.paramNames[name] != nil || isResult:
		return nil, false, nil
	case e.fn.trust != nil:
		var err error
		variable, rest, err = e.trustedErrorVariable(name, steps)
		if err != nil {
			return nil, true, err
		}
	case e.fn.imported != nil:
		spelled := name
		if len(steps) > 0 && steps[0].Field != "" {
			if key, ok := e.fn.imported.Errors[name+"."+steps[0].Field]; ok {
				spelled, rest = name+"."+steps[0].Field, steps[1:]
				variable = e.v.lookupKey(key)
				if variable == nil {
					return nil, true, fmt.Errorf("%s names %s, which is not known here", spelled, key)
				}
				break
			}
		}
		key, ok := e.fn.imported.Errors[spelled]
		if !ok {
			return nil, false, nil
		}
		if variable = e.v.lookupKey(key); variable == nil {
			return nil, true, fmt.Errorf("%s names %s, which is not known here", spelled, key)
		}
	default:
		// A function type has no declaration of a function; its contract
		// is read where the type is declared.
		at := e.fn.obj.Pos()
		if e.fn.decl != nil {
			at = e.fn.decl.Pos()
		}
		_, obj := e.v.pass.Pkg.Scope().Innermost(at).LookupParent(name, at)
		variable, rest = e.v.packageErrorVariable(obj, steps)
	}
	if variable == nil {
		return nil, false, nil
	}
	sentinel, err := e.errorVariableTerm(variable, rest, when)
	return sentinel, true, err
}

// trustedErrorVariable resolves a name in a trusted contract that is not a
// parameter or a result. A contract of a function means the same wherever it
// is used, whatever the package that declares the function imports, so a
// name is a package-level error variable of that package, and a name with a
// field after it is the variable of that name in the package of the build
// whose path is the name, as in io.EOF. A longer path is written in quotes;
// see Qualified.
func (e *specEnv) trustedErrorVariable(name string, steps []logic.Step) (*types.Var, []logic.Step, error) {
	if variable := errorVariableOf(e.fn.obj.Pkg().Scope().Lookup(name), ""); variable != nil {
		return variable, steps, nil
	}
	if len(steps) == 0 || steps[0].Field == "" {
		return nil, nil, nil
	}
	pkg := e.v.lookupPackage(name)
	if pkg == nil {
		return nil, nil, nil
	}
	variable := errorVariableOf(pkg.Scope().Lookup(steps[0].Field), "")
	if variable == nil {
		return nil, nil, fmt.Errorf("package %s has no package-level error variable %s", name, steps[0].Field)
	}
	return variable, steps[1:], nil
}

// Qualified resolves a variable named by the path of its package in quotes,
// which only a trusted contract may use, and only for a path that is not a
// Go identifier: io.EOF is written without quotes, and example.com, a path
// with a dot, with them.
func (e *specEnv) Qualified(path, name string, steps []logic.Step, when logic.When) (*logic.Term, error) {
	spelled := fmt.Sprintf("%q.%s", path, name)
	switch {
	case e.fn == nil || e.fn.trust == nil || e.selfType != nil:
		return nil, fmt.Errorf("%s: a package path in quotes can only be used in a trusted contract; name the package as the file imports it", spelled)
	case token.IsIdentifier(path):
		return nil, fmt.Errorf("%s: write %s.%s, without quotes", spelled, path, name)
	}
	pkg := e.v.lookupPackage(path)
	if pkg == nil {
		return nil, fmt.Errorf("%s: package %s is not in the build of this package", spelled, path)
	}
	variable := errorVariableOf(pkg.Scope().Lookup(name), "")
	if variable == nil {
		return nil, fmt.Errorf("%s: package %s has no package-level error variable %s", spelled, path, name)
	}
	return e.errorVariableTerm(variable, steps, when)
}

// errorVariableTerm returns the constant for a package-level error variable
// named in an annotation and followed by steps, which it cannot have.
func (e *specEnv) errorVariableTerm(variable *types.Var, rest []logic.Step, when logic.When) (*logic.Term, error) {
	switch {
	case len(rest) > 0 && rest[len(rest)-1].Len:
		return nil, fmt.Errorf("%s is an error and has no length", variable.Name())
	case len(rest) > 0:
		return nil, fmt.Errorf("%s is an error variable and has no fields or elements", variable.Name())
	case when != logic.Now:
		return nil, fmt.Errorf("%s is an error variable of a package, which cannot be primed or put in old()", variable.Name())
	}
	sentinel, why := e.v.sentinelTerm(e.sink, variable)
	if why != "" {
		return nil, errors.New(why)
	}
	return sentinel, nil
}

// packageErrorVariable returns the package-level error variable that an
// object is, or that its first step selects when it is a package name, and
// the steps after it.
func (v *fnVerifier) packageErrorVariable(obj types.Object, steps []logic.Step) (*types.Var, []logic.Step) {
	field := ""
	if _, isPackage := obj.(*types.PkgName); isPackage && len(steps) > 0 && steps[0].Field != "" {
		field, steps = steps[0].Field, steps[1:]
	}
	if variable := errorVariableOf(obj, field); variable != nil {
		return variable, steps
	}
	return nil, nil
}

// errorVariableOf returns the package-level error variable that an object
// is, or, when the object is a package name, the one of that package with
// the given name, or nil.
func errorVariableOf(obj types.Object, field string) *types.Var {
	if pkgName, ok := obj.(*types.PkgName); ok {
		if field == "" {
			return nil
		}
		obj = pkgName.Imported().Scope().Lookup(field)
	} else if field != "" {
		return nil
	}
	variable, ok := obj.(*types.Var)
	if !ok || variable.Pkg() == nil || variable.Parent() != variable.Pkg().Scope() || !isError(variable.Type()) {
		return nil
	}
	return variable
}

// reached is what a path leads to.
type reached struct {
	val      value
	typ      types.Type
	mem      memory // the memory the path was read from
	sink     *state // where facts about what it leads to may be noted; nil if it depends on a quantified variable
	isResult bool
	hops     int
	constant *logic.Term // set instead of val for a constant
}

// locate follows a path of an annotation through values and memory.
func (e *specEnv) locate(name string, steps []logic.Step, when logic.When) (reached, error) {
	if when == logic.Old && e.fn == nil {
		// Inside a body, old(x) is the value on entry of the function being
		// verified, which is how its own contract sees x.
		entry := &specEnv{v: e.v, sink: e.sink, fn: e.v.fn, args: e.v.entry, now: memory{}}
		param, isParam := e.v.fn.paramNames[name]
		if own := e.v.fn.ownParams; own != nil {
			// In a function literal verified on its own, old names its own
			// parameter, whatever the contract of its type calls it.
			param, isParam = own[name]
			renamed := *e.v.fn
			renamed.paramNames = own
			entry.fn = &renamed
		}
		if !isParam {
			return reached{}, fmt.Errorf("old(%s): %s is not a parameter", name, name)
		}
		// A variable declared in the body, such as a parameter of a
		// function literal, may hide the parameter here.
		if scope := e.v.pass.Pkg.Scope().Innermost(e.pos); scope != nil {
			if _, obj := scope.LookupParent(name, e.pos); obj != param {
				return reached{}, fmt.Errorf("old(%s): %s here is not the parameter of %s but a variable that hides it; rename the variable",
					name, name, e.v.fn.obj.Name())
			}
		}
		return entry.locate(name, steps, logic.Now)
	}
	if e.selfType != nil {
		return e.locateField(name, steps, when)
	}
	if sentinel, named, err := e.errorVariable(name, steps, when); named {
		return reached{constant: sentinel}, err
	}
	val, t, isResult, constant, err := e.root(name)
	switch {
	case err != nil:
		return reached{}, err
	case when == logic.Old && (isResult || constant != nil):
		return reached{}, fmt.Errorf("old(%s): %s is not a parameter", name, name)
	case constant != nil && len(steps) > 0:
		return reached{}, fmt.Errorf("%s is a constant and has no fields or elements", name)
	case constant != nil && when == logic.Primed:
		return reached{}, fmt.Errorf("%s' is not a program variable and cannot be primed", name)
	case constant != nil:
		return reached{constant: constant}, nil
	}
	hops, final, err := plan(t, steps)
	if err != nil {
		return reached{}, fmt.Errorf("%s%v", name, err)
	}
	mem := e.now
	switch {
	case isResult && when == logic.Primed:
		return reached{}, fmt.Errorf("%s is a result and already denotes the state on return; drop the prime", name)
	case isResult:
		mem = e.post
	case when == logic.Primed && e.fn == nil:
		return reached{}, fmt.Errorf("%s' is only allowed in Ensures; inside a body %s already denotes the current value", name, name)
	case when == logic.Primed && e.post == nil:
		return reached{}, fmt.Errorf("%s' describes the state on return and is only allowed in Ensures", name)
	case when == logic.Primed:
		if !reachesMemory(hops, final) {
			return reached{}, fmt.Errorf("%s is passed by value, so only its value on entry is visible to callers; drop the prime", name)
		}
		mem = e.post
	}
	cur, ground := e.v.follow(e.sink, mem, val, hops)
	found := reached{val: cur, typ: final, mem: mem, isResult: isResult, hops: len(hops)}
	if ground {
		found.sink = e.sink
	}
	return found, nil
}

// locateField follows a path of an invariant, which starts at a field of
// the value the invariant is stated of, or is a constant.
func (e *specEnv) locateField(name string, steps []logic.Step, when logic.When) (reached, error) {
	if when != logic.Now {
		return reached{}, fmt.Errorf("an invariant describes one state, so %s cannot be primed or put in old()", name)
	}
	hops, final, err := plan(e.selfType, append([]logic.Step{{Field: name}}, steps...))
	if err != nil {
		// A name that is a field stays a field, also when the field cannot
		// be used; only a name that is no field can be a constant.
		object := e.selfType
		if target, ok := pointee(object); ok {
			object = target
		}
		var home *types.Package
		if named, ok := types.Unalias(object).(*types.Named); ok {
			home = named.Obj().Pkg()
		}
		if found, _, _ := types.LookupFieldOrMethod(e.selfType, true, home, name); found != nil {
			return reached{}, errors.New(strings.TrimPrefix(err.Error(), "."))
		}
		if variable, _ := e.v.packageErrorVariable(e.v.pass.Pkg.Scope().Lookup(name), steps); variable != nil {
			return reached{}, fmt.Errorf("an invariant cannot name the error variable %s yet", name)
		}
		constant, constErr := e.v.contractConstant(e.fn, name)
		switch {
		case constErr != nil:
			return reached{}, fmt.Errorf("%s is neither a field of the type nor a constant", name)
		case len(steps) > 0:
			return reached{}, fmt.Errorf("%s is a constant and has no fields or elements", name)
		}
		return reached{constant: constant}, nil
	}
	cur, ground := e.v.follow(e.sink, e.now, e.self, hops)
	found := reached{val: cur, typ: final, mem: e.now, hops: len(hops)}
	if ground {
		found.sink = e.sink
	}
	return found, nil
}

// Path resolves a path of an annotation; see logic.Env. A path that ends in
// a slice of single values yields the sequence of its elements; one that
// ends in a struct, or in a slice of structs, has no value of its own.
func (e *specEnv) Path(name string, steps []logic.Step, when logic.When) (*logic.Term, error) {
	measured := len(steps) > 0 && steps[len(steps)-1].Len
	if measured {
		steps = steps[:len(steps)-1]
	}
	if asked := len(steps) > 0 && steps[len(steps)-1].Has; asked {
		// has(m, k): the path leads to the map, and the key is looked up.
		key := steps[len(steps)-1].Index
		found, err := e.locate(name, steps[:len(steps)-1], when)
		switch {
		case err != nil:
			return nil, err
		case found.constant != nil || !isMap(found.typ):
			return nil, fmt.Errorf("has(%s, ...): %s is not a map", spell(name, steps[:len(steps)-1]), spell(name, steps[:len(steps)-1]))
		case key.Sort != map[bool]logic.Sort{true: logic.IntSeq}[isString(found.typ.Underlying().(*types.Map).Key())]:
			return nil, fmt.Errorf("has(%s, ...): the key has type %s, which is not what the map is indexed by", name, key.Sort)
		}
		sink := found.sink
		if hasBound(key) {
			sink = nil
		}
		e.v.noteMap(sink, found.mem, found.typ, found.val[0], key)
		return e.v.mapHas(found.sink, found.mem, found.typ, found.val[0], key), nil
	}
	if base, ok := e.readyMade(name, when); ok {
		// A ready-made term stands for the parameter; it can only be indexed.
		for _, step := range steps {
			if step.Field != "" || !base.Sort.IsSeq() {
				return nil, fmt.Errorf("%s cannot be used this way here", name)
			}
			base = logic.Select(base, step.Index)
		}
		if measured && base.Sort.IsSeq() {
			base = logic.Len(base)
		}
		return base, nil
	}
	found, err := e.locate(name, steps, when)
	switch {
	case err != nil:
		return nil, err
	case measured && found.constant == nil && isSlice(found.typ):
		return found.val[2], nil
	case measured && found.constant == nil && isString(found.typ):
		return logic.Len(found.val[0]), nil
	case measured && found.constant == nil && isMap(found.typ):
		return e.v.mapLen(found.sink, found.mem, found.typ, found.val[0]), nil
	case measured:
		return nil, fmt.Errorf("%s is not a slice or a string and has no length", spell(name, steps))
	case found.constant != nil:
		return found.constant, nil
	}
	if isFunc(found.typ) {
		// A function value can only be compared with nil.
		return logic.FuncVal(found.val[0]), nil
	}
	if _, single := sortOf(found.typ); single {
		return found.val[0], nil
	}
	if object, isPointer := pointee(found.typ); isPointer {
		// Two pointers to values without size may or may not be equal, so
		// such a pointer can only be compared with nil.
		if e.v.pass.TypesSizes.Sizeof(object) == 0 {
			return logic.Pair(found.val[0], nil), nil
		}
		return logic.Pair(found.val[0], found.val[1]), nil
	}
	if isSlice(found.typ) {
		if seq, ok := e.v.view(found.sink, found.mem, found.val, found.typ); ok {
			return seq, nil
		}
		return nil, fmt.Errorf("%s is a slice of %s; index it and name a field", spell(name, steps), elemType(found.typ))
	}
	return nil, fmt.Errorf("%s is a %s; name one of its fields", spell(name, steps), found.typ)
}

// readyMade returns the term that was given for a parameter or a result in
// place of a value, if one was.
func (e *specEnv) readyMade(name string, when logic.When) (*logic.Term, bool) {
	if e.fn == nil || e.given == nil {
		return nil, false
	}
	if index, isResult := e.fn.resultNames[name]; isResult && index < len(e.givenResults) {
		return e.givenResults[index], true
	}
	param, isParam := e.fn.paramNames[name]
	if !isParam || e.given[param] == nil {
		return nil, false
	}
	if when == logic.Primed {
		return e.givenPost[param], e.givenPost[param] != nil
	}
	return e.given[param], true
}

// reachesMemory reports whether a path reads anything from memory, which is
// the only thing that can differ between entry and return for a parameter.
func reachesMemory(hops []hop, final types.Type) bool {
	for _, h := range hops {
		if _, viaPointer := pointee(h.from); viaPointer || (h.field < 0 && (isSlice(h.from) || isMap(h.from))) {
			return true
		}
	}
	return isSlice(final) || isMap(final)
}

// Relation resolves fresh(x) and within(a, b); see logic.Env.
func (e *specEnv) Relation(name string, paths []logic.Path) (*logic.Term, error) {
	if e.given != nil {
		return nil, fmt.Errorf("%s cannot be used here", name)
	}
	found := make([]reached, len(paths))
	for i, path := range paths {
		var err error
		if found[i], err = e.locate(path.Root, path.Steps, path.When); err != nil {
			return nil, err
		}
		spelled := spell(path.Root, path.Steps)
		_, isPointer := pointee(found[i].typ)
		switch {
		case found[i].constant != nil || (!isPointer && !isSlice(found[i].typ) && !isMap(found[i].typ)):
			return nil, fmt.Errorf("%s(%s): %s is not a pointer, a slice, or a map", name, spelled, spelled)
		case name == "within" && isMap(found[i].typ):
			return nil, fmt.Errorf("within(%s): %s is a map, and nothing lies within a map or holds one", spelled, spelled)
		}
	}
	first := found[0].val
	if name == "within" {
		// Inside means inside the capacity, which is what a write through
		// a slice, or an append to it, can reach. A slice without capacity
		// reaches nothing, and so lies within anything; a nil pointer
		// points nowhere, and so lies within nothing.
		outer := found[1].val
		firstStart, firstEnd := e.v.extent(first, found[0].typ)
		outerStart, outerEnd := e.v.extent(outer, found[1].typ)
		inside := logic.And(logic.Eq(first[0], outer[0]), logic.Le(outerStart, firstStart), logic.Le(firstEnd, outerEnd))
		if isSlice(found[0].typ) {
			return logic.Or(logic.Le(first[3], logic.IntLit(0)), inside), nil
		}
		return logic.And(logic.Not(logic.Eq(first[0], logic.RefLit(0))), inside), nil
	}
	if e.before == nil || e.post == nil {
		return nil, errors.New("fresh says what a call created and is only allowed in Ensures")
	}
	if found[0].hops == 0 && !found[0].isResult {
		return nil, fmt.Errorf("fresh(%s): %s was passed in, so the call did not create it", paths[0].Root, paths[0].Root)
	}
	// What a path leads to on return is what the call may have created.
	after, err := e.locate(paths[0].Root, paths[0].Steps, map[bool]logic.When{false: logic.Primed}[found[0].isResult])
	if err != nil {
		return nil, err
	}
	if isSlice(after.typ) {
		// A slice without capacity shares nothing with anything either.
		return logic.Or(logic.Le(after.val[3], logic.IntLit(0)), logic.Le(e.before, after.val[0])), nil
	}
	return logic.Le(e.before, after.val[0]), nil
}

// spell writes a path the way an annotation does.
func spell(name string, steps []logic.Step) string {
	for _, step := range steps {
		if step.Field != "" {
			name += "." + step.Field
		} else {
			name += "[" + step.Index.String() + "]"
		}
	}
	return name
}

// hop is one step of a path through values and memory: the selection of a
// field, by its index in the struct, or of an element.
type hop struct {
	from  types.Type // the type the step applies to: a struct, a pointer to one, a slice, or a string
	field int        // -1 for an element
	index *logic.Term
}

// plan checks a path against the type it starts from, and returns its hops
// and the type it ends in. A field promoted from an embedded struct takes
// one hop for each struct on the way.
func plan(t types.Type, steps []logic.Step) ([]hop, types.Type, error) {
	var hops []hop
	spelled := ""
	for _, step := range steps {
		if step.Field == "" {
			keyed := isMap(t) && mapModelled(t)
			if want := map[bool]logic.Sort{true: logic.IntSeq}[keyed && isString(t.Underlying().(*types.Map).Key())]; step.Index != nil && step.Index.Sort != want {
				return nil, nil, fmt.Errorf("%s: the index has type %s, which is not what a %s is indexed by", spelled, step.Index.Sort, t)
			}
			switch {
			case keyed:
				hops = append(hops, hop{from: t, field: -1, index: step.Index})
				_, t = mapParts(t)
			case isSlice(t):
				hops = append(hops, hop{from: t, field: -1, index: step.Index})
				t = elemType(t)
				if _, ok := layoutOf(t); !ok {
					return nil, nil, fmt.Errorf("%s has type %s, which is not supported", spelled, t)
				}
			case isString(t):
				hops = append(hops, hop{from: t, field: -1, index: step.Index})
				t = types.Typ[types.Uint8]
			default:
				return nil, nil, fmt.Errorf("%s: a %s cannot be indexed", spelled, t)
			}
			spelled += "[...]"
			continue
		}
		object := t
		if target, ok := pointee(t); ok {
			object = target
		}
		if _, ok := object.Underlying().(*types.Struct); !ok {
			return nil, nil, fmt.Errorf("%s.%s: a %s has no fields", spelled, step.Field, t)
		}
		var home *types.Package
		if named, ok := types.Unalias(object).(*types.Named); ok {
			home = named.Obj().Pkg()
		}
		found, path, _ := types.LookupFieldOrMethod(t, true, home, step.Field)
		if _, ok := found.(*types.Var); !ok {
			return nil, nil, fmt.Errorf("%s.%s: %s has no field %s", spelled, step.Field, object, step.Field)
		}
		spelled += "." + step.Field
		for _, index := range path {
			hops = append(hops, hop{from: t, field: index})
			object = t
			if target, ok := pointee(t); ok {
				object = target
			}
			t = object.Underlying().(*types.Struct).Field(index).Type()
		}
		if _, ok := layoutOf(t); !ok {
			return nil, nil, fmt.Errorf("%s has type %s, which is not supported", spelled, t)
		}
	}
	return hops, t, nil
}

// follow reads a path, without the checks execution makes: an annotation
// may speak of p.f where p is nil, and then says nothing useful. It reports
// false when the path depends on a quantified variable; nothing can then be
// noted about the memory it reads.
func (v *fnVerifier) follow(sink *state, mem memory, cur value, hops []hop) (value, bool) {
	ground := true
	for _, h := range hops {
		reads := sink
		if !ground {
			reads = nil
		}
		switch {
		case h.field >= 0:
			cur, _, _ = v.member(reads, mem, cur, h.from, h.field)
		case isMap(h.from):
			if !ground {
				reads = nil
			}
			cur = v.mapValue(reads, mem, h.from, cur[0], h.index)
			ground = ground && !hasBound(h.index)
		case isSlice(h.from):
			// The array is known as long as the slice is, whatever the
			// index.
			cur, _ = v.element(reads, mem, cur, h.from, h.index)
			ground = ground && !hasBound(h.index)
		default:
			ground = ground && !hasBound(h.index)
			cur = value{logic.Select(cur[0], h.index)}
		}
	}
	return cur, ground
}

// hasBound reports whether a term mentions a quantified variable.
func hasBound(t *logic.Term) bool {
	if t.Op == logic.OpBound {
		return true
	}
	for _, arg := range t.Args {
		if hasBound(arg) {
			return true
		}
	}
	return false
}

// modTarget is one entry of a Modifies clause.
type modTarget struct {
	name string // the parameter the path starts from
	// steps holds, for each step of the path, the name of a field or the
	// index of an element.
	steps  []modStep
	text   string
	clause *clause
}

type modStep struct {
	field string
	index *logic.Node
}

// newModTargets turns the parsed list of a Modifies clause into targets.
func newModTargets(nodes []*logic.Node, c *clause) []*modTarget {
	var list []*modTarget
	for _, node := range nodes {
		target := &modTarget{text: c.text[node.Start:node.End], clause: c}
		for n := node; ; n = n.Kids[0] {
			if n.Kind == logic.NIdent {
				target.name = n.Name
				break
			}
			step := modStep{field: n.Name}
			if n.Kind == logic.NIndex {
				step = modStep{index: n.Kids[1]}
			}
			target.steps = append([]modStep{step}, target.steps...)
		}
		list = append(list, target)
	}
	return list
}

// shape describes a Modifies entry without evaluating it: which regions it
// reaches into, and how its positions follow from the value of a parameter
// when the entry names what that parameter itself points to or holds.
type shape struct {
	param *types.Var
	cells []cell
	// elem is set for the elements of a slice and mapType for a map; else
	// the entry is a struct or a part of one.
	elem    types.Type
	mapType types.Type
	// direct is set when the allocation is the one the parameter itself
	// points into or holds, and not one read out of memory. For a pointer,
	// lo and hi then bound the positions from where the pointer points.
	direct bool
	lo, hi int64
}

// located is where a path has led: a value, and, while the value lies in
// memory, the allocation, the position of the struct or element it is part
// of, and its cells counted from there.
type located struct {
	val   value
	typ   types.Type
	ref   *logic.Term
	at    *logic.Term
	cells []cell
}

// locateTarget follows the path of a Modifies entry. With mem nil it only
// follows the types, which is enough to tell what kind of memory the entry
// covers. A path that ends in a pointer means the whole struct it points to;
// one that ends in a slice means the elements of the slice, up to its
// capacity; one that ends in a map means the map; any other path must lead
// to something that lies in memory, and means that.
func (v *fnVerifier) locateTarget(fn *funcInfo, m *modTarget, args map[*types.Var]value, sink *state, mem memory) (shape, target, error) {
	param, ok := fn.paramNames[m.name]
	if !ok {
		return shape{}, target{}, fmt.Errorf("%s is not a parameter", m.name)
	}
	symbolic := mem == nil
	if !symbolic && args[param] == nil {
		return shape{}, target{}, fmt.Errorf("parameter %s has type %s, which is not supported", m.name, param.Type())
	}
	steps := make([]logic.Step, len(m.steps))
	for i, step := range m.steps {
		steps[i] = logic.Step{Field: step.field}
		if step.index == nil {
			continue
		}
		// What is indexed decides what the index is: a map with strings for
		// keys takes a string, everything else a number.
		_, indexed, err := plan(param.Type(), steps[:i])
		if err != nil {
			return shape{}, target{}, fmt.Errorf("%s%v", m.name, err)
		}
		want, placeholder := logic.Int, logic.IntLit(0)
		if isMap(indexed) && isString(indexed.Underlying().(*types.Map).Key()) {
			want, placeholder = logic.IntSeq, logic.Fill(logic.IntLit(0), logic.IntLit(0))
		}
		steps[i].Index = placeholder
		if !symbolic {
			index, err := v.resolverOf(m.clause).Term(step.index, &specEnv{v: v, sink: sink, fn: fn, args: args, now: mem}, want)
			if err != nil && want == logic.IntSeq {
				return shape{}, target{}, fmt.Errorf("a %s is indexed by a string: %w", indexed, err)
			}
			if err != nil {
				return shape{}, target{}, err
			}
			steps[i].Index = index
		}
	}
	hops, final, err := plan(param.Type(), steps)
	if err != nil {
		return shape{}, target{}, fmt.Errorf("%s%v", m.name, err)
	}
	// Follow the hops, keeping track of where the value lies. first is set
	// while the allocation is still the one the parameter points into.
	cur := located{val: args[param], typ: param.Type()}
	first, inMemory := true, false
	for i, h := range hops {
		object, viaPointer := pointee(h.from)
		switch {
		case h.field >= 0 && viaPointer:
			lo, hi, _ := fieldLeaves(object, h.field)
			first, inMemory = i == 0, true
			if !symbolic {
				cur.ref, cur.at = cur.val[0], cur.val[1]
				cur.val, _, _ = v.member(sink, mem, cur.val, h.from, h.field)
			}
			cur.cells = v.cellsOf(object)[lo:hi]
		case h.field >= 0:
			lo, hi, _ := fieldLeaves(h.from, h.field)
			if !symbolic {
				cur.val = cur.val[lo:hi]
			}
			if inMemory {
				cur.cells = cur.cells[lo:hi]
			}
		case isSlice(h.from):
			first, inMemory = false, true
			if !symbolic {
				cur.ref, cur.at = cur.val[0], v.elementAt(cur.val, h.from, h.index)
				cur.val, _ = v.element(sink, mem, cur.val, h.from, h.index)
			}
			cur.cells = v.cellsOf(elemType(h.from))
		default:
			// What a map has for a key, or a byte of a string, is no place
			// that can be written through this path.
			inMemory = false
			if !symbolic && isMap(h.from) {
				cur.val = v.mapValue(sink, mem, h.from, cur.val[0], h.index)
			}
		}
	}
	form := shape{param: param}
	t := target{text: m.text, clause: m.clause}
	object, isPointer := pointee(final)
	switch {
	case isPointer:
		form.cells, form.direct, form.hi = v.cellsOf(object), len(hops) == 0, v.pass.TypesSizes.Sizeof(object)
		if !symbolic {
			t.ref, t.lo, t.hi = cur.val[0], cur.val[1], logic.Add(cur.val[1], logic.IntLit(form.hi))
		}
		t.single = true
	case isSlice(final):
		form.cells, form.elem, form.direct = v.cellsOf(elemType(final)), elemType(final), len(hops) == 0
		if !symbolic {
			t.ref = cur.val[0]
			t.lo, t.hi = v.extent(cur.val, final)
		}
	case isMap(final):
		form.mapType, form.direct = final, len(hops) == 0
		if !symbolic {
			t.ref = cur.val[0]
		}
	case !inMemory:
		return shape{}, target{}, fmt.Errorf("%s is passed by value, so the caller cannot see a change to it", m.text)
	default:
		form.cells, form.direct = cur.cells, first
		form.lo, form.hi = bounds(cur.cells)
		if !symbolic {
			t.ref, t.lo, t.hi = cur.ref, logic.Add(cur.at, logic.IntLit(form.lo)), logic.Add(cur.at, logic.IntLit(form.hi))
			// The cells are counted from the struct, the target from its
			// first position.
			shifted := make([]cell, len(cur.cells))
			for i, c := range cur.cells {
				shifted[i] = cell{key: c.key, sort: c.sort, off: c.off - form.lo}
			}
			form.cells = shifted
		}
		t.single = true
	}
	t.cells, t.elem, t.mapType = form.cells, form.elem, form.mapType
	if form.direct && len(m.steps) == 0 {
		t.param = param
	}
	return form, t, nil
}

// targets evaluates the Modifies clauses of a function for the given
// arguments, reading memory as it is when the function is entered.
func (v *fnVerifier) targets(fn *funcInfo, args map[*types.Var]value, sink *state, mem memory) []target {
	var list []target
	for _, m := range fn.modifies {
		_, t, err := v.locateTarget(fn, m, args, sink, mem)
		if err != nil {
			v.misread(m.clause, err)
		}
		list = append(list, t)
	}
	return list
}
