package vego

import (
	"errors"
	"fmt"
	"go/token"
	"go/types"
	"golang.org/x/tools/go/analysis"
	"maps"
	"slices"
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
	// givenState replaces the state of a parameter or a result, plain or
	// primed, by a ready-made term, where given is set.
	givenState func(param *types.Var, state string, when logic.When) *logic.Term
	// givenRelation resolves fresh and within where given is set, which
	// otherwise cannot be read there; the tests of shipped entries answer
	// it from what they saw.
	givenRelation func(name string, paths []logic.Path) (*logic.Term, error)
	// givenSlice resolves cap(A) and A = nil of a parameter or a result,
	// and |m| of a map, where given is set; the tests of shipped entries
	// answer it from the real slice or map.
	givenSlice func(name string, last logic.Step, when logic.When) (*logic.Term, error)
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
	if e.fn == nil || e.fn.calls.len() == 0 {
		return nil, false, nil
	}
	param := e.fn.paramNames[name]
	cb := e.fn.calls.get(param)
	switch {
	case cb == nil:
		return nil, false, nil
	case !cb.applied:
		return nil, true, entryDefect{fmt.Errorf("%s cannot be applied here", name)}
	case e.results == nil && e.givenResults == nil:
		return nil, true, entryDefect{fmt.Errorf("%s(...) can only be used in ensures", name)}
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

// Applies reports whether name is a function parameter with a contract
// under calls, which Apply gives a meaning; see logic.Applier.
func (e *specEnv) Applies(name string) bool {
	return e.fn != nil && e.fn.calls.len() > 0 && e.fn.calls.get(e.fn.paramNames[name]) != nil
}

var errNoValue = errors.New("value of unsupported type")

// root resolves the name a path starts from. It returns either a value and
// its type or, for a constant, a finished term.
func (e *specEnv) root(name string) (val value, t types.Type, isResult bool, constant *logic.Term, err error) {
	if e.fn == nil {
		scope := e.v.scopeAt(e.pos)
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
			return nil, nil, false, nil, entryDefect{fmt.Errorf("result %s can only be used in Ensures", name)}
		}
		if e.results[index] == nil {
			return nil, nil, false, nil, errNoValue
		}
		return e.results[index], e.fn.results[index].Type(), true, nil, nil
	}
	constant, err = e.v.contractConstant(e.fn.spelling(), name)
	if err != nil {
		// A name that is no parameter, result, or constant is unknown
		// whatever the types of the parameters.
		err = entryDefect{err}
	}
	return nil, nil, false, constant, err
}

// packageVariable resolves a name that, with the field after it for a
// package name, is a package-level variable: one of this package, as
// ErrEmpty or limit, or of another, as io.EOF. It reports whether the name
// is one, and returns the steps after it. A contract keeps the meaning it
// had where it was written: a verified function sees the names of its
// file, an imported contract the variables its package recorded for its
// spellings, and a trusted contract the error variables of the function's
// own package by name and those of any package in the build by its path;
// see trustedErrorVariable. Only error variables may be named in a trusted
// contract or a contract of a type.
func (e *specEnv) packageVariable(name string, steps []logic.Step) (*types.Var, []logic.Step, bool, error) {
	var variable *types.Var
	rest := steps
	isResult := false
	if e.fn != nil {
		_, isResult = e.fn.resultNames[name]
	}
	switch {
	case e.fn == nil:
		scope := e.v.scopeAt(e.pos)
		if scope == nil {
			return nil, nil, false, nil
		}
		_, obj := scope.LookupParent(name, e.pos)
		variable, rest = e.v.packageVariableNamed(obj, steps)
	case e.fn.paramNames[name] != nil || isResult:
		return nil, nil, false, nil
	case e.fn.spelling().trust != nil:
		var err error
		variable, rest, err = e.trustedErrorVariable(name, steps)
		if err != nil {
			return nil, nil, true, err
		}
	case e.fn.spelling().imported != nil:
		imported := e.fn.spelling().imported
		spelled := name
		if len(steps) > 0 && steps[0].Field != "" {
			if key, ok := imported.Errors[name+"."+steps[0].Field]; ok {
				spelled, rest = name+"."+steps[0].Field, steps[1:]
				variable = e.v.lookupKey(key)
				if variable == nil {
					return nil, nil, true, fmt.Errorf("%s names %s, which is not known here", spelled, key)
				}
				break
			}
		}
		key, ok := imported.Errors[spelled]
		if !ok {
			return nil, nil, false, nil
		}
		if variable = e.v.lookupKey(key); variable == nil {
			return nil, nil, true, fmt.Errorf("%s names %s, which is not known here", spelled, key)
		}
	default:
		// A function type has no declaration of a function; its contract
		// is read where the type is declared.
		at := e.fn.spelling().obj.Pos()
		if decl := e.fn.spelling().decl; decl != nil {
			at = decl.Pos()
		}
		_, obj := e.v.pass.Pkg.Scope().Innermost(at).LookupParent(name, at)
		variable, rest = e.v.packageVariableNamed(obj, steps)
		if variable != nil && !isError(variable.Type()) && (e.fn.spelling().valueOf != nil || e.fn.spelling().methodOf != nil) {
			return nil, nil, true, fmt.Errorf("a contract of a function type or of a method of an interface cannot name the package-level variable %s yet",
				e.v.spelling(variable))
		}
	}
	if variable == nil {
		return nil, nil, false, nil
	}
	return variable, rest, true, nil
}

// trustedErrorVariable resolves a name in a trusted contract that is not a
// parameter or a result. A contract of a function means the same wherever it
// is used, whatever the package that declares the function imports, so a
// name is a package-level error variable of that package, and a name with a
// field after it is the variable of that name in the package of the build
// whose path is the name, as in io.EOF. A longer path is written in quotes;
// see Qualified.
func (e *specEnv) trustedErrorVariable(name string, steps []logic.Step) (*types.Var, []logic.Step, error) {
	if variable := errorVariableOf(e.fn.spelling().obj.Pkg().Scope().Lookup(name), ""); variable != nil {
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
	case e.fn == nil || e.fn.spelling().trust == nil || e.selfType != nil:
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
	if variable, rest := v.packageVariableNamed(obj, steps); variable != nil && isError(variable.Type()) {
		return variable, rest
	}
	return nil, nil
}

// packageVariableNamed returns the package-level variable that an object
// is, or that its first step selects when it is a package name, and the
// steps after it.
func (v *fnVerifier) packageVariableNamed(obj types.Object, steps []logic.Step) (*types.Var, []logic.Step) {
	field := ""
	if _, isPackage := obj.(*types.PkgName); isPackage && len(steps) > 0 && steps[0].Field != "" {
		field, steps = steps[0].Field, steps[1:]
	}
	if variable := packageVariableOf(obj, field); variable != nil {
		return variable, steps
	}
	return nil, nil
}

// errorVariableOf returns the package-level error variable that an object
// is, or, when the object is a package name, the one of that package with
// the given name, or nil.
func errorVariableOf(obj types.Object, field string) *types.Var {
	if variable := packageVariableOf(obj, field); variable != nil && isError(variable.Type()) {
		return variable
	}
	return nil
}

// packageVariableOf returns the package-level variable that an object is,
// or, when the object is a package name, the one of that package with the
// given name, or nil.
func packageVariableOf(obj types.Object, field string) *types.Var {
	if pkgName, ok := obj.(*types.PkgName); ok {
		if field == "" {
			return nil
		}
		obj = pkgName.Imported().Scope().Lookup(field)
	} else if field != "" {
		return nil
	}
	variable, ok := obj.(*types.Var)
	if !ok || variable.Pkg() == nil || variable.Parent() != variable.Pkg().Scope() {
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
	// start is the value the path starts from and path its hops, which
	// the address of what it leads to is computed from; see address.
	start value
	path  []hop
}

// writtenIn returns the package the annotation was written in: the package
// of the function inside a body, that of the type for an invariant, and
// that of the contract otherwise; nil for a contract shipped with vego.
func (e *specEnv) writtenIn() *types.Package {
	switch {
	case e.selfType != nil:
		object := e.selfType
		if target, ok := pointee(object); ok {
			object = target
		}
		if named, ok := types.Unalias(object).(*types.Named); ok {
			return named.Obj().Pkg()
		}
		return e.v.pass.Pkg
	case e.fn == nil:
		return e.v.pass.Pkg
	}
	return e.fn.writtenIn()
}

// locate follows a path of an annotation through values and memory.
func (e *specEnv) locate(name string, steps []logic.Step, when logic.When) (reached, error) {
	return e.locateAt(name, steps, when, false)
}

// locateAt is locate. With throughPointer, a path that ends in a pointer to
// a struct reads memory, since what is asked of it is read where it points.
func (e *specEnv) locateAt(name string, steps []logic.Step, when logic.When, throughPointer bool) (reached, error) {
	if e.fn == nil && e.st != nil {
		if c := e.v.visitedAt(name, e.pos); c != nil {
			return reached{}, fmt.Errorf("%s is the set of keys that the loop has visited; a formula reads it only as |%s|, has(%s, k), and in Forall k in %s", name, name, name, name)
		}
		if c := e.v.snapshotAt(name, e.pos); c != nil {
			taken, ok := e.st.snapshots[c]
			switch {
			case when != logic.Now:
				return reached{}, fmt.Errorf("%s is a snapshot, which has one value; it cannot be primed or put in old()", name)
			case len(steps) > 0:
				return reached{}, fmt.Errorf("%s is a snapshot of an integer or a boolean, and has no fields or elements", name)
			case !ok:
				panic(fmt.Sprintf("vego: internal error: the snapshot %s is read where it was not taken", name))
			}
			return reached{constant: taken}, nil
		}
	}
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
		if scope := e.v.scopeAt(e.pos); scope != nil {
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
	if variable, rest, named, err := e.packageVariable(name, steps); named {
		switch {
		case err != nil:
			return reached{}, err
		case isError(variable.Type()):
			sentinel, err := e.errorVariableTerm(variable, rest, when)
			return reached{constant: sentinel}, err
		}
		return e.locateVariable(variable, rest, when)
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
	hops, final, err := plan(t, steps, e.writtenIn())
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
		_, pointer := pointee(final)
		// A state of what a pointer points to, or of what an interface
		// value holds, lies in memory.
		if !reachesMemory(hops, final) && !(throughPointer && (pointer || isIface(final))) {
			return reached{}, fmt.Errorf("%s is passed by value, so only its value on entry is visible to callers; drop the prime", name)
		}
		mem = e.post
	}
	cur, ground := e.v.follow(e.sink, mem, val, hops)
	found := reached{val: cur, typ: final, mem: mem, isResult: isResult, hops: len(hops), start: val, path: hops}
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
	hops, final, err := plan(e.selfType, append([]logic.Step{{Field: name}}, steps...), e.writtenIn())
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
		if variable, _ := e.v.packageVariableNamed(e.v.pass.Pkg.Scope().Lookup(name), steps); variable != nil {
			if isError(variable.Type()) {
				return reached{}, fmt.Errorf("an invariant cannot name the error variable %s yet", name)
			}
			return reached{}, fmt.Errorf("an invariant cannot name the package-level variable %s yet", name)
		}
		constant, constErr := e.v.contractConstant(e.fn.spelling(), name)
		switch {
		case constErr != nil:
			return reached{}, fmt.Errorf("%s is neither a field of the type nor a constant", name)
		case len(steps) > 0:
			return reached{}, fmt.Errorf("%s is a constant and has no fields or elements", name)
		}
		return reached{constant: constant}, nil
	}
	cur, ground := e.v.follow(e.sink, e.now, e.self, hops)
	found := reached{val: cur, typ: final, mem: e.now, hops: len(hops), start: e.self, path: hops}
	if ground {
		found.sink = e.sink
	}
	return found, nil
}

// Path resolves a path of an annotation; see logic.Env. A path that ends in
// a slice of single values yields the sequence of its elements; one that
// ends in a struct, or in a slice of structs, has no value of its own.
func (e *specEnv) Path(name string, steps []logic.Step, when logic.When) (*logic.Term, error) {
	if e.fn == nil && e.st != nil {
		if c := e.v.visitedAt(name, e.pos); c != nil {
			return e.visitedPath(c, steps, when)
		}
	}
	if err := e.genericPath(name, steps); err != nil {
		return nil, err
	}
	if last := len(steps) - 1; last >= 0 && steps[last].ElemSize {
		return e.elemSize(name, steps[:last], when)
	}
	if _, ok := e.readyMade(name, when); ok && len(steps) == 1 && (steps[0].Keys || steps[0].Has) && e.givenSlice != nil {
		// The keys of a map a parameter or a result holds, which the
		// tests of shipped entries answer from the real map.
		return e.givenSlice(name, steps[0], when)
	}
	if last := len(steps) - 1; last >= 0 && steps[last].Keys {
		found, err := e.locate(name, steps[:last], when)
		switch {
		case err != nil:
			return nil, err
		case found.constant != nil || !isMap(found.typ):
			return nil, fmt.Errorf("%s is not a map, so a quantifier cannot range over its keys; it ranges over Z, an interval, or the keys of a map", spell(name, steps[:last]))
		}
		return keyPlaceholder(found.typ), nil
	}
	if last := len(steps) - 1; last >= 0 && steps[last].State != "" {
		return e.state(name, steps[:last], steps[last].State, when)
	}
	if e.fn != nil && e.fn.receiver != nil && e.fn.paramNames[name] == e.fn.receiver {
		example := "closed"
		if states := e.v.ifaceStatesOf(e.fn.receiver.Type()); len(states) > 0 {
			example = states[0].name
		}
		return nil, fmt.Errorf("%s names the receiver, which a contract can use only as the argument of a state, as in %s(%s), and in Modifies",
			name, example, name)
	}
	if last := len(steps) - 1; last >= 0 && (steps[last].Cap || steps[last].Nil || steps[last].Addr) {
		return e.sliceOrAddress(name, steps[:last], steps[last], when)
	}
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
		case key.Sort != keyPlaceholder(found.typ).Sort:
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
		if measured && len(steps) == 0 && !base.Sort.IsSeq() && e.givenSlice != nil {
			// The number of keys of a map.
			return e.givenSlice(name, logic.Step{Len: true}, when)
		}
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
	if isIface(found.typ) {
		// So can an interface value: two that are not nil may hold the
		// same value under different references.
		return logic.IfaceVal(found.val[0]), nil
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
	if generic := e.genericAt(name, steps); generic != nil {
		return nil, fmt.Errorf("a value of type %s, which is %s here, is a struct, and a formula cannot compare a struct or use it as a whole",
			generic.Obj().Name(), types.TypeString(found.typ, types.RelativeTo(e.v.pass.Pkg)))
	}
	return nil, fmt.Errorf("%s is a %s; name one of its fields", spell(name, steps), found.typ)
}

// genericAt returns, in the contract of an instantiation of a generic
// function, the type parameter that a path leads to in the generic
// signature, or nil.
func (e *specEnv) genericAt(name string, steps []logic.Step) *types.TypeParam {
	if e.fn == nil || e.fn.genericTypes == nil {
		return nil
	}
	root, isParam := e.fn.paramNames[name]
	if index, isResult := e.fn.resultNames[name]; isResult && !isParam {
		root = e.fn.results[index]
	}
	t := e.fn.genericTypes[root]
	for _, step := range steps {
		switch u := coreType(t).(type) {
		case *types.Slice:
			t = u.Elem()
		case *types.Map:
			t = u.Elem()
		default:
			return nil
		}
		if step.Field != "" {
			return nil
		}
	}
	param, _ := types.Unalias(t).(*types.TypeParam)
	return param
}

// genericPath refuses, in the contract of an instantiation of a generic
// function, a path that names a field, a state, or the address of a value
// whose type in the generic signature is a type parameter; see
// throughTypeParam.
func (e *specEnv) genericPath(name string, steps []logic.Step) error {
	if e.fn == nil || e.fn.genericTypes == nil {
		return nil
	}
	root, isParam := e.fn.paramNames[name]
	if index, isResult := e.fn.resultNames[name]; isResult && !isParam {
		root = e.fn.results[index]
	}
	if root == nil || e.fn.genericTypes[root] == nil {
		return nil
	}
	return throughTypeParam(name, e.fn.genericTypes[root], steps, e.v.stateNamed)
}

// elemSize resolves elemsize(A): the size in bytes of an element of the
// slice A on the target, which depends only on its type and reads nothing.
// For a slice of values of size zero it is 0.
func (e *specEnv) elemSize(name string, steps []logic.Step, when logic.When) (*logic.Term, error) {
	what := spell(name, steps)
	var t types.Type
	if _, ok := e.readyMade(name, when); ok {
		root, isParam := e.fn.paramNames[name]
		if index, isResult := e.fn.resultNames[name]; isResult && !isParam {
			root = e.fn.results[index]
		}
		_, final, err := plan(root.Type(), steps, e.writtenIn())
		if err != nil {
			return nil, fmt.Errorf("%s%v", name, err)
		}
		t = final
	} else {
		found, err := e.locate(name, steps, when)
		if err != nil {
			return nil, err
		}
		if found.constant == nil {
			t = found.typ
		}
	}
	if t == nil || !isSlice(t) {
		return nil, fmt.Errorf("elemsize(%s): %s is not a slice; elemsize is the size of an element of a slice", what, what)
	}
	return logic.IntLit(e.v.pass.TypesSizes.Sizeof(elemType(t))), nil
}

// sliceOrAddress resolves cap(A), A = nil for a slice A, and &x.f: the
// capacity, whether the slice is nil, as code's A == nil asks it, and the
// address of a struct that the path reaches through memory.
func (e *specEnv) sliceOrAddress(name string, steps []logic.Step, last logic.Step, when logic.When) (*logic.Term, error) {
	what := spell(name, steps)
	if _, ok := e.readyMade(name, when); ok {
		if e.givenSlice != nil && len(steps) == 0 && !last.Addr {
			return e.givenSlice(name, last, when)
		}
		if last.Nil {
			return nil, logic.NotSlice
		}
		return nil, fmt.Errorf("%s cannot be used this way here", name)
	}
	found, err := e.locate(name, steps, when)
	switch {
	case err != nil:
		return nil, err
	case last.Nil && found.constant == nil && isString(found.typ):
		return nil, fmt.Errorf("%s is a string, which is never nil; compare |%s| with 0", what, what)
	case last.Nil && (found.constant != nil || !isSlice(found.typ)):
		return nil, logic.NotSlice
	case last.Nil:
		e.v.noteNamed(found.val[0], " = nil")
		return isNilRef(found.val), nil
	case last.Cap && (found.constant != nil || !isSlice(found.typ)):
		return nil, fmt.Errorf("cap(%s): %s is not a slice; only a slice has a capacity", what, what)
	case last.Cap:
		e.v.noteNamed(found.val[3], "")
		return found.val[3], nil
	}
	return e.address(what, found)
}

// noteNamed records that a formula names the capacity of a slice, or
// compares it with nil: the search for an input on which a contract forces
// success then also tries slices with more capacity than length, or nil
// ones; see addSlice. What is recorded is the constant the part was read
// from: the part itself for a slice the function holds, and the region for
// one that lies in memory, as a field behind a pointer or an element does,
// which is the name the sample gives that part.
func (v *fnVerifier) noteNamed(part *logic.Term, how string) {
	for part.Op == logic.OpSelect {
		part = part.Args[0]
	}
	if part.Op != logic.OpConst {
		return
	}
	if v.namedInFormulas == nil {
		v.namedInFormulas = map[string]bool{}
	}
	v.namedInFormulas[part.Name+how] = true
}

// address returns the pointer to what a path leads to, as code's &x.f
// computes it: the allocation and position of the struct or element that
// the last pointer or slice of the path leads into, and the offsets of the
// fields selected in it since. Nothing is read beyond that pointer or
// slice, and nothing is checked: for a nil pointer it is a pointer with the
// allocation 0, which is nil, where Go would panic.
func (e *specEnv) address(what string, found reached) (*logic.Term, error) {
	_, isStruct := types.Unalias(found.typ).Underlying().(*types.Struct)
	if found.constant != nil || !isStruct {
		return nil, fmt.Errorf("&%s: %s has type %s, and & gives only pointers to structs", what, what, found.typ)
	}
	cur, ground := found.start, true
	var ref, at *logic.Term
	var offset int64
	inMemory := false
	for i, h := range found.path {
		reads := e.sink
		if !ground {
			reads = nil
		}
		object, viaPointer := pointee(h.from)
		switch {
		case h.field >= 0 && viaPointer:
			ref, at, offset, inMemory = cur[0], cur[1], e.v.fieldOffset(object, h.field), true
		case h.field >= 0:
			offset += e.v.fieldOffset(h.from, h.field)
		case isSlice(h.from):
			ref, at, offset, inMemory = cur[0], e.v.elementAt(cur, h.from, h.index), 0, true
		default:
			inMemory = false
		}
		if i < len(found.path)-1 {
			next, _ := e.v.follow(reads, found.mem, cur, found.path[i:i+1])
			cur = next
			ground = ground && (h.index == nil || !hasBound(h.index))
		}
	}
	if !inMemory {
		return nil, fmt.Errorf("&%s: %s is not reached through a pointer or an element of a slice, so it has no address a formula can name", what, what)
	}
	if e.v.pass.TypesSizes.Sizeof(found.typ) == 0 {
		// Two pointers to values without size may or may not be equal, as
		// for a pointer read from memory.
		return logic.Pair(ref, nil), nil
	}
	return logic.Pair(ref, logic.Add(at, logic.IntLit(offset))), nil
}

// state resolves name(x) for a state of a struct, read from the value x or
// where the pointer x points; see stateDecl.
func (e *specEnv) state(name string, steps []logic.Step, state string, when logic.When) (*logic.Term, error) {
	if !e.v.stateNamed(state) {
		return nil, &logic.NoState{}
	}
	what := spell(name, steps)
	if e.givenState != nil && e.fn != nil && len(steps) == 0 {
		if param, isParam := e.fn.paramNames[name]; isParam {
			if t := e.givenState(param, state, when); t != nil {
				return t, nil
			}
		}
		if index, isResult := e.fn.resultNames[name]; isResult {
			if t := e.givenState(e.fn.results[index], state, when); t != nil {
				return t, nil
			}
		}
	}
	found, err := e.locateAt(name, steps, when, true)
	switch {
	case err != nil:
		return nil, err
	case found.constant != nil:
		return nil, &logic.NoState{Msg: fmt.Sprintf("%s(%s): %s is a constant and has no state", state, what, what)}
	case isIface(found.typ):
		return e.ifaceState(what, found.typ, found.val[0], found.sink, found.mem, state)
	}
	object, viaPointer := pointee(found.typ)
	if !viaPointer {
		object = found.typ
	}
	var decls []stateDecl
	if u, isStruct := object.Underlying().(*types.Struct); isStruct {
		decls = statesOf(u)
	}
	index := slices.IndexFunc(decls, func(d stateDecl) bool { return d.name == state })
	if index < 0 {
		has := "no states"
		if len(decls) == 1 {
			has = "the state " + decls[0].name
		}
		if len(decls) > 1 {
			names := make([]string, len(decls))
			for i, d := range decls {
				names[i] = d.name
			}
			has = "the states " + strings.Join(names, ", ")
		}
		return nil, &logic.NoState{Msg: fmt.Sprintf("%s(%s): %s is a %s, which has %s", state, what, what, found.typ, has)}
	}
	leaves, _ := layoutOf(object)
	position := len(leaves) - len(decls) + index
	if !viaPointer {
		return found.val[position], nil
	}
	return e.v.fetch(found.sink, found.mem, e.v.cellsOf(object)[position:position+1], found.val[0], found.val[1])[0], nil
}

// stateNamed reports whether some type that the package can see has a
// state of the name: a struct or interface of the shipped files, an
// interface of the project's trust file, of this package, or of a package
// it is built with.
func (pv *pkgVerifier) stateNamed(name string) bool {
	if stateNamed(name) || (pv.projectTrust != nil && slices.ContainsFunc(slices.Collect(maps.Values(pv.projectTrust.states)),
		func(decls []stateDecl) bool {
			return slices.ContainsFunc(decls, func(d stateDecl) bool { return d.name == name })
		})) {
		return true
	}
	if pv.importedStateNames == nil {
		pv.importedStateNames = map[string]bool{}
		var facts []analysis.ObjectFact
		if pv.pass.AllObjectFacts != nil {
			facts = pv.pass.AllObjectFacts()
		}
		built := map[*types.Package]bool{}
		var visit func(pkg *types.Package)
		visit = func(pkg *types.Package) {
			if !built[pkg] {
				built[pkg] = true
				for _, imported := range pkg.Imports() {
					visit(imported)
				}
			}
		}
		visit(pv.pass.Pkg)
		for _, fact := range facts {
			if states, ok := fact.Fact.(*stateFact); ok && built[fact.Object.Pkg()] {
				for _, n := range states.Names {
					pv.importedStateNames[n] = true
				}
			}
		}
	}
	for _, states := range pv.ownStates {
		if slices.ContainsFunc(states, func(s ifaceState) bool { return s.name == name }) {
			return true
		}
	}
	return pv.importedStateNames[name]
}

// stateNamed reports whether some type has a state of the name in the
// shipped files.
func stateNamed(name string) bool {
	for _, byType := range shippedStates() {
		for _, decls := range byType {
			if slices.ContainsFunc(decls, func(d stateDecl) bool { return d.name == name }) {
				return true
			}
		}
	}
	return false
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
	if e.given != nil && e.givenRelation != nil {
		return e.givenRelation(name, paths)
	}
	if e.given != nil {
		return nil, fmt.Errorf("%s cannot be used here", name)
	}
	found := make([]reached, len(paths))
	for i, path := range paths {
		var err error
		if err := e.genericPath(path.Root, path.Steps); err != nil {
			return nil, err
		}
		if found[i], err = e.locate(path.Root, path.Steps, path.When); err != nil {
			return nil, err
		}
		spelled := spell(path.Root, path.Steps)
		_, isPointer := pointee(found[i].typ)
		switch {
		case name == "apart" && (found[i].constant != nil || !isSlice(found[i].typ)):
			return nil, fmt.Errorf("apart(%s, ...): %s is not a slice; apart says that two slices share no memory", spelled, spelled)
		case name == "apart":
		case name == "fresh" && found[i].constant == nil && isIface(found[i].typ):
			// The states of an interface value lie at its home, which
			// is new when what it holds is.
		case found[i].constant != nil || (!isPointer && !isSlice(found[i].typ) && !isMap(found[i].typ)):
			if name == "fresh" {
				return nil, fmt.Errorf("fresh(%s): %s is not a pointer, a slice, a map, or an interface value", spelled, spelled)
			}
			return nil, fmt.Errorf("%s(%s): %s is not a pointer, a slice, or a map", name, spelled, spelled)
		case name == "within" && isMap(found[i].typ):
			return nil, fmt.Errorf("within(%s): %s is a map, and nothing lies within a map or holds one", spelled, spelled)
		}
	}
	first := found[0].val
	if name == "apart" {
		// What two slices may reach, up to their capacities, does not
		// meet: the assumption made of slice parameters, by the same term.
		a, b := elemType(found[0].typ), elemType(found[1].typ)
		if typeKey(a) != typeKey(b) {
			return nil, fmt.Errorf("apart(%s, %s): a slice of %s and a slice of %s never share memory, so there is nothing to state",
				spell(paths[0].Root, paths[0].Steps), spell(paths[1].Root, paths[1].Steps),
				types.TypeString(a, types.RelativeTo(e.v.pass.Pkg)), types.TypeString(b, types.RelativeTo(e.v.pass.Pkg)))
		}
		return e.v.separate(first, found[1].val, found[0].typ), nil
	}
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
		// A pointer to a struct inside a struct lies where a field of its
		// type does: without unsafe, the bytes of the outer struct are its
		// fields and nothing else. A slice target covers a range, so this
		// matters only for a pointer within a pointer.
		object, _ := pointee(found[0].typ)
		if outerObject, isPointer := pointee(found[1].typ); isPointer && e.v.pass.TypesSizes.Sizeof(object) > 0 {
			offsets := e.v.offsetsOf(outerObject, object)
			if len(offsets) == 0 {
				return nil, fmt.Errorf("within(%s, %s): no field of %s, at any depth, has the type %s, so %s cannot lie within %s",
					spell(paths[0].Root, paths[0].Steps), spell(paths[1].Root, paths[1].Steps),
					types.TypeString(outerObject, types.RelativeTo(e.v.pass.Pkg)), types.TypeString(object, types.RelativeTo(e.v.pass.Pkg)),
					spell(paths[0].Root, paths[0].Steps), spell(paths[1].Root, paths[1].Steps))
			}
			var at []*logic.Term
			for _, offset := range offsets {
				at = append(at, logic.Eq(first[1], logic.Add(outer[1], logic.IntLit(offset))))
			}
			return logic.And(logic.Not(logic.Eq(first[0], logic.RefLit(0))), logic.Eq(first[0], outer[0]), logic.Or(at...)), nil
		}
		return logic.And(logic.Not(logic.Eq(first[0], logic.RefLit(0))), inside), nil
	}
	where := "is allowed in an Ensures, where it says what the call allocated, and in an Invariant or an Assert inside a body, " +
		"where it says what the function allocated since it was entered"
	switch {
	case e.selfType != nil:
		return nil, fmt.Errorf("an invariant of a type describes one state, so it cannot say what was allocated since a call began; fresh %s", where)
	case e.fn == nil && e.st != nil:
		// Inside a body, what the path leads to now was allocated since the
		// function was entered: the bound the check of every write uses
		// for memory the function may write without a Modifies entry.
		return freshSince(e.v.entryBrk, found[0]), nil
	case e.before == nil || e.post == nil:
		return nil, fmt.Errorf("fresh says what was allocated since a call began, and nothing has been allocated where this annotation is read; fresh %s", where)
	case found[0].hops == 0 && !found[0].isResult:
		return nil, fmt.Errorf("fresh(%s): %s was passed in, so the call did not create it", paths[0].Root, paths[0].Root)
	}
	// What a path leads to on return is what the call may have created.
	after, err := e.locate(paths[0].Root, paths[0].Steps, map[bool]logic.When{false: logic.Primed}[found[0].isResult])
	if err != nil {
		return nil, err
	}
	return freshSince(e.before, after), nil
}

// freshSince states that what a value refers to was allocated at or past a
// bound. A slice without capacity shares nothing with anything, and a nil
// interface value holds nothing, so both count as fresh; a nil pointer or
// map does not, so fresh(p) gives p != nil.
func freshSince(before *logic.Term, found reached) *logic.Term {
	switch {
	case isIface(found.typ):
		return logic.Or(isNilRef(found.val), logic.Le(before, home(found.val[0])))
	case isSlice(found.typ):
		return logic.Or(logic.Le(found.val[3], logic.IntLit(0)), logic.Le(before, found.val[0]))
	}
	return logic.Le(before, found.val[0])
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
// one hop for each struct on the way. from is the package the formula was
// written in, nil for a contract shipped with vego: only there may it name
// an unexported field.
func plan(t types.Type, steps []logic.Step, from *types.Package) ([]hop, types.Type, error) {
	var hops []hop
	spelled := ""
	for _, step := range steps {
		if step.Field == "" {
			keyed := isMap(t) && mapModelled(t)
			want := logic.Int
			if keyed {
				want = keyPlaceholder(t).Sort
			}
			if step.Index != nil && step.Index.Sort != want {
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
			field := object.Underlying().(*types.Struct).Field(index)
			if !field.Exported() && (from == nil || field.Pkg() == nil || field.Pkg().Path() != from.Path()) {
				return nil, nil, unexportedField(spelled, field, object, from)
			}
			t = field.Type()
		}
		if _, ok := layoutOf(t); !ok {
			return nil, nil, fmt.Errorf("%s has type %s, which is not supported", spelled, t)
		}
	}
	return hops, t, nil
}

// unexportedField reports a path that names an unexported field of a struct
// declared in another package than the formula. Such a field may change
// between versions of Go or of the module, and what another goroutine may
// do to it, as to the fields of a sync.Mutex, is not known; a formula speaks
// of such a type through its exported fields and its states.
func unexportedField(spelled string, field *types.Var, object types.Type, from *types.Package) error {
	where := "a contract shipped with vego"
	if from != nil {
		where = "package " + from.Path()
	}
	instead := ""
	if u, ok := object.Underlying().(*types.Struct); ok {
		if decls := statesOf(u); len(decls) > 0 {
			instead = fmt.Sprintf("; %s has the state %s, which a formula names as %s(x) for a value or a pointer x", object, decls[0].name, decls[0].name)
		}
	}
	return fmt.Errorf("%s: %s is an unexported field of %s, declared in package %s, and a formula in %s cannot name it%s",
		spelled, field.Name(), object, field.Pkg().Path(), where, instead)
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
	// row is set for the states of an interface value.
	row   bool
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
		if variable := v.modifiesVariable(fn, m); variable != nil {
			return shape{}, target{}, fmt.Errorf("%s is a package-level variable, which a Modifies clause cannot name yet", v.spelling(variable))
		}
		return shape{}, target{}, fmt.Errorf("%s is not a parameter", m.name)
	}
	if generic := fn.genericTypes[param]; generic != nil {
		steps := make([]logic.Step, len(m.steps))
		for i, step := range m.steps {
			steps[i] = logic.Step{Field: step.field}
			if step.index != nil {
				steps[i].Index = logic.IntLit(0)
			}
		}
		if err := throughTypeParam(m.name, generic, steps, v.stateNamed); err != nil {
			return shape{}, target{}, err
		}
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
		_, indexed, err := plan(param.Type(), steps[:i], fn.writtenIn())
		if err != nil {
			return shape{}, target{}, fmt.Errorf("%s%v", m.name, err)
		}
		want, placeholder := logic.Int, logic.IntLit(0)
		if isMap(indexed) {
			placeholder = keyPlaceholder(indexed)
			want = placeholder.Sort
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
	hops, final, err := plan(param.Type(), steps, fn.writtenIn())
	if err != nil {
		return shape{}, target{}, fmt.Errorf("%s%v", m.name, err)
	}
	// Follow the hops, keeping track of where the value lies. first is set
	// while the allocation is still the one the parameter points into.
	cur := located{val: args[param], typ: param.Type()}
	first, inMemory := true, false
	// entry is set while the path is at a key of a map, which a path that
	// ends there names: whether the map has the key, what it holds there,
	// and how many keys the map has.
	type mapEntry struct {
		t        types.Type
		ref, key *logic.Term
		direct   bool
	}
	var entry *mapEntry
	afterEntry := false
	for i, h := range hops {
		if entry != nil {
			entry, afterEntry = nil, true
		}
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
			// What a map has for a key is an entry of the map, and a byte
			// of a string no place that can be written through this path.
			inMemory = false
			if isMap(h.from) {
				entry = &mapEntry{t: h.from, direct: i == 0}
				if !symbolic {
					entry.ref, entry.key = cur.val[0], mapKey(h.index)
					cur.val = v.mapValue(sink, mem, h.from, cur.val[0], h.index)
				}
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
	case isIface(final):
		// Every state of what the interface value holds, which lies in
		// the row of its home; see ifacestate.go. The value itself, a
		// field or an element, is not part of it.
		if fn.trust == nil && !v.hasStates(final) {
			return shape{}, target{}, fmt.Errorf("%s has type %s, which has no states; an entry for an interface value covers the states of what it holds, "+
				"and to assign %s itself, list what holds it", m.text, final, m.text)
		}
		form.cells, form.direct, form.row = []cell{stateCell}, len(hops) == 0, true
		if inMemory {
			t.holder = cur.cells
		}
		if !symbolic {
			t.ref = home(cur.val[0])
		}
		t.row = true
	case entry != nil:
		// An entry of a map whose values are not references: the entry of
		// one whose values are is covered by the map, since the path names
		// what such a value refers to.
		form.mapType, form.direct = entry.t, entry.direct
		if !symbolic {
			t.ref, t.key = entry.ref, entry.key
		}
	case afterEntry && !inMemory:
		return shape{}, target{}, fmt.Errorf("%s is part of a value that a map holds, which a Modifies clause names only as a whole entry of the map", m.text)
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
