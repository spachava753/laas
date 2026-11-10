package vego

import (
	"errors"
	"fmt"
	"go/token"
	"go/types"
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
		if _, isParam := e.v.fn.paramNames[name]; !isParam {
			return reached{}, fmt.Errorf("old(%s): %s is not a parameter", name, name)
		}
		return entry.locate(name, steps, logic.Now)
	}
	if e.selfType != nil {
		return e.locateField(name, steps, when)
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
	case measured:
		return nil, fmt.Errorf("%s is not a slice or a string and has no length", spell(name, steps))
	case found.constant != nil:
		return found.constant, nil
	}
	if _, single := sortOf(found.typ); single {
		return found.val[0], nil
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
		if _, viaPointer := pointee(h.from); viaPointer || (h.field < 0 && isSlice(h.from)) {
			return true
		}
	}
	return isSlice(final)
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
		case found[i].constant != nil || (!isPointer && !isSlice(found[i].typ)):
			return nil, fmt.Errorf("%s(%s): %s is not a pointer or a slice", name, spelled, spelled)
		case name == "within" && !isSlice(found[i].typ):
			return nil, fmt.Errorf("within(%s): %s is not a slice", spelled, spelled)
		}
	}
	first := found[0].val
	if name == "within" {
		// Inside means inside the capacity, which is what a write through
		// the slice, or an append to it, can reach. A slice without
		// capacity reaches nothing.
		outer := found[1].val
		inside := logic.And(logic.Eq(first[0], outer[0]), logic.Le(outer[1], first[1]),
			logic.Le(logic.Add(first[1], first[3]), logic.Add(outer[1], outer[3])))
		return logic.Or(logic.Le(first[3], logic.IntLit(0)), inside), nil
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
			switch {
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

// shape describes a Modifies entry without evaluating it: the type and
// fields it covers, and whether the object or array it names is the very
// one a parameter holds, as opposed to something read out of memory.
type shape struct {
	typ    types.Type
	elems  bool
	prefix string
	param  *types.Var
	direct bool
	// hops lead from the parameter to the pointer or slice that is the
	// target, or whose object holds the fields that are.
	hops []hop
}

// shapeOf type-checks a Modifies entry against the function's signature. A
// path that ends in a pointer means the whole object it points to; one that
// ends in a slice means the elements of the slice, up to its capacity; any
// other path must name a field of an object reached through a pointer, and
// means that field.
//
// indices holds the values of the indices the entry mentions, in order; it
// may be nil when only the kind of memory matters and not which.
func (fn *funcInfo) shapeOf(m *modTarget, indices []*logic.Term) (shape, error) {
	param, ok := fn.paramNames[m.name]
	if !ok {
		return shape{}, fmt.Errorf("%s is not a parameter", m.name)
	}
	steps := make([]logic.Step, len(m.steps))
	for i, step := range m.steps {
		steps[i] = logic.Step{Field: step.field}
		if step.index != nil {
			steps[i].Index = logic.IntLit(0)
			if len(indices) > 0 {
				steps[i].Index, indices = indices[0], indices[1:]
			}
		}
	}
	hops, final, err := plan(param.Type(), steps)
	if err != nil {
		return shape{}, fmt.Errorf("%s%v", m.name, err)
	}
	if object, ok := pointee(final); ok {
		return shape{typ: object, param: param, direct: len(hops) == 0, hops: hops}, nil
	}
	if isSlice(final) {
		return shape{typ: elemType(final), elems: true, param: param, direct: len(hops) == 0, hops: hops}, nil
	}
	// The last hop through a pointer decides which object the field is in.
	last := -1
	for i, h := range hops {
		if _, viaPointer := pointee(h.from); viaPointer {
			last = i
		}
	}
	single := slices.ContainsFunc(hops[max(last, 0):], func(h hop) bool { return h.field < 0 })
	switch {
	case single:
		return shape{}, fmt.Errorf("%s is a single element or part of one; list the slice instead", m.text)
	case last < 0:
		return shape{}, fmt.Errorf("%s is passed by value, so the caller cannot see a change to it", m.text)
	}
	object, _ := pointee(hops[last].from)
	prefix, t := "", object
	for _, h := range hops[last:] {
		field := t.Underlying().(*types.Struct).Field(h.field)
		prefix += "." + field.Name()
		t = field.Type()
	}
	return shape{typ: object, prefix: prefix, param: param, direct: last == 0, hops: hops[:last]}, nil
}

// targets evaluates the Modifies clauses of a function for the given
// arguments, reading memory as it is when the function is entered.
func (v *fnVerifier) targets(fn *funcInfo, args map[*types.Var]value, sink *state, mem memory) []target {
	var list []target
	for _, m := range fn.modifies {
		env := &specEnv{v: v, sink: sink, fn: fn, args: args, now: mem}
		var indices []*logic.Term
		for _, step := range m.steps {
			if step.index == nil {
				continue
			}
			index, err := v.resolverOf(m.clause).IntTerm(step.index, env)
			if err != nil {
				v.misread(m.clause, err)
			}
			indices = append(indices, index)
		}
		form, err := fn.shapeOf(m, indices)
		if err == nil && args[form.param] == nil {
			err = fmt.Errorf("parameter %s has type %s, which is not supported", m.name, form.param.Type())
		}
		if err != nil {
			v.misread(m.clause, err)
		}
		cur, _ := v.follow(sink, mem, args[form.param], form.hops)
		t := target{typ: form.typ, elems: form.elems, prefix: form.prefix, ref: cur[0], text: m.text, clause: m.clause}
		if form.direct && len(m.steps) == 0 {
			t.param = form.param
		}
		if form.elems {
			t.lo, t.hi = cur[1], logic.Add(cur[1], cur[3])
		}
		list = append(list, t)
	}
	return list
}
