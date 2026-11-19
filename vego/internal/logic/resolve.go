package logic

import (
	"errors"
	"fmt"
	"slices"
	"sort"
)

// When says in which state of the program a path is read.
type When int

// The states an annotation can speak about.
const (
	Now    When = iota // the state the annotation describes
	Primed             // the state on return, written x' in the annotation
	Old                // the state on function entry, written old(x)
)

// Step is one step of a path: the selection of a field, of the element at
// Index, or, as the last step, of the length or, with Has, of whether a map
// has the key Index.
type Step struct {
	Field string
	Index *Term
	Len   bool
	Has   bool
}

// Env supplies the meaning of program names that occur in an annotation.
type Env interface {
	// Path returns the value reached from a program variable by selecting
	// fields and elements.
	Path(root string, steps []Step, when When) (*Term, error)
	// Relation returns a formula about the identity of the pointers or
	// slices that paths lead to: "fresh" states that what one path refers to
	// was created during the call, and "within" that the memory the first
	// of two paths refers to lies inside that of the second.
	Relation(name string, paths []Path) (*Term, error)
	// Qualified returns the value of a variable named by the path of its
	// package in quotes, as in "io/fs".ErrNotExist, followed by steps.
	Qualified(path, name string, steps []Step, when When) (*Term, error)
}

// Applier is an Env that gives a meaning to some applications, as f(i) for
// a function that a trusted contract names. Apply reports whether it knows
// the name; a name it does not know is a predicate.
type Applier interface {
	Apply(name string, args []*Term) (t *Term, known bool, err error)
}

// Path is a path together with the state it is read in.
type Path struct {
	Root  string
	Steps []Step
	When  When
}

// PredDef is a resolved user-defined predicate.
type PredDef struct {
	Name   string
	Params []*Term // bound variables standing for the parameters
	Body   *Term
}

// Resolver type-checks parsed annotations and turns them into terms.
type Resolver struct {
	// Preds holds the defined predicates by the name their applications
	// carry in terms, which is Prefix followed by the name in annotations.
	Preds map[string]*PredDef
	// Prefix keeps the predicates of different packages apart when their
	// terms meet in one proof.
	Prefix string
	fresh  int
}

// NewResolver returns a resolver with no predicates defined.
func NewResolver() *Resolver { return &Resolver{Preds: map[string]*PredDef{}} }

type scope struct {
	r     *Resolver
	env   Env
	bound map[string]*Term
}

func (r *Resolver) newBound(name string, sort Sort) *Term {
	r.fresh++
	return Bound(fmt.Sprintf("%s#%d", name, r.fresh), sort)
}

// Formula resolves a parsed clause that must be a formula.
func (r *Resolver) Formula(n *Node, env Env) (*Term, error) {
	return r.resolve(n, env, nil, Bool)
}

// IntTerm resolves a parsed clause that must be an integer expression.
func (r *Resolver) IntTerm(n *Node, env Env) (*Term, error) {
	return r.resolve(n, env, nil, Int)
}

// Term resolves a parsed expression that must have the given sort.
func (r *Resolver) Term(n *Node, env Env, want Sort) (*Term, error) {
	return r.resolve(n, env, nil, want)
}

func (r *Resolver) resolve(n *Node, env Env, bound map[string]*Term, want Sort) (t *Term, err error) {
	defer func() {
		if recovered := recover(); recovered != nil {
			resolveErr, ok := recovered.(resolveError)
			if !ok {
				panic(recovered)
			}
			t, err = nil, resolveErr.err
		}
	}()
	s := &scope{r: r, env: env, bound: bound}
	return s.expect(n, want), nil
}

type resolveError struct{ err error }

func fail(format string, args ...any) {
	panic(resolveError{fmt.Errorf(format, args...)})
}

// kindOf names what a term of a formula stands for, as a message should
// call it. A reference is a pointer, a function value, or, when it is
// neither, a map: those are the only references a path gives.
func kindOf(t *Term) string {
	switch {
	case t.Op == OpIntLit && t.Sort == Ref && t.Val == 0:
		return "nil"
	case t.Op == OpFuncVal:
		return "function value"
	case t.Op == OpPair:
		return "pointer"
	case t.Sort == Ref:
		return "map"
	}
	return t.Sort.String()
}

func (s *scope) expect(n *Node, want Sort) *Term {
	t := s.term(n)
	if t.Sort != want {
		fail("expected %s but %s has type %s", describe(want), n, kindOf(t))
	}
	return t
}

func describe(sort Sort) string {
	switch sort {
	case Bool:
		return "a formula"
	case Int:
		return "an integer"
	case Err:
		return "an error"
	}
	return "a slice or a string"
}

// term resolves one syntax node, checking operand sorts along the way.
func (s *scope) term(n *Node) *Term {
	switch n.Kind {
	case NInt:
		return BigLit(n.Big)
	case NNil:
		return NilErr()
	case NStr:
		return Bytes(n.Name)
	case NBool:
		return BoolLit(n.Val == 1)
	case NIdent, NField, NIndex:
		return s.access(n, Now)
	case NCall:
		return s.call(n)
	case NLen:
		return s.length(n.Kids[0])
	case NUnary:
		if n.Op == "-" {
			return Neg(s.expect(n.Kids[0], Int))
		}
		return Not(s.expect(n.Kids[0], Bool))
	case NBinary:
		return s.binary(n)
	case NCompare:
		var parts []*Term
		for i, op := range n.Ops {
			parts = append(parts, s.compare(op, n.Kids[i], n.Kids[i+1]))
		}
		return And(parts...)
	case NQuant:
		return s.quantifier(n)
	}
	fail("a slice range such as A[lo:hi) can only be used as an operand of a comparison")
	return nil
}

func (s *scope) seq(n *Node) *Term {
	t := s.term(n)
	if !t.Sort.IsSeq() {
		fail("%s has type %s, not a slice", n, kindOf(t))
	}
	return t
}

// length resolves |x|. The length of something reached from a program
// variable is asked of the environment, which also knows the length of a
// slice whose elements have no value in the logic.
func (s *scope) length(n *Node) *Term {
	root, steps, primed := s.path(n)
	_, bound := s.bound[root.Name]
	if (n.Kind != NIdent && n.Kind != NField && n.Kind != NIndex) || root.Kind != NIdent || bound || s.env == nil {
		return Len(s.seq(n))
	}
	t, err := s.env.Path(root.Name, append(steps, Step{Len: true}), map[bool]When{true: Primed}[primed])
	if err != nil {
		panic(resolveError{err})
	}
	return t
}

// path splits a chain of field selections and indexing into the node it
// starts from and its steps, and reports whether any part of it is primed.
func (s *scope) path(n *Node) (root *Node, steps []Step, primed bool) {
	switch n.Kind {
	case NField:
		root, steps, primed = s.path(n.Kids[0])
		return root, append(steps, Step{Field: n.Name}), primed || n.Primed
	case NIndex:
		root, steps, primed = s.path(n.Kids[0])
		// What may index depends on what is indexed: a number for a slice,
		// and for a map whatever its keys are.
		return root, append(steps, Step{Index: s.term(n.Kids[1])}), primed
	}
	return n, nil, n.Kind == NIdent && n.Primed
}

// access resolves a name, possibly followed by field selections and
// indexing. A path that starts at a program variable is handed to the
// environment as a whole, since only the program knows its fields; anything
// else can only be indexed.
func (s *scope) access(n *Node, when When) *Term {
	root, steps, primed := s.path(n)
	_, bound := s.bound[root.Name]
	if root.Kind == NStr && len(steps) > 0 && steps[0].Field != "" && s.env != nil {
		if primed {
			when = Primed
		}
		t, err := s.env.Qualified(root.Name, steps[0].Field, steps[1:], when)
		if err != nil {
			panic(resolveError{err})
		}
		return t
	}
	if root.Kind != NIdent || bound {
		var base *Term
		switch {
		case root.Kind != NIdent:
			base = s.term(root)
		case primed:
			fail("%s' is not a program variable and cannot be primed", root.Name)
		default:
			base = s.bound[root.Name]
		}
		for _, step := range steps {
			if step.Field != "" {
				fail("%s has no field %s", root, step.Field)
			}
			if !base.Sort.IsSeq() {
				fail("%s has type %s and cannot be indexed", root, kindOf(base))
			}
			if step.Index.Sort != Int {
				fail("%s is indexed by a %s, not by an integer", root, step.Index.Sort)
			}
			base = Select(base, step.Index)
		}
		return base
	}
	if s.env == nil {
		fail("unknown name %s in predicate definition; predicates may only mention their parameters", root.Name)
	}
	if primed {
		if when == Old {
			fail("old(%s) is the value on entry and cannot be primed", root.Name)
		}
		when = Primed
	}
	t, err := s.env.Path(root.Name, steps, when)
	if err != nil {
		panic(resolveError{err})
	}
	return t
}

// call resolves the built-in form old(x) and applications of user-defined
// predicates, checking arity and argument sorts.
func (s *scope) call(n *Node) *Term {
	switch n.Name {
	case "len":
		// One spelling for one thing: the length is written with bars.
		fail("there is no len in annotations; write |x| for the length of x")
	case "is":
		// is(err, target): whether errors.Is(err, target) reports true.
		if len(n.Kids) != 2 {
			fail("is takes two errors, as in is(err, ErrEmpty)")
		}
		return Is(s.expect(n.Kids[0], Err), s.expect(n.Kids[1], Err))
	case "has":
		// has(m, k): whether map m has key k.
		if s.env == nil || len(n.Kids) != 2 {
			fail("has takes a map and a key, as in has(m, k), and cannot be used in a predicate definition")
		}
		root, steps, primed := s.path(n.Kids[0])
		if _, bound := s.bound[root.Name]; root.Kind != NIdent || bound {
			fail("has takes a map reached from a variable, as in has(m, k) or has(s.index, k)")
		}
		steps = append(steps, Step{Index: s.term(n.Kids[1]), Has: true})
		t, err := s.env.Path(root.Name, steps, map[bool]When{true: Primed}[primed])
		if err != nil {
			panic(resolveError{err})
		}
		return t
	case "old", "fresh", "within":
		if s.env == nil {
			fail("%s cannot be used in a predicate definition", n.Name)
		}
		if want := map[string]int{"within": 2}[n.Name]; len(n.Kids) != max(want, 1) {
			fail("%s takes %d argument(s), as in %s", n.Name, max(want, 1),
				map[string]string{"old": "old(A)", "fresh": "fresh(result)", "within": "within(s.items', s.items) or within(p, s.items)"}[n.Name])
		}
		var paths []Path
		for _, kid := range n.Kids {
			root, steps, primed := s.path(kid)
			if _, bound := s.bound[root.Name]; root.Kind != NIdent || bound || (primed && n.Name != "within") {
				fail("%s takes a parameter or something reached from one, as in %s(A) or %s(s.items)", n.Name, n.Name, n.Name)
			}
			paths = append(paths, Path{root.Name, steps, map[bool]When{true: Primed}[primed]})
		}
		if n.Name == "old" {
			return s.access(n.Kids[0], Old)
		}
		t, err := s.env.Relation(n.Name, paths)
		if err != nil {
			panic(resolveError{err})
		}
		return t
	}
	if applier, ok := s.env.(Applier); ok && s.env != nil {
		args := make([]*Term, len(n.Kids))
		for i, kid := range n.Kids {
			args[i] = s.term(kid)
		}
		t, known, err := applier.Apply(n.Name, args)
		if err != nil {
			panic(resolveError{err})
		}
		if known {
			return t
		}
	}
	def, ok := s.r.Preds[s.r.Prefix+n.Name]
	if !ok {
		fail("unknown predicate %s", n.Name)
	}
	if len(n.Kids) != len(def.Params) {
		fail("predicate %s takes %d arguments, got %d", n.Name, len(def.Params), len(n.Kids))
	}
	args := make([]*Term, len(n.Kids))
	for i, kid := range n.Kids {
		args[i] = s.term(kid)
		if want := def.Params[i].Sort; args[i].Sort != want {
			fail("argument %d of %s has type %s, want %s", i+1, n.Name, kindOf(args[i]), want)
		}
	}
	return Pred(def.Name, args...)
}

func (s *scope) binary(n *Node) *Term {
	sort := Int
	switch n.Op {
	case "And", "Or", "->", "<->":
		sort = Bool
	}
	a, b := s.expect(n.Kids[0], sort), s.expect(n.Kids[1], sort)
	switch n.Op {
	case "And":
		return And(a, b)
	case "Or":
		return Or(a, b)
	case "->":
		return Implies(a, b)
	case "<->":
		return Iff(a, b)
	case "+":
		return Add(a, b)
	case "-":
		return Sub(a, b)
	case "*":
		return Mul(a, b)
	case "/":
		return Div(a, b)
	}
	return Mod(a, b)
}

// compare resolves one link of a comparison chain. An operand written as a
// slice range, such as A[0:j), stands for every element of the range, so the
// comparison becomes a bounded universal quantifier over the range.
func (s *scope) compare(op string, left, right *Node) *Term {
	var guards []*Term
	var vars []*Term
	operand := func(n *Node) *Term {
		if n.Kind != NRange {
			return s.term(n)
		}
		index := s.r.newBound("k", Int)
		hi := Lt(index, s.expect(n.Kids[2], Int))
		if n.Closed {
			hi = Le(index, hi.Args[1])
		}
		guards = append(guards, Le(s.expect(n.Kids[1], Int), index), hi)
		vars = append(vars, index)
		return Select(s.seq(n.Kids[0]), index)
	}
	a, b := operand(left), operand(right)
	// nil is written the same for an error and for a pointer.
	switch {
	case a == NilErr() && b.Sort == Ref:
		a = RefLit(0)
	case b == NilErr() && a.Sort == Ref:
		b = RefLit(0)
	}
	if a.Sort != b.Sort {
		fail("cannot compare %s (%s) with %s (%s)", plain(left), kindOf(a), plain(right), kindOf(b))
	}
	result := s.relation(op, a, b)
	if len(vars) == 0 {
		return result
	}
	result = Implies(And(guards...), result)
	for i := len(vars) - 1; i >= 0; i-- {
		result = Forall(vars[i], result)
	}
	return result
}

// plain spells an operand of a comparison; of a slice range it names the
// slice, whose elements are what is compared.
func plain(n *Node) string {
	if n.Kind == NRange {
		return "the elements of " + n.Kids[0].String()
	}
	return n.String()
}

// relation builds a comparison between two terms of the same sort. Slices
// compare by length and elements, booleans by equivalence.
func (s *scope) relation(op string, a, b *Term) *Term {
	equality := op == "=" || op == "==" || op == "!="
	var result *Term
	switch {
	case a.Sort.IsSeq() && a.Sort.Elem() == Float:
		// Nothing can be said of a float, so nothing of a sequence of them
		// beyond its length either.
		fail("operator %s cannot be applied to %s values", op, a.Sort)
	case a.Sort.IsSeq() && equality:
		result = SeqEq(a, b, s.r.newBound("k", Int))
	case a.Sort == Err && equality && (a == NilErr() || b == NilErr()):
		result = And(IsNil(a), IsNil(b))
	case a.Sort == Err && equality:
		// Two errors are equal when they are the same error.
		result = Eq(a, b)
	case a.Sort == Err:
		fail("operator %s cannot be applied to errors; compare them with = or !=", op)
	case a.Sort == Bool && equality:
		result = Iff(a, b)
	case a.Sort == Ref && equality && Incomparable(a, b) != "":
		fail("%s", Incomparable(a, b))
	case a.Sort == Ref && equality:
		result = RefEq(a, b)
	case a.Sort == Ref:
		// Of nil and something else, the message names the other.
		named := a
		if kindOf(a) == "nil" {
			named = b
		}
		fail("operator %s cannot be applied to a %s", op, kindOf(named))
	case a.Sort != Int:
		fail("operator %s cannot be applied to %s values", op, a.Sort)
	case equality:
		result = Eq(a, b)
	case op == "<":
		return Lt(a, b)
	case op == "<=":
		return Le(a, b)
	case op == ">":
		return Lt(b, a)
	default:
		return Le(b, a)
	}
	if op == "!=" {
		return Not(result)
	}
	return result
}

func (s *scope) quantifier(n *Node) *Term {
	inner := &scope{r: s.r, env: s.env, bound: map[string]*Term{}}
	for name, t := range s.bound {
		inner.bound[name] = t
	}
	var vars, guards []*Term
	for _, name := range n.Vars {
		v := s.r.newBound(name, Int)
		vars = append(vars, v)
		inner.bound[name] = v
		if len(n.Kids) == 1 {
			continue
		}
		lo, hi := s.expect(n.Kids[0], Int), s.expect(n.Kids[1], Int)
		if n.LoOpen {
			guards = append(guards, Lt(lo, v))
		} else {
			guards = append(guards, Le(lo, v))
		}
		if n.HiOpen {
			guards = append(guards, Lt(v, hi))
		} else {
			guards = append(guards, Le(v, hi))
		}
	}
	result := inner.expect(n.Kids[len(n.Kids)-1], Bool)
	for i := len(vars) - 1; i >= 0; i-- {
		if n.Op == "Forall" {
			result = Forall(vars[i], Implies(And(guards...), result))
			guards = nil
			continue
		}
		result = Exists(vars[i], And(append(guards, result)...))
		guards = nil
	}
	return result
}

// DefineError reports a predicate definition that could not be accepted.
type DefineError struct {
	Decl *PredDecl
	Err  error
}

// Define registers a group of possibly mutually recursive predicates. It
// infers parameter sorts from how each parameter is used, resolves the bodies,
// and rejects recursion through negation, under which a definition taken as
// an axiom could contradict itself.
func (r *Resolver) Define(decls []*PredDecl) []DefineError {
	var errs []DefineError
	byName := map[string]*PredDecl{}
	for _, decl := range decls {
		if _, dup := byName[decl.Name]; dup || slices.Contains([]string{"len", "old", "fresh", "within", "has", "is"}, decl.Name) {
			errs = append(errs, DefineError{decl, fmt.Errorf("predicate %s is already defined", decl.Name)})
			continue
		}
		byName[decl.Name] = decl
	}
	sorts := inferSorts(byName)
	for name, decl := range byName {
		def := &PredDef{Name: r.Prefix + name}
		for i, param := range decl.Params {
			def.Params = append(def.Params, r.newBound(param, sorts[name][i]))
		}
		r.Preds[def.Name] = def
	}
	names := make([]string, 0, len(byName))
	for name := range byName {
		names = append(names, name)
	}
	sort.Strings(names)
	for _, name := range names {
		decl, def := byName[name], r.Preds[r.Prefix+name]
		bound := map[string]*Term{}
		for i, param := range decl.Params {
			bound[param] = def.Params[i]
		}
		body, err := r.resolve(decl.Body, nil, bound, Bool)
		if err != nil {
			errs = append(errs, DefineError{decl, err})
			body = True()
		}
		def.Body = body
	}
	for _, name := range names {
		if r.negativeCycle(r.Prefix + name) {
			err := errors.New("recursive use of predicate " + name + " must not occur under negation, " +
				"on the left of ->, or under <->")
			errs = append(errs, DefineError{byName[name], err})
			r.Preds[r.Prefix+name].Body = True()
		}
	}
	return errs
}

// negativeCycle reports whether the predicate can reach itself through an
// occurrence that is not in positive position. Positive recursion guarantees
// that a least fixed point exists, so a definition taken as an axiom is
// consistent.
func (r *Resolver) negativeCycle(name string) bool {
	reaches := func(from string) bool {
		seen := map[string]bool{}
		var visit func(string) bool
		visit = func(current string) bool {
			if current == name {
				return true
			}
			if seen[current] {
				return false
			}
			seen[current] = true
			found := false
			walkPreds(r.Preds[current].Body, true, func(callee string, _ bool) {
				found = found || visit(callee)
			})
			return found
		}
		return visit(from)
	}
	negative := false
	walkPreds(r.Preds[name].Body, true, func(callee string, positive bool) {
		if !positive && reaches(callee) {
			negative = true
		}
	})
	return negative
}

// walkPreds calls visit for every predicate application in t, telling it
// whether the application occurs in positive position.
func walkPreds(t *Term, positive bool, visit func(name string, positive bool)) {
	switch t.Op {
	case OpPred:
		// The applied predicate may negate a boolean argument, so nothing
		// inside the arguments counts as positive.
		visit(t.Name, positive)
		positive = false
	case OpNot:
		walkPreds(t.Args[0], false, visit)
		return
	case OpImplies:
		walkPreds(t.Args[0], false, visit)
		walkPreds(t.Args[1], positive, visit)
		return
	case OpIff:
		positive = false
	case OpIte:
		walkPreds(t.Args[0], false, visit)
		walkPreds(t.Args[1], positive, visit)
		walkPreds(t.Args[2], positive, visit)
		return
	}
	for _, arg := range t.Args {
		walkPreds(arg, positive, visit)
	}
}

// inferSorts guesses predicate parameter sorts from usage: a parameter that is
// indexed or measured is a slice, one used as a formula is a boolean, and every
// other parameter is an integer. Sorts flow through calls to other predicates
// until nothing changes.
func inferSorts(decls map[string]*PredDecl) map[string][]Sort {
	sorts := map[string][]Sort{}
	for name, decl := range decls {
		sorts[name] = make([]Sort, len(decl.Params))
	}
	for changed := true; changed; {
		changed = false
		for name, decl := range decls {
			index := map[string]int{}
			for i, param := range decl.Params {
				index[param] = i
			}
			set := func(n *Node, sort Sort) {
				i, ok := index[n.Name]
				if n.Kind != NIdent || !ok || sorts[name][i] == sort {
					return
				}
				if current := sorts[name][i]; current != Int && (current != IntSeq || sort != BoolSeq) {
					return
				}
				sorts[name][i] = sort
				changed = true
			}
			var visit func(n *Node, formula bool)
			visit = func(n *Node, formula bool) {
				kidsAreFormulas := false
				switch n.Kind {
				case NIdent:
					if formula {
						set(n, Bool)
					}
				case NIndex:
					set(n.Kids[0], SeqOf(map[bool]Sort{true: Bool, false: Int}[formula]))
				case NRange, NLen:
					set(n.Kids[0], IntSeq)
				case NCall:
					if n.Name == "len" && len(n.Kids) == 1 {
						set(n.Kids[0], IntSeq)
					}
					if n.Name == "is" {
						for _, kid := range n.Kids {
							set(kid, Err)
						}
					}
					for i, kid := range n.Kids {
						if callee, ok := sorts[n.Name]; ok && i < len(callee) && callee[i] != Int {
							set(kid, callee[i])
						}
					}
				case NCompare:
					for i, kid := range n.Kids {
						for _, j := range []int{i - 1, i + 1} {
							if j < 0 || j >= len(n.Kids) || n.Kids[j].Kind != NBool {
								continue
							}
							set(kid, Bool)
							if kid.Kind == NIndex {
								set(kid.Kids[0], BoolSeq)
							}
						}
					}
				case NUnary:
					kidsAreFormulas = n.Op == "~"
				case NBinary:
					switch n.Op {
					case "And", "Or", "->", "<->":
						kidsAreFormulas = true
					}
				case NQuant:
					visit(n.Kids[len(n.Kids)-1], true)
					for _, kid := range n.Kids[:len(n.Kids)-1] {
						visit(kid, false)
					}
					return
				}
				for _, kid := range n.Kids {
					visit(kid, kidsAreFormulas)
				}
			}
			visit(decl.Body, true)
		}
	}
	return sorts
}
