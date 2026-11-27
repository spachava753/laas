package logic

import (
	"errors"
	"fmt"
	"maps"
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
// Index, or, as the last step, of the length, with Has of whether a map has
// the key Index, with State of a state of the value, as in held(m), with
// Cap of the capacity of a slice, with Nil of whether a slice is nil, with
// Addr of the address of what the path leads to, as in &e.list.root, with
// ElemSize of the size in bytes of an element of a slice, as in
// elemsize(s), or with Keys of the sort of the keys of a map, which a
// quantifier over them binds: the Env returns any term of that sort.
type Step struct {
	Field string
	Index *Term
	Len   bool
	Has   bool
	State string
	Cap   bool
	Nil   bool
	Addr  bool
	// ElemSize depends only on the type the path leads to, so it reads
	// nothing.
	ElemSize bool
	Keys     bool
	// Assert reads what an error holds as a value of the type, as in
	// err.(*ParseError), and Holds, as the last step, whether it holds one,
	// as in holds(err, *ParseError).
	Assert *TypeName
	Holds  *TypeName
	// As, as the last step, is whether errors.As finds a value of the
	// type in the error, as in as(err, *ParseError).
	As *TypeName
	// Deref reads what a pointer to a number, a boolean, or a string
	// points to, as in *p.
	Deref bool
}

// NotSlice is what an Env returns for a path with a last step Nil that does
// not lead to a slice: the comparison with nil is then resolved as for any
// other value.
var NotSlice = errors.New("not a slice")

// NoState is the error an Env returns for a path whose value has no state
// of the name asked for. The name may then be a predicate.
type NoState struct{ Msg string }

func (e *NoState) Error() string { return e.Msg }

// Env supplies the meaning of program names that occur in an annotation.
type Env interface {
	// Path returns the value reached from a program variable by selecting
	// fields and elements.
	Path(root string, steps []Step, when When) (*Term, error)
	// Relation returns a formula about the identity of the pointers or
	// slices that paths lead to: "fresh" states that what one path refers to
	// was created during the call, "within" that the memory the first of
	// two paths refers to lies inside that of the second, and "apart" that
	// two slices share no memory, and "valid" that the invariants of the
	// struct a path leads to hold.
	Relation(name string, paths []Path) (*Term, error)
	// Qualified returns the value of a variable named by the path of its
	// package in quotes, as in "io/fs".ErrNotExist, followed by steps.
	Qualified(path, name string, steps []Step, when When) (*Term, error)
}

// Typer is an Env that knows the types of the program (F33): what a name
// in a formula that is a type means, and what errors hold.
type Typer interface {
	// IsType reports whether a name is a type where the formula stands,
	// and Convertible whether it is one whose values a formula can convert
	// to, as in T(v): an integer, string, or boolean type.
	IsType(t TypeName) bool
	Convertible(t TypeName) bool
	// Convert returns the value of the conversion T(v) of an integer, a
	// string, or a boolean, for v the term arg and, when arg is a path, its
	// Go type argType, or a literal; it refuses one that may not fit T, and
	// one whose value Go converts otherwise.
	Convert(t TypeName, arg *Term, argType any, literal bool) (*Term, error)
	// PathType returns the Go type of what a path leads to, or nil.
	PathType(root string, steps []Step, when When) any
	// ErrorType returns the type of what a path leads to when it is a
	// concrete type that implements error, which Go converts to error
	// beside an error, with Resolved set; ok is false otherwise.
	ErrorType(root string, steps []Step, when When) (t TypeName, ok bool)
	// TypedEquals returns the formula err = error(T(v)): Go's == of err and
	// the error that holds v.
	TypedEquals(t TypeName, err, v *Term) (*Term, error)
	// TypedError returns the error that holds v, an Err term, for a type
	// that has one.
	TypedError(t TypeName, v *Term) (*Term, error)
}

// Applier is an Env that gives a meaning to some applications, as f(i) for
// a function that a trusted contract names. Apply reports whether it knows
// the name; a name it does not know is a predicate.
type Applier interface {
	Apply(name string, args []*Term) (t *Term, known bool, err error)
	// Applies reports whether Apply knows the name, without arguments.
	Applies(name string) bool
}

// Gatherer is an Env whose reads under a quantifier make facts that may
// mention its variables and hold in every state, such as what a layer of
// memory keeps at the cell a bound variable names. A quantifier takes the
// ones that mention its variables beside its guards, as premises of a
// Forall and conjuncts of an Exists, which changes neither, since they are
// true, and hands Keep the same facts quantified on their own over its
// variables under its guards, so that a formula that is assumed has them
// as facts and not only as premises.
type Gatherer interface {
	OpenBound(vars []*Term)
	CloseBound() []*Term
	Keep(fact *Term)
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

// Reserved lists the names of the forms of the language that look like
// applications, which no predicate, state, or other name may take.
var Reserved = []string{"len", "cap", "elemsize", "old", "fresh", "within", "apart", "has", "is", "valid", "behind", "holds", "as"}

// Resolver type-checks parsed annotations and turns them into terms.
type Resolver struct {
	// Preds holds the defined predicates by the name their applications
	// carry in terms, which is Prefix followed by the name in annotations.
	Preds map[string]*PredDef
	// Prefix keeps the predicates of different packages apart when their
	// terms meet in one proof.
	Prefix string
	// Mark, when set, starts the name of every bound variable the
	// resolver makes, so that the names of a resolver kept apart from
	// another never meet that one's.
	Mark  string
	fresh int
}

// NewResolver returns a resolver with no predicates defined.
func NewResolver() *Resolver { return &Resolver{Preds: map[string]*PredDef{}} }

type scope struct {
	r     *Resolver
	env   Env
	bound map[string]*Term
	// compared holds, for each variable bound to the string keys of a map,
	// the strings that the body of its quantifier compares it with; see
	// quantifier.
	compared map[string]*comparedKey
	// negated is the comparison that a ~ is written directly on, whose =
	// between two interface values is refused as != is (O4 of F34).
	negated *Node
}

// comparedKey is what the body of a quantifier over string keys compares
// its key with: strings that mention no variable but those in scope where
// the quantifier binds its own.
type comparedKey struct {
	terms []*Term
	scope map[string]bool
}

func (r *Resolver) newBound(name string, sort Sort) *Term {
	r.fresh++
	return Bound(fmt.Sprintf("%s%s#%d", r.Mark, name, r.fresh), sort)
}

// Formula resolves a parsed clause that must be a formula.
func (r *Resolver) Formula(n *Node, env Env) (*Term, error) {
	return r.resolve(n, env, nil, Bool)
}

// IntTerm resolves a parsed clause that must be an integer expression.
func (r *Resolver) IntTerm(n *Node, env Env) (*Term, error) {
	return r.resolve(n, env, nil, Int)
}

// Value resolves a parsed expression of any sort.
func (r *Resolver) Value(n *Node, env Env) (t *Term, err error) {
	defer func() {
		if recovered := recover(); recovered != nil {
			resolveErr, ok := recovered.(resolveError)
			if !ok {
				panic(recovered)
			}
			t, err = nil, resolveErr.err
		}
	}()
	s := &scope{r: r, env: env}
	return s.term(n), nil
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
	panic(resolveError{&FormError{fmt.Sprintf(format, args...)}})
}

// FormError is an error of a formula that the resolver finds whatever the
// types of what it names: a name it does not know, a form with the wrong
// number of arguments, a word used as a name.
type FormError struct{ Msg string }

func (e *FormError) Error() string { return e.Msg }

// SortError is an error of a formula that the resolver finds from the
// sorts of the values it reads, as an order of strings or a field of an
// integer; at another instantiation of a generic function the same formula
// may have a meaning.
type SortError struct{ Msg string }

func (e *SortError) Error() string { return e.Msg }

func failSort(format string, args ...any) {
	panic(resolveError{&SortError{fmt.Sprintf(format, args...)}})
}

// IncomparableError is a SortError for values that a formula cannot
// compare by their nature, floats and pointers to values of size zero,
// which an entry of a generic function may meet at some type arguments.
type IncomparableError struct{ SortError }

func (e *IncomparableError) Unwrap() error { return &e.SortError }

func failIncomparable(format string, args ...any) {
	panic(resolveError{&IncomparableError{SortError{fmt.Sprintf(format, args...)}}})
}

// kindOf names what a term of a formula stands for, as a message should
// call it. A reference is a pointer, a function value, an interface value,
// or, when it is none of these, a map: those are the only references a path
// gives.
func kindOf(t *Term) string {
	switch {
	case t.Op == OpIntLit && t.Sort == Ref && t.Val == 0:
		return "nil"
	case t.Op == OpFuncVal:
		return "function value"
	case t.Op == OpIfaceVal:
		return "interface value"
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
		failSort("expected %s but %s has type %s", describe(want), n, kindOf(t))
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
	case NIdent, NField, NIndex, NAssert, NDeref:
		return s.access(n, Now)
	case NConvert:
		return s.conversion(*n.Type, n.Kids[0])
	case NCall:
		return s.call(n)
	case NLen:
		return s.length(n.Kids[0])
	case NKeysLeft:
		panic(resolveError{fmt.Errorf("%s is a measure of a search and stands only as the whole of a Variant, as in // @Variant |g \\ seen|", n.String())})
	case NUnary:
		if n.Op == "-" {
			return Neg(s.expect(n.Kids[0], Int))
		}
		if n.Kids[0].Kind == NCompare {
			s.negated = n.Kids[0]
		}
		return Not(s.expect(n.Kids[0], Bool))
	case NBinary:
		return s.binary(n)
	case NCompare:
		negated := s.negated == n
		s.negated = nil
		var parts []*Term
		for i, op := range n.Ops {
			parts = append(parts, s.compare(op, n.Kids[i], n.Kids[i+1], negated && len(n.Ops) == 1))
		}
		return And(parts...)
	case NQuant:
		return s.quantifier(n)
	case NAddr:
		return s.address(n)
	}
	fail("a slice range such as A[lo:hi) can only be used as an operand of a comparison")
	return nil
}

func (s *scope) seq(n *Node) *Term {
	t := s.term(n)
	if !t.Sort.IsSeq() {
		failSort("%s has type %s, not a slice", n, kindOf(t))
	}
	return t
}

// length resolves |x|. The length of something reached from a program
// variable is asked of the environment, which also knows the length of a
// slice whose elements have no value in the logic.
func (s *scope) length(n *Node) *Term {
	root, steps, when, ok := s.pathOf(n)
	if !ok {
		return Len(s.seq(n))
	}
	t, err := s.env.Path(root, append(steps, Step{Len: true}), when)
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
	case NAssert:
		root, steps, primed = s.path(n.Kids[0])
		return root, append(steps, Step{Assert: n.Type}), primed
	case NDeref:
		root, steps, primed = s.path(n.Kids[0])
		return root, append(steps, Step{Deref: true}), primed
	}
	return n, nil, n.Kind == NIdent && n.Primed
}

// address resolves &x.f, the address of a struct reached from a program
// variable through a pointer or an element of a slice. The environment
// decides what may be addressed.
func (s *scope) address(n *Node) *Term {
	kid := n.Kids[0]
	root, steps, primed := s.path(kid)
	_, bound := s.bound[root.Name]
	switch {
	case s.env == nil:
		fail("& cannot be used in a predicate definition")
	case (kid.Kind != NField && kid.Kind != NIndex) || root.Kind != NIdent || bound:
		fail("& takes a field or an element reached from a variable through a pointer or a slice, as in &e.list.root or &s[i]")
	}
	t, err := s.env.Path(root.Name, append(steps, Step{Addr: true}), map[bool]When{true: Primed}[primed])
	if err != nil {
		panic(resolveError{err})
	}
	return t
}

// pathOf splits the argument of cap, or an operand compared with nil, into
// the variable it starts from, its steps, and the state it is read in; old
// around the whole path reads it on entry. It reports false for anything
// that is not such a path.
func (s *scope) pathOf(n *Node) (root string, steps []Step, when When, ok bool) {
	if n.Kind == NCall && n.Name == "old" && len(n.Kids) == 1 {
		n, when = n.Kids[0], Old
	}
	if n.Kind != NIdent && n.Kind != NField && n.Kind != NIndex && n.Kind != NAssert && n.Kind != NDeref {
		return "", nil, Now, false
	}
	start, steps, primed := s.path(n)
	if _, bound := s.bound[start.Name]; start.Kind != NIdent || bound || s.env == nil {
		return "", nil, Now, false
	}
	if primed && when == Old {
		fail("old(%s) is the value on entry and cannot be primed", start.Name)
	}
	if primed {
		when = Primed
	}
	return start.Name, steps, when, true
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
			if step.Assert != nil {
				fail("%s.(%s) takes an error reached from a variable", root, step.Assert)
			}
			if step.Deref {
				fail("* takes a pointer reached from a variable, as in *p or *c.limit")
			}
			if step.Field != "" {
				fail("%s has no field %s", root, step.Field)
			}
			if !base.Sort.IsSeq() {
				failSort("%s has type %s and cannot be indexed", root, kindOf(base))
			}
			if step.Index.Sort != Int {
				failSort("%s is indexed by a %s, not by an integer", root, step.Index.Sort)
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
		return Is(s.expect(n.Kids[0], Err), s.errorOperand(n.Kids[1]))
	case "holds":
		// holds(x, T): whether the error x holds a value of type T.
		if s.env == nil || n.Type == nil || len(n.Kids) != 1 {
			fail("holds takes an error and a type, as in holds(err, *ParseError), and cannot be used in a predicate definition")
		}
		root, steps, when, ok := s.pathOf(n.Kids[0])
		if !ok {
			fail("holds takes an error reached from a variable, as in holds(err, *ParseError) or holds(old(err), Error)")
		}
		t, err := s.env.Path(root, append(steps, Step{Holds: n.Type}), when)
		if err != nil {
			panic(resolveError{err})
		}
		return t
	case "as":
		// as(err, T): whether errors.As finds a value of type T in err.
		if s.env == nil || n.Type == nil || len(n.Kids) != 1 {
			fail("as takes an error and a type, as in as(err, *ParseError), and cannot be used in a predicate definition")
		}
		root, steps, when, ok := s.pathOf(n.Kids[0])
		if !ok {
			fail("as takes an error reached from a variable, as in as(err, *ParseError) or as(old(err), Error)")
		}
		t, err := s.env.Path(root, append(steps, Step{As: n.Type}), when)
		if err != nil {
			panic(resolveError{err})
		}
		return t
	case "has":
		// has(m, k): whether map m has key k.
		if s.env == nil || len(n.Kids) != 2 {
			fail("has takes a map and a key, as in has(m, k), and cannot be used in a predicate definition")
		}
		root, steps, when, ok := s.pathOf(n.Kids[0])
		if !ok {
			fail("has takes a map reached from a variable, as in has(m, k), has(s.index, k), or has(old(m), k)")
		}
		steps = append(steps, Step{Index: s.term(n.Kids[1]), Has: true})
		t, err := s.env.Path(root, steps, when)
		if err != nil {
			panic(resolveError{err})
		}
		return t
	case "cap":
		// cap(A): the capacity of a slice.
		if s.env == nil {
			fail("cap cannot be used in a predicate definition")
		}
		if len(n.Kids) != 1 {
			fail("cap takes one slice, as in cap(A)")
		}
		root, steps, when, ok := s.pathOf(n.Kids[0])
		if !ok {
			fail("cap takes a slice reached from a variable, as in cap(A), cap(s.items), or cap(old(A))")
		}
		t, err := s.env.Path(root, append(steps, Step{Cap: true}), when)
		if err != nil {
			panic(resolveError{err})
		}
		return t
	case "elemsize":
		// elemsize(A): the number of bytes an element of the slice A takes
		// on the target, a constant of its type.
		if s.env == nil {
			fail("elemsize cannot be used in a predicate definition")
		}
		if len(n.Kids) != 1 {
			fail("elemsize takes one slice, as in elemsize(A)")
		}
		root, steps, when, ok := s.pathOf(n.Kids[0])
		if !ok {
			fail("elemsize takes a slice reached from a variable, as in elemsize(A) or elemsize(s.items)")
		}
		t, err := s.env.Path(root, append(steps, Step{ElemSize: true}), when)
		if err != nil {
			panic(resolveError{err})
		}
		return t
	case "old", "fresh", "within", "apart", "valid":
		if s.env == nil {
			fail("%s cannot be used in a predicate definition", n.Name)
		}
		if n.Name == "fresh" && len(n.Kids) == 0 {
			fail("fresh takes one argument or more, as in fresh(result) or fresh(result, w)")
		}
		if want := map[string]int{"within": 2, "apart": 2}[n.Name]; n.Name != "fresh" && len(n.Kids) != max(want, 1) {
			fail("%s takes %d argument(s), as in %s", n.Name, max(want, 1),
				map[string]string{"old": "old(A)", "fresh": "fresh(result)", "within": "within(s.items', s.items) or within(p, s.items)",
					"apart": "apart(A, B)", "valid": "valid(ts)"}[n.Name])
		}
		var paths []Path
		for _, kid := range n.Kids {
			// valid(old(x)) is what a boundary assumed of x as it was on
			// entry, inside a body.
			if n.Name == "valid" && kid.Kind == NCall && kid.Name == "old" && len(kid.Kids) == 1 {
				root, steps, primed := s.path(kid.Kids[0])
				if _, bound := s.bound[root.Name]; root.Kind != NIdent || bound || primed {
					fail("valid takes a struct or a pointer to one, a parameter or something reached from one, as in valid(ts), valid(ts.store), or valid(old(ts))")
				}
				paths = append(paths, Path{root.Name, steps, Old})
				continue
			}
			root, steps, primed := s.path(kid)
			if _, bound := s.bound[root.Name]; root.Kind != NIdent || bound || (primed && n.Name != "within" && n.Name != "apart" && n.Name != "valid") {
				if n.Name == "valid" {
					fail("valid takes a struct or a pointer to one, a parameter or something reached from one, as in valid(ts), valid(ts.store), or valid(old(ts))")
				}
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
	_, predicate := s.r.Preds[s.r.Prefix+n.Name]
	if typer, ok := s.env.(Typer); ok && s.env != nil && typer.IsType(TypeName{Name: n.Name}) && (!predicate || typer.Convertible(TypeName{Name: n.Name})) {
		// A type that a formula cannot convert to leaves its name to a
		// predicate of that name.
		if predicate {
			fail("%s is both a type and a predicate here; rename the predicate", n.Name)
		}
		if len(n.Kids) != 1 {
			fail("the conversion %s takes one value, as in %s(c)", n.Name, n.Name)
		}
		return s.conversion(TypeName{Name: n.Name}, n.Kids[0])
	}
	state, isState, missing := s.state(n)
	applier, _ := s.env.(Applier)
	applies := s.env != nil && applier != nil && applier.Applies(n.Name)
	if isState && applies {
		fail("%s is both a function that the contract applies and a state of %s; rename the parameter", n.Name, plain(n.Kids[0]))
	}
	if isState {
		return state
	}
	if _, predicate := s.r.Preds[s.r.Prefix+n.Name]; missing != "" && !predicate && !applies {
		fail("%s", missing)
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
			failSort("argument %d of %s has type %s, want %s", i+1, n.Name, kindOf(args[i]), want)
		}
	}
	return Pred(def.Name, args...)
}

// state resolves name(x) as a state of the value or pointer x, as in
// held(m) or held(a.mu'), and reports whether it is one. A name that is a
// state of x and also a predicate is an error: the formula would mean one of
// two things. When x has no such state, missing says why, for the case that
// the name is no predicate either; it is empty when nothing has a state of
// that name.
func (s *scope) state(n *Node) (t *Term, ok bool, missing string) {
	if s.env == nil || len(n.Kids) != 1 {
		return nil, false, ""
	}
	kid, when := n.Kids[0], Now
	if kid.Kind == NCall && kid.Name == "old" && len(kid.Kids) == 1 {
		kid, when = kid.Kids[0], Old
	}
	root, steps, primed := s.path(kid)
	if _, bound := s.bound[root.Name]; root.Kind != NIdent || bound {
		return nil, false, ""
	}
	if primed && when == Old {
		fail("old(%s) is the value on entry and cannot be primed", root.Name)
	}
	if primed {
		when = Primed
	}
	steps = append(steps, Step{State: n.Name})
	t, err := s.env.Path(root.Name, steps, when)
	var none *NoState
	_, predicate := s.r.Preds[s.r.Prefix+n.Name]
	switch {
	case errors.As(err, &none):
		return nil, false, none.Msg
	case err != nil:
		panic(resolveError{err})
	case predicate:
		fail("%s is both a predicate and a state of %s; rename the predicate", n.Name, plain(n.Kids[0]))
	}
	return t, true, ""
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
func (s *scope) compare(op string, left, right *Node, negated bool) *Term {
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
	if t := s.nilSlice(op, left, right); t != nil {
		return t
	}
	a, b := operand(left), operand(right)
	// nil is written the same for an error and for a pointer. Only nil as
	// written is a nil pointer: an error that is nil, as a result an
	// outcome chose, beside a pointer is compared as Go compares them,
	// converting the pointer to error (F33).
	switch {
	case a == NilErr() && b.Sort == Ref && left.Kind == NNil:
		a = RefLit(0)
	case b == NilErr() && a.Sort == Ref && right.Kind == NNil:
		b = RefLit(0)
	}
	if a.Sort != b.Sort && len(vars) == 0 {
		// An error beside a value of a concrete type that implements
		// error, which Go converts.
		if t := s.typedCompare(op, a, b, left, right); t != nil {
			return t
		}
	}
	if a.Sort != b.Sort {
		failSort("cannot compare %s (%s) with %s (%s)", plain(left), kindOf(a), plain(right), kindOf(b))
	}
	if a.Op == OpIfaceVal && b.Op == OpIfaceVal && (op == "!=" || op == "=" && negated) {
		// That two interface values are not the same value is not what
		// Go's != says of them, and nothing in Go can observe it (O4 of
		// F34).
		written := plain(left) + " != " + plain(right)
		if op == "=" {
			written = "~(" + plain(left) + " = " + plain(right) + ")"
		}
		failSort("%s between two interface values that are not nil is not supported: = says that they are the same value, copied from one another, "+
			"and not Go's ==, so its negation says nothing that code can observe; to say what Go's == says, state what they hold, "+
			"as in holds(%s, T) And holds(%s, T) And %s.(T) != %s.(T)", written, plain(left), plain(right), plain(left), plain(right))
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

// typedType returns the type of a node that is a value of a concrete type
// that implements error, which Go converts to error beside an error: a
// conversion T(v) to such a type, or a path to such a value, such as a
// constant ErrSyntax of a type Error.
func (s *scope) typedType(n *Node) (TypeName, bool) {
	typer, isTyper := s.env.(Typer)
	if !isTyper || s.env == nil {
		return TypeName{}, false
	}
	switch {
	case n.Kind == NConvert:
		return *n.Type, true
	case n.Kind == NCall && len(n.Kids) == 1 && typer.IsType(TypeName{Name: n.Name}):
		return TypeName{Name: n.Name}, true
	}
	root, steps, when, isPath := s.pathOf(n)
	if !isPath {
		return TypeName{}, false
	}
	return typer.ErrorType(root, steps, when)
}

// typedCompare resolves err = v and err != v for an error err and a value
// v of a concrete type that Go converts to error, as Go's == of err and the
// error that holds v. It returns nil when neither side is such a value.
func (s *scope) typedCompare(op string, a, b *Term, left, right *Node) *Term {
	e, v, other := a, b, right
	if b.Sort == Err {
		e, v, other = b, a, left
	}
	if e.Sort != Err {
		return nil
	}
	t, ok := s.typedType(other)
	if !ok {
		return nil
	}
	if op != "=" && op != "!=" {
		failSort("operator %s cannot be applied to errors; compare them with = or !=", op)
	}
	eq, err := s.env.(Typer).TypedEquals(t, e, v)
	if err != nil {
		panic(resolveError{err})
	}
	if op == "!=" {
		return Not(eq)
	}
	return eq
}

// errorOperand resolves an operand that must be an error, where a value of
// a concrete type that implements error is converted, as the target of
// is(err, ErrSyntax).
func (s *scope) errorOperand(n *Node) *Term {
	v := s.term(n)
	if v.Sort == Err {
		return v
	}
	if t, ok := s.typedType(n); ok {
		e, err := s.env.(Typer).TypedError(t, v)
		if err != nil {
			panic(resolveError{err})
		}
		return e
	}
	failSort("expected an error but %s has type %s", n, kindOf(v))
	return nil
}

// conversion resolves T(v) of an integer, a string, or a boolean v.
func (s *scope) conversion(t TypeName, arg *Node) *Term {
	typer, ok := s.env.(Typer)
	if !ok || s.env == nil {
		fail("a conversion %s(...) cannot be used here", t)
	}
	v := s.term(arg)
	var argType any
	if root, steps, when, isPath := s.pathOf(arg); isPath {
		argType = typer.PathType(root, steps, when)
	}
	converted, err := typer.Convert(t, v, argType, arg.Kind == NStr || arg.Kind == NInt)
	if err != nil {
		panic(resolveError{err})
	}
	return converted
}

// nilSlice resolves A = nil and A != nil for a slice A, which has no value
// of its own in a formula: whether it is nil is asked of the environment.
// It returns nil when neither side is nil, or the other side is no slice.
func (s *scope) nilSlice(op string, left, right *Node) *Term {
	other := left
	switch {
	case left.Kind == NNil:
		other = right
	case right.Kind != NNil:
		return nil
	}
	root, steps, when, ok := s.pathOf(other)
	if !ok {
		return nil
	}
	t, err := s.env.Path(root, append(steps, Step{Nil: true}), when)
	switch {
	case errors.Is(err, NotSlice):
		return nil
	case err != nil:
		panic(resolveError{err})
	case op != "=" && op != "!=":
		failSort("operator %s cannot be applied to a slice and nil; a slice is compared with nil by = or !=", op)
	case op == "!=":
		return Not(t)
	}
	return t
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
	equality := op == "=" || op == "!="
	var result *Term
	switch {
	case a.Sort.IsSeq() && a.Sort.Elem() == Float:
		// Nothing can be said of a float, so nothing of a sequence of them
		// beyond its length either.
		failSort("operator %s cannot be applied to %s values", op, a.Sort)
	case a.Sort.IsSeq() && equality:
		result = SeqEq(a, b, s.r.newBound("k", Int))
		s.noteCompared(a, b)
		s.noteCompared(b, a)
	case a.Sort == Err && equality && (a == NilErr() || b == NilErr()):
		result = And(IsNil(a), IsNil(b))
	case a.Sort == Err && equality:
		// Two errors are equal when they are the same error.
		result = Eq(a, b)
	case a.Sort == Err:
		failSort("operator %s cannot be applied to errors; compare them with = or !=", op)
	case a.Sort == Bool && equality:
		result = Iff(a, b)
	case a.Sort == Ref && equality && Incomparable(a, b) != "":
		if a.Op == OpPair && b.Op == OpPair {
			// Two pointers, one of them to a value of size zero.
			failIncomparable("%s", Incomparable(a, b))
		}
		failSort("%s", Incomparable(a, b))
	case a.Sort == Ref && equality:
		result = RefEq(a, b)
	case a.Sort == Ref:
		// Of nil and something else, the message names the other.
		named := a
		if kindOf(a) == "nil" {
			named = b
		}
		kind := kindOf(named)
		article := "a"
		if kind == "interface value" {
			article = "an"
		}
		failSort("operator %s cannot be applied to %s %s", op, article, kind)
	case a.Sort == Float:
		failIncomparable("operator %s cannot be applied to float values; a formula can say nothing of a float", op)
	case a.Sort.IsSeq():
		failSort("operator %s cannot be applied to string or slice values; a formula has no order of them", op)
	case a.Sort != Int:
		failSort("operator %s cannot be applied to %s values", op, a.Sort)
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

// quantifier resolves Forall and Exists. Each variable ranges over the
// integers, an interval, whose ends give guards, or the keys of a map,
// whose guard is that the map has the variable as a key and whose sort is
// that of the keys. A Forall implies its body from the guards and an Exists
// conjoins them, at the innermost variable. Over Z, a name Z that means
// something here is refused, since it would give Z two meanings.
func (s *scope) quantifier(n *Node) *Term {
	inner := &scope{r: s.r, env: s.env, bound: map[string]*Term{}, compared: maps.Clone(s.compared)}
	if inner.compared == nil {
		inner.compared = map[string]*comparedKey{}
	}
	for name, t := range s.bound {
		inner.bound[name] = t
	}
	var vars, guards []*Term
	if len(n.Kids) == 1 && s.env != nil {
		// Z is the integers, which a variable of that name would make a
		// second meaning of.
		if _, err := s.env.Path("Z", nil, Now); err == nil {
			fail("Z names something here, so Forall %s in Z could mean the integers or what Z names; rename it, or write an interval", n.Vars[0])
		}
	}
	var keyed []*Term
	for _, name := range n.Vars {
		if name == "Z" {
			fail("Z is the integers in the domain of a quantifier, so it cannot also name a bound variable; choose another name")
		}
		if len(n.Kids) == 2 {
			// The keys of a map, which have the sort of its keys.
			v, guard := s.keyOf(n.Kids[0], name)
			vars, guards = append(vars, v), append(guards, guard)
			inner.bound[name] = v
			if v.Sort.IsSeq() {
				keyed = append(keyed, v)
				inner.compared[v.Name] = &comparedKey{}
			}
			continue
		}
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
	// A compared string may mention the variables bound around the
	// quantifier and its own, which are in scope where its guards stand.
	for _, v := range keyed {
		known := map[string]bool{}
		for _, t := range inner.bound {
			known[t.Name] = true
		}
		inner.compared[v.Name].scope = known
	}
	gatherer, gathers := s.env.(Gatherer)
	if gathers {
		gatherer.OpenBound(vars)
	}
	closed := false
	defer func() {
		if gathers && !closed {
			gatherer.CloseBound()
		}
	}()
	result := inner.expect(n.Kids[len(n.Kids)-1], Bool)
	if gathers {
		closed = true
		if facts := gatherer.CloseBound(); len(facts) > 0 {
			side := Implies(And(guards...), And(facts...))
			for i := len(vars) - 1; i >= 0; i-- {
				side = Forall(vars[i], side)
			}
			gatherer.Keep(side)
			guards = append(guards, facts...)
		}
	}
	// The key of a string is the same as that of another exactly when the
	// two strings are equal, which the solver states only of strings keyed
	// outside quantifiers. For each string the body compares a bound key
	// with, that is stated with the guard, so that a key the body excepts,
	// as in k = node, is known to be the one a write to Key(node) reached.
	for _, v := range keyed {
		for _, t := range inner.compared[v.Name].terms {
			guards = append(guards, Iff(Eq(Key(v), Key(t)), SeqEq(v, t, s.r.newBound("k", Int))))
		}
	}
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

// noteCompared records that the body of a quantifier over string keys
// compares its bound key with a string that does not mention it.
func (s *scope) noteCompared(key, other *Term) {
	if key.Op != OpBound || s.compared[key.Name] == nil {
		return
	}
	entry := s.compared[key.Name]
	if !boundWithin(other, entry.scope) || mentionsBound(other, key.Name) {
		return
	}
	entry.terms = append(entry.terms, other)
}

// boundWithin reports whether every bound variable a term holds is among
// the names given.
func boundWithin(t *Term, names map[string]bool) bool {
	if t.Op == OpBound && !names[t.Name] {
		return false
	}
	return !slices.ContainsFunc(t.Args, func(arg *Term) bool { return !boundWithin(arg, names) })
}

// mentionsBound reports whether a term holds the bound variable of a name.
func mentionsBound(t *Term, name string) bool {
	if t.Op == OpBound && t.Name == name {
		return true
	}
	return slices.ContainsFunc(t.Args, func(arg *Term) bool { return mentionsBound(arg, name) })
}

// keyOf binds a variable to the keys of a map named by a path, and returns
// it with the formula that the map has it. A quantifier over the keys says
// its body of every key the map has, or that some key it has meets it.
func (s *scope) keyOf(domain *Node, name string) (*Term, *Term) {
	if s.env == nil {
		fail("a quantifier over the keys of a map cannot be used in a predicate definition")
	}
	root, steps, when, ok := s.pathOf(domain)
	if !ok {
		fail("a quantifier ranges over Z, an interval, or the keys of a map reached from a variable, as in Forall k in m; %s is none of these", domain)
	}
	sorted, err := s.env.Path(root, append(slices.Clip(steps), Step{Keys: true}), when)
	if err != nil {
		panic(resolveError{err})
	}
	v := s.r.newBound(name, sorted.Sort)
	has, err := s.env.Path(root, append(slices.Clip(steps), Step{Index: v, Has: true}), when)
	if err != nil {
		panic(resolveError{err})
	}
	return v, has
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
		if _, dup := byName[decl.Name]; dup || slices.Contains(Reserved, decl.Name) {
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
