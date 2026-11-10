package logic

import (
	"errors"
	"fmt"
	"sort"
)

// Env supplies the meaning of program names that occur in an annotation.
type Env interface {
	// Var returns the value of a program variable; primed asks for the
	// post-state value written x' in the annotation.
	Var(name string, primed bool) (*Term, error)
	// Old returns the value a parameter had on function entry.
	Old(name string) (*Term, error)
}

// PredDef is a resolved user-defined predicate.
type PredDef struct {
	Name   string
	Params []*Term // bound variables standing for the parameters
	Body   *Term
}

// Resolver type-checks parsed annotations and turns them into terms.
type Resolver struct {
	Preds map[string]*PredDef
	fresh int
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

func (s *scope) expect(n *Node, want Sort) *Term {
	t := s.term(n)
	if t.Sort != want {
		fail("expected %s but %s has type %s", describe(want), t, t.Sort)
	}
	return t
}

func describe(sort Sort) string {
	switch sort {
	case Bool:
		return "a formula"
	case Int:
		return "an integer"
	}
	return "a slice"
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
	case NIdent:
		return s.name(n)
	case NCall:
		return s.call(n)
	case NIndex:
		return Select(s.seq(n.Kids[0]), s.expect(n.Kids[1], Int))
	case NLen:
		return Len(s.seq(n.Kids[0]))
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
		fail("%s has type %s, not a slice", t, t.Sort)
	}
	return t
}

func (s *scope) name(n *Node) *Term {
	if t, ok := s.bound[n.Name]; ok {
		if n.Primed {
			fail("%s' is not a program variable and cannot be primed", n.Name)
		}
		return t
	}
	if s.env == nil {
		fail("unknown name %s in predicate definition; predicates may only mention their parameters", n.Name)
	}
	t, err := s.env.Var(n.Name, n.Primed)
	if err != nil {
		panic(resolveError{err})
	}
	return t
}

// call resolves the built-in forms len(A) and old(x) and applications of
// user-defined predicates, checking arity and argument sorts.
func (s *scope) call(n *Node) *Term {
	switch n.Name {
	case "len":
		if len(n.Kids) != 1 {
			fail("len takes exactly one argument")
		}
		return Len(s.seq(n.Kids[0]))
	case "old":
		if len(n.Kids) != 1 || n.Kids[0].Kind != NIdent || n.Kids[0].Primed {
			fail("old takes exactly one parameter name, as in old(A)")
		}
		if s.env == nil {
			fail("old cannot be used in a predicate definition")
		}
		t, err := s.env.Old(n.Kids[0].Name)
		if err != nil {
			panic(resolveError{err})
		}
		return t
	}
	def, ok := s.r.Preds[n.Name]
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
			fail("argument %d of %s has type %s, want %s", i+1, n.Name, args[i].Sort, want)
		}
	}
	return Pred(n.Name, args...)
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
	if a.Sort != b.Sort {
		fail("cannot compare %s (%s) with %s (%s)", a, a.Sort, b, b.Sort)
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

// relation builds a comparison between two terms of the same sort. Slices
// compare by length and elements, booleans by equivalence.
func (s *scope) relation(op string, a, b *Term) *Term {
	equality := op == "=" || op == "==" || op == "!="
	var result *Term
	switch {
	case a.Sort.IsSeq() && equality:
		result = SeqEq(a, b, s.r.newBound("k", Int))
	case a.Sort == Err && equality && (a == NilErr() || b == NilErr()):
		// Whether an error is nil is all that is known about it.
		result = And(IsNil(a), IsNil(b))
	case a.Sort == Err:
		fail("an error can only be compared with nil")
	case a.Sort == Bool && equality:
		result = Iff(a, b)
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
// and rejects recursion through negation, which would make unfolding a
// predicate unsound.
func (r *Resolver) Define(decls []*PredDecl) []DefineError {
	var errs []DefineError
	byName := map[string]*PredDecl{}
	for _, decl := range decls {
		if _, dup := byName[decl.Name]; dup || decl.Name == "len" || decl.Name == "old" {
			errs = append(errs, DefineError{decl, fmt.Errorf("predicate %s is already defined", decl.Name)})
			continue
		}
		byName[decl.Name] = decl
	}
	sorts := inferSorts(byName)
	for name, decl := range byName {
		def := &PredDef{Name: name}
		for i, param := range decl.Params {
			def.Params = append(def.Params, r.newBound(param, sorts[name][i]))
		}
		r.Preds[name] = def
	}
	names := make([]string, 0, len(byName))
	for name := range byName {
		names = append(names, name)
	}
	sort.Strings(names)
	for _, name := range names {
		decl, def := byName[name], r.Preds[name]
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
		if r.negativeCycle(name) {
			err := errors.New("recursive use of predicate " + name + " must not occur under negation, " +
				"on the left of ->, or under <->")
			errs = append(errs, DefineError{byName[name], err})
			r.Preds[name].Body = True()
		}
	}
	return errs
}

// negativeCycle reports whether the predicate can reach itself through an
// occurrence that is not in positive position. Positive recursion guarantees
// that a least fixed point exists, so unfolding a definition is consistent.
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
