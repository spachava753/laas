package solver

import (
	"fmt"
	"math"
	"math/big"
	"slices"
	"strconv"
	"strings"

	"github.com/spachava753/laas/vego/internal/logic"
)

// The translation of the logic into SMT-LIB.
//
// Integers and references are Int, booleans are Bool, and floats and errors
// are uninterpreted sorts. The nil error is a constant, an error is nil
// exactly when it equals that constant, and some error is not nil. Two
// errors are the same error when they are equal, and whether errors.Is
// reports true for them is an uninterpreted function.
//
// A sequence is a datatype of an (Array Int E) and a raw length, so reads
// are total: a read outside the length gives some value, and a filled
// sequence holds its value at every index. The length of a sequence is its
// raw length, or zero where that is negative. No Go value has a negative
// length, so a sequence the problem names needs no fact about it, and one
// constructed with a negative length, which code that runs never builds, is
// empty. The operations on sequences are functions defined once per sort,
// so that every operation of the logic becomes one application.
//
// Go's division and remainder truncate toward zero; SMT-LIB's are
// Euclidean, and a division by zero is left to an uninterpreted function of
// the dividend, which is all the logic says about it.
//
// The key of a sequence is an uninterpreted function. For every two
// sequences keyed outside quantifiers, the keys are stated to be equal
// exactly when the contents are. A key inside a quantifier gets no such
// fact, which can only keep something from being proved.
//
// The translation adds no quantifier of its own beyond the one in that
// statement about contents, and builds no array by a lambda except for the
// concatenation and the cutting of sequences: both keep Z3 from finding
// models of facts that have one.
//
// Constants, bound variables, and predicates are given generated names, so
// that no name of the logic needs quoting. A ground subterm that occurs
// more than once becomes a definition of its own, so that the text grows
// with the number of distinct subterms and not with the size of the term
// written out as a tree.

// encoder writes one problem as SMT-LIB commands.
type encoder struct {
	out   strings.Builder
	preds map[string]*logic.PredDef
	// sorts holds the declared sorts by the sort of the logic they stand
	// for, after references are taken for integers.
	sorts map[logic.Sort]string
	// keyed holds the sequence sorts whose key functions are declared.
	keyed map[logic.Sort]bool
	// consts holds the declared constants by name, with their sorts.
	consts     map[string]string
	constSorts map[string]string
	// defined holds the predicates already written, and defining those of
	// the group being written.
	defined  map[string]string
	defining map[string]string
	// uses counts the parents of each node of the problem, and shared
	// holds the names of the subterms written as definitions.
	uses   map[*logic.Term]int
	shared map[*logic.Term]string
	ground map[*logic.Term]bool
	// scopes maps the bound variables in scope to their names, innermost
	// last.
	scopes   []map[string]string
	division bool
	names    int
	// universal holds the constants that stand for bound variables of the
	// quantifier around the whole problem, by name.
	universal map[string]string
	// keys holds the sequences keyed outside quantifiers.
	keys []keyed
	// polarity is 1 while a formula is encoded that is asserted, -1 while
	// one is encoded that is denied, and 0 where it is both or neither.
	// It only decides where shifted copies of facts are worth adding.
	polarity int
}

// fault reports a term that the logic does not allow where it stands. It is
// a fault of the verifier, not of the program being verified.
func fault(format string, args ...any) {
	panic(fmt.Sprintf("vego solver: "+format, args...))
}

func (e *encoder) name(prefix string) string {
	e.names++
	return prefix + strconv.Itoa(e.names)
}

// count records the parents of every node reachable from t.
func (e *encoder) count(t *logic.Term) {
	e.uses[t]++
	if e.uses[t] == 1 {
		for _, arg := range t.Args {
			e.count(arg)
		}
	}
	// A write is encoded with its table twice; see node. The table counts
	// once more only after it has been visited, so that its own parts are
	// counted too.
	if t.Op == logic.OpWrite {
		e.uses[t.Args[0]]++
	}
}

// isGround reports whether a term mentions no bound variable.
func (e *encoder) isGround(t *logic.Term) bool {
	if t.Op == logic.OpBound || (t.Op == logic.OpConst && e.universal[t.Name] != "") {
		return false
	}
	if len(t.Args) == 0 {
		return true
	}
	if cached, ok := e.ground[t]; ok {
		return cached
	}
	result := !slices.ContainsFunc(t.Args, func(arg *logic.Term) bool { return !e.isGround(arg) })
	e.ground[t] = result
	return result
}

// assert writes a formula as an assertion.
func (e *encoder) assert(f *logic.Term) {
	if f.Sort != logic.Bool {
		fault("asserting a term of sort %v", f.Sort)
	}
	var b strings.Builder
	e.polarity = 1
	e.term(&b, f)
	e.out.WriteString("(assert ")
	e.out.WriteString(b.String())
	e.out.WriteString(")\n")
}

// assertForall writes the facts as one assertion quantified over the given
// constants.
func (e *encoder) assertForall(consts []*logic.Term, facts []*logic.Term) {
	e.universal = map[string]string{}
	var vars strings.Builder
	for _, c := range consts {
		if c.Op != logic.OpConst {
			fault("quantifying over %v, which is not a constant", c)
		}
		if _, dup := e.universal[c.Name]; dup {
			continue
		}
		name := e.name("u")
		e.universal[c.Name] = name
		fmt.Fprintf(&vars, "(%s %s)", name, e.sort(c.Sort))
	}
	var body strings.Builder
	e.polarity = 1
	body.WriteString("(and true")
	for _, f := range facts {
		if f.Sort != logic.Bool {
			fault("asserting a term of sort %v", f.Sort)
		}
		body.WriteByte(' ')
		e.term(&body, f)
	}
	body.WriteByte(')')
	fmt.Fprintf(&e.out, "(assert (forall (%s) %s))\n", vars.String(), body.String())
	e.universal = nil
}

// plain returns the sort of the logic that s is encoded as: a reference is
// an integer, also inside sequences.
func plain(s logic.Sort) logic.Sort {
	if s.IsSeq() {
		return logic.SeqOf(plain(s.Elem()))
	}
	if s == logic.Ref {
		return logic.Int
	}
	return s
}

// sort returns the SMT-LIB sort of a sort of the logic, declaring it first
// if needed.
func (e *encoder) sort(s logic.Sort) string {
	s = plain(s)
	if name, ok := e.sorts[s]; ok {
		return name
	}
	var name string
	switch {
	case s == logic.Int:
		name = "Int"
	case s == logic.Bool:
		name = "Bool"
	case s == logic.Float:
		name = "Float"
		e.out.WriteString("(declare-sort Float 0)\n")
	case s == logic.Err:
		name = "Err"
		// Some error is not nil. Without that fact a model could have
		// only the nil error, and in it every error would be nil. Whether
		// errors.Is reports true for two errors is a function of them and
		// nothing more.
		e.out.WriteString("(declare-sort Err 0)\n(declare-const nil Err)\n(declare-const some-error Err)\n(assert (not (= some-error nil)))\n" +
			"(declare-fun error-is (Err Err) Bool)\n")
	case s.IsSeq():
		elem := e.sort(s.Elem())
		name = "Seq" + elem
		array := "(Array Int " + elem + ")"
		r := strings.NewReplacer("S", name, "E", elem, "A", array)
		for _, line := range []string{
			"(declare-datatype S ((S.mk (S.at A) (S.raw Int))))",
			"(define-fun S.len ((s S)) Int (ite (< (S.raw s) 0) 0 (S.raw s)))",
			"(define-fun S.store ((s S) (i Int) (v E)) S (S.mk (store (S.at s) i v) (S.raw s)))",
			"(define-fun S.fill ((n Int) (v E)) S (S.mk ((as const A) v) n))",
			"(define-fun S.push ((s S) (v E)) S (S.mk (store (S.at s) (S.len s) v) (+ (S.len s) 1)))",
			"(define-fun S.concat ((a S) (b S)) S (S.mk (lambda ((j Int)) (ite (< j (S.len a)) (select (S.at a) j) (select (S.at b) (- j (S.len a))))) (+ (S.len a) (S.len b))))",
			"(define-fun S.sub ((s S) (lo Int) (hi Int)) S (S.mk (lambda ((j Int)) (select (S.at s) (+ lo j))) (- hi lo)))",
		} {
			// The names of the sort and of its element are replaced as
			// whole words: the line is split on the characters that
			// delimit symbols.
			e.out.WriteString(replaceSymbols(line, r))
			e.out.WriteByte('\n')
		}
	default:
		fault("no encoding for sort %v", s)
	}
	e.sorts[s] = name
	return name
}

// replaceSymbols applies a replacer to the symbols S, E, and A and to the
// symbols that begin with "S." in a line, leaving every other symbol alone.
func replaceSymbols(line string, r *strings.Replacer) string {
	var b strings.Builder
	start := -1
	flush := func(end int) {
		if start < 0 {
			return
		}
		word := line[start:end]
		switch {
		case word == "S" || word == "E" || word == "A":
			b.WriteString(r.Replace(word))
		case strings.HasPrefix(word, "S."):
			b.WriteString(r.Replace("S"))
			b.WriteString(word[1:])
		default:
			b.WriteString(word)
		}
		start = -1
	}
	for i := range len(line) {
		switch c := line[i]; c {
		case '(', ')', ' ':
			flush(i)
			b.WriteByte(c)
		default:
			if start < 0 {
				start = i
			}
		}
	}
	flush(len(line))
	return b.String()
}

// constant returns the name of a constant of the logic, declaring it first.
func (e *encoder) constant(t *logic.Term) string {
	if t.Op == logic.OpConst && t.Name == "nil" && t.Sort == logic.Err {
		e.sort(logic.Err)
		return "nil"
	}
	if name := e.universal[t.Name]; name != "" {
		return name
	}
	sort := e.sort(t.Sort)
	if name, ok := e.consts[t.Name]; ok {
		if e.constSorts[t.Name] != sort {
			fault("constant %s is used with sorts %s and %s", t.Name, e.constSorts[t.Name], sort)
		}
		return name
	}
	name := e.name("c")
	e.consts[t.Name] = name
	e.constSorts[t.Name] = sort
	fmt.Fprintf(&e.out, "(declare-const %s %s) ; %s\n", name, sort, comment(t.Name))
	return name
}

// comment makes a name safe to write after a semicolon.
func comment(name string) string {
	return strings.Map(func(r rune) rune {
		if r == '\n' || r == '\r' {
			return ' '
		}
		return r
	}, name)
}

// key writes the key of a sequence, declaring the key function of its sort
// first. A sequence keyed outside a quantifier is given a name, once for
// each sequence, and the facts that relate the keys of such sequences are
// written once the problem is complete; see keyFacts.
func (e *encoder) key(b *strings.Builder, t *logic.Term) {
	s := plain(t.Args[0].Sort)
	if s.Elem().IsSeq() {
		fault("a key of a sequence of sequences, %v", s)
	}
	sort := e.sort(s)
	if !e.keyed[s] {
		e.keyed[s] = true
		fmt.Fprintf(&e.out, "(declare-fun %s.key (%s) Int)\n", sort, sort)
	}
	var seq strings.Builder
	e.term(&seq, t.Args[0])
	text := seq.String()
	if e.isGround(t) {
		i := slices.IndexFunc(e.keys, func(k keyed) bool { return k.text == text })
		if i < 0 {
			name := e.name("k")
			fmt.Fprintf(&e.out, "(define-fun %s () %s %s)\n", name, sort, text)
			e.keys = append(e.keys, keyed{sort, name, text})
			i = len(e.keys) - 1
		}
		text = e.keys[i].name
	}
	fmt.Fprintf(b, "(%s.key %s)", sort, text)
}

// keyed is a sequence keyed outside a quantifier: its sort, the name it is
// given, and its encoding.
type keyed struct{ sort, name, text string }

// keyFacts states, for every two sequences of one sort keyed outside
// quantifiers, that their keys are equal exactly when they have the same
// length and the same elements below it. That is true of a function that
// numbers the contents of sequences, and such a function exists, since
// those contents are countable.
func (e *encoder) keyFacts() {
	for i, a := range e.keys {
		for _, b := range e.keys[i+1:] {
			if a.sort != b.sort {
				continue
			}
			j := e.name("j")
			fmt.Fprintf(&e.out, "(assert (= (= (%[1]s.key %[2]s) (%[1]s.key %[3]s)) "+
				"(and (= (%[1]s.len %[2]s) (%[1]s.len %[3]s)) (forall ((%[4]s Int)) "+
				"(=> (and (<= 0 %[4]s) (< %[4]s (%[1]s.len %[2]s))) (= (select (%[1]s.at %[2]s) %[4]s) (select (%[1]s.at %[3]s) %[4]s)))))))\n",
				a.sort, a.name, b.name, j)
		}
	}
}

// pred returns the name of a recursive predicate, writing its definition
// first, and with it the definitions of every predicate it reaches. A
// group of predicates that reach each other are functions with their
// definitions as axioms; a predicate outside the group that a body uses is
// a macro.
func (e *encoder) pred(name string) string {
	if symbol, ok := e.defined[name]; ok {
		return symbol
	}
	if symbol, ok := e.defining[name]; ok {
		return symbol
	}
	group := e.group(name)
	recursive := len(group) > 1 || e.reaches(name, name)
	params := map[string][]string{}
	for _, member := range group {
		e.defining[member] = e.name("p")
		for range e.preds[member].Params {
			params[member] = append(params[member], e.name("x"))
		}
	}
	if recursive {
		for _, member := range group {
			var sorts strings.Builder
			for _, param := range e.preds[member].Params {
				sorts.WriteString(" " + e.sort(param.Sort))
			}
			fmt.Fprintf(&e.out, "(declare-fun %s (%s) Bool)\n", e.defining[member], strings.TrimSpace(sorts.String()))
		}
	}
	// Everything the definitions need is declared before the group is
	// written: the sorts of the parameters, and the predicates outside the
	// group that the bodies use, which encoding the bodies writes.
	headers := make([]string, len(group))
	bodies := make([]string, len(group))
	for i, member := range group {
		def := e.preds[member]
		var b strings.Builder
		fmt.Fprintf(&b, "%s (", e.defining[member])
		scope := map[string]string{}
		for j, param := range def.Params {
			scope[param.Name] = params[member][j]
			fmt.Fprintf(&b, "(%s %s)", params[member][j], e.sort(param.Sort))
		}
		b.WriteString(") Bool")
		headers[i] = b.String()
		e.scopes = append(e.scopes, scope)
		var body strings.Builder
		saved := e.polarity
		e.polarity = 0
		e.term(&body, def.Body)
		e.polarity = saved
		e.scopes = e.scopes[:len(e.scopes)-1]
		bodies[i] = body.String()
	}
	if !recursive {
		fmt.Fprintf(&e.out, "(define-fun %s %s) ; %s\n", headers[0], bodies[0], comment(name))
	} else {
		// A recursive predicate is a function with its definition as an
		// axiom, which Z3 unfolds where an application occurs. Recursion
		// only in positive position has a fixed point, so the axioms have
		// a model.
		for i, member := range group {
			def := e.preds[member]
			var vars, args strings.Builder
			for j, param := range def.Params {
				fmt.Fprintf(&vars, "(%s %s)", params[member][j], e.sort(param.Sort))
				args.WriteString(" " + params[member][j])
			}
			application := "(" + e.defining[member] + args.String() + ")"
			if len(def.Params) == 0 {
				fmt.Fprintf(&e.out, "(assert (= %s %s)) ; %s\n", e.defining[member], bodies[i], comment(member))
				continue
			}
			fmt.Fprintf(&e.out, "(assert (forall (%s) (! (= %s %s) :pattern (%s)))) ; %s\n",
				vars.String(), application, bodies[i], application, comment(member))
		}
	}
	for _, member := range group {
		e.defined[member] = e.defining[member]
		delete(e.defining, member)
	}
	return e.defined[name]
}

// group returns the predicates that reach name and that name reaches,
// including name, in a fixed order.
func (e *encoder) group(name string) []string {
	var group []string
	for other := range e.preds {
		if other == name || (e.reaches(name, other) && e.reaches(other, name)) {
			group = append(group, other)
		}
	}
	slices.Sort(group)
	return group
}

// reaches reports whether the body of from applies to, directly or through
// other predicates.
func (e *encoder) reaches(from, to string) bool {
	seen := map[string]bool{}
	var visit func(current string) bool
	visit = func(current string) bool {
		def := e.preds[current]
		if def == nil {
			fault("predicate %s is not defined", current)
		}
		found := false
		walk(def.Body, func(t *logic.Term) {
			if t.Op != logic.OpPred || found {
				return
			}
			if t.Name == to {
				found = true
			} else if !seen[t.Name] {
				seen[t.Name] = true
				found = visit(t.Name)
			}
		})
		return found
	}
	return visit(from)
}

// walk calls visit for every node of a term, once for each occurrence.
func walk(t *logic.Term, visit func(*logic.Term)) {
	visit(t)
	for _, arg := range t.Args {
		walk(arg, visit)
	}
}

// term writes the encoding of a term.
func (e *encoder) term(b *strings.Builder, t *logic.Term) {
	if name, ok := e.shared[t]; ok {
		b.WriteString(name)
		return
	}
	if len(t.Args) > 0 && e.uses[t] > 1 && e.isGround(t) {
		var def strings.Builder
		e.node(&def, t)
		name := e.name("t")
		fmt.Fprintf(&e.out, "(define-fun %s () %s %s)\n", name, e.sort(t.Sort), def.String())
		e.shared[t] = name
		b.WriteString(name)
		return
	}
	e.node(b, t)
}

// node writes one node of a term, encoding its arguments with term.
func (e *encoder) node(b *strings.Builder, t *logic.Term) {
	checkSorts(t)
	apply := func(head string, args ...*logic.Term) {
		b.WriteByte('(')
		b.WriteString(head)
		for _, arg := range args {
			b.WriteByte(' ')
			e.term(b, arg)
		}
		b.WriteByte(')')
	}
	// within encodes the arguments of a node with the polarity each has:
	// flip says which are denied when the node is asserted, and both which
	// are used either way.
	saved := e.polarity
	defer func() { e.polarity = saved }()
	within := func(head string, polarities ...int) {
		b.WriteByte('(')
		b.WriteString(head)
		for i, arg := range t.Args {
			e.polarity = saved * polarities[min(i, len(polarities)-1)]
			b.WriteByte(' ')
			e.term(b, arg)
		}
		e.polarity = saved
		b.WriteByte(')')
	}
	seqOp := func(op string) string { return e.sort(t.Args[0].Sort) + "." + op }
	switch t.Op {
	case logic.OpIntLit:
		value := t.Value()
		if value.Sign() < 0 {
			b.WriteString("(- ")
			b.WriteString(new(big.Int).Neg(value).String())
			b.WriteByte(')')
		} else {
			b.WriteString(value.String())
		}
	case logic.OpTrue:
		b.WriteString("true")
	case logic.OpFalse:
		b.WriteString("false")
	case logic.OpConst:
		b.WriteString(e.constant(t))
	case logic.OpBound:
		for i := len(e.scopes) - 1; i >= 0; i-- {
			if name, ok := e.scopes[i][t.Name]; ok {
				b.WriteString(name)
				return
			}
		}
		fault("bound variable %s is not in scope", t.Name)
	case logic.OpAdd:
		apply("+", t.Args...)
	case logic.OpMul:
		apply("*", t.Args...)
	case logic.OpNeg:
		apply("-", t.Args...)
	case logic.OpDiv, logic.OpMod:
		if !e.division {
			e.division = true
			e.out.WriteString(division)
		}
		if t.Op == logic.OpDiv {
			apply("go.div", t.Args...)
		} else {
			apply("go.mod", t.Args...)
		}
	case logic.OpLen:
		apply(seqOp("len"), t.Args...)
	case logic.OpSelect:
		if read := reduceRead(t); read != nil {
			e.term(b, read)
			return
		}
		b.WriteString("(select (")
		b.WriteString(seqOp("at"))
		b.WriteByte(' ')
		e.term(b, t.Args[0])
		b.WriteString(") ")
		e.term(b, t.Args[1])
		b.WriteByte(')')
	case logic.OpStore:
		apply(seqOp("store"), t.Args...)
	case logic.OpWrite:
		// The table is used twice; count made it shared, so that it is
		// written once.
		e.node(b, logic.Expand(t))
	case logic.OpFill:
		apply(e.sort(t.Sort)+".fill", t.Args...)
	case logic.OpPush:
		apply(seqOp("push"), t.Args...)
	case logic.OpConcat:
		apply(seqOp("concat"), t.Args...)
	case logic.OpSub:
		apply(seqOp("sub"), t.Args...)
	case logic.OpIsNil:
		e.sort(logic.Err)
		b.WriteString("(= ")
		e.term(b, t.Args[0])
		b.WriteString(" nil)")
	case logic.OpIs:
		e.sort(logic.Err)
		apply("error-is", t.Args...)
	case logic.OpKey:
		e.key(b, t)
	case logic.OpIte:
		within("ite", 0, 1)
	case logic.OpEq:
		if t.Args[0].Sort.IsSeq() || t.Args[1].Sort.IsSeq() {
			fault("equality of sequences %v", t)
		}
		if plain(t.Args[0].Sort) != plain(t.Args[1].Sort) {
			fault("equality of a %v and a %v: %v", t.Args[0].Sort, t.Args[1].Sort, t)
		}
		within("=", 0)
	case logic.OpLe:
		apply("<=", t.Args...)
	case logic.OpLt:
		apply("<", t.Args...)
	case logic.OpAnd:
		apply("and", t.Args...)
	case logic.OpOr:
		apply("or", t.Args...)
	case logic.OpNot:
		within("not", -1)
	case logic.OpImplies:
		within("=>", -1, 1)
	case logic.OpIff:
		within("=", 0)
	case logic.OpForall, logic.OpExists:
		variable := t.Args[0]
		if variable.Op != logic.OpBound {
			fault("quantifier over %v", variable)
		}
		name := e.name("b")
		e.scopes = append(e.scopes, map[string]string{variable.Name: name})
		quantifier := "forall"
		if t.Op == logic.OpExists {
			quantifier = "exists"
		}
		shifts := e.shifts(t)
		if len(shifts) > 0 {
			b.WriteString("(and ")
		}
		fmt.Fprintf(b, "(%s ((%s %s)) ", quantifier, name, e.sort(variable.Sort))
		e.term(b, t.Args[1])
		b.WriteByte(')')
		e.scopes = e.scopes[:len(e.scopes)-1]
		for _, shift := range shifts {
			e.shifted(b, shift)
		}
		if len(shifts) > 0 {
			b.WriteByte(')')
		}
	case logic.OpPred:
		def := e.preds[t.Name]
		if def == nil {
			fault("predicate %s is not defined", t.Name)
		}
		if len(def.Params) != len(t.Args) {
			fault("predicate %s takes %d arguments, applied to %d", t.Name, len(def.Params), len(t.Args))
		}
		if !e.reaches(t.Name, t.Name) {
			// A predicate that does not reach itself is written out in
			// place, so that its reads are reduced like any other. The
			// variables the body binds are renamed first, so that none can
			// capture a variable bound around the application.
			bindings := map[string]*logic.Term{}
			for i, param := range def.Params {
				bindings[param.Name] = t.Args[i]
			}
			e.term(b, logic.Subst(e.freshen(def.Body), bindings))
			return
		}
		symbol := e.pred(t.Name)
		e.polarity = 0
		apply(symbol, t.Args...)
	case logic.OpPair:
		fault("a pointer outside a comparison: %v", t)
	case logic.OpFuncVal:
		fault("a function value outside a comparison: %v", t)
	case logic.OpIfaceVal:
		fault("an interface value outside a comparison: %v", t)
	default:
		fault("no encoding for %v", t)
	}
}

// division defines Go's division and remainder.
const division = `(declare-fun go.div0 (Int) Int)
(declare-fun go.mod0 (Int) Int)
(define-fun go.div ((a Int) (b Int)) Int (ite (= b 0) (go.div0 a) (ite (<= 0 a) (div a b) (- (div (- a) b)))))
(define-fun go.mod ((a Int) (b Int)) Int (ite (= b 0) (go.mod0 a) (ite (<= 0 a) (mod a b) (- (mod (- a) b)))))
`

// checkSorts rejects a node whose arguments have sorts its operator does
// not take. Z3 converts between booleans and integers where SMT-LIB does
// not allow it, so such a node would be read as something else instead of
// being refused.
func checkSorts(t *logic.Term) {
	numeric := func(a *logic.Term) bool { return plain(a.Sort) == logic.Int }
	is := func(a *logic.Term, s logic.Sort) bool { return plain(a.Sort) == plain(s) }
	arity := func(n int) bool { return len(t.Args) == n }
	allBool := func() bool {
		return !slices.ContainsFunc(t.Args, func(a *logic.Term) bool { return a.Sort != logic.Bool })
	}
	ok := true
	switch t.Op {
	case logic.OpIntLit:
		ok = numeric(t)
	case logic.OpTrue, logic.OpFalse:
		ok = t.Sort == logic.Bool
	case logic.OpAdd, logic.OpMul, logic.OpDiv, logic.OpMod:
		ok = arity(2) && numeric(t) && numeric(t.Args[0]) && numeric(t.Args[1])
	case logic.OpNeg:
		ok = arity(1) && numeric(t) && numeric(t.Args[0])
	case logic.OpLen:
		ok = arity(1) && numeric(t) && t.Args[0].Sort.IsSeq()
	case logic.OpSelect:
		ok = arity(2) && t.Args[0].Sort.IsSeq() && numeric(t.Args[1]) && is(t, t.Args[0].Sort.Elem())
	case logic.OpStore:
		ok = arity(3) && t.Args[0].Sort.IsSeq() && numeric(t.Args[1]) && is(t.Args[2], t.Args[0].Sort.Elem()) && is(t, t.Args[0].Sort)
	case logic.OpWrite:
		ok = arity(4) && t.Args[0].Sort.IsSeq() && t.Args[0].Sort.Elem().IsSeq() && numeric(t.Args[1]) && numeric(t.Args[2]) &&
			is(t.Args[3], t.Args[0].Sort.Elem().Elem()) && is(t, t.Args[0].Sort)
	case logic.OpFill:
		ok = arity(2) && numeric(t.Args[0]) && is(t, logic.SeqOf(t.Args[1].Sort))
	case logic.OpPush:
		ok = arity(2) && t.Args[0].Sort.IsSeq() && is(t.Args[1], t.Args[0].Sort.Elem()) && is(t, t.Args[0].Sort)
	case logic.OpConcat:
		ok = arity(2) && t.Args[0].Sort.IsSeq() && is(t.Args[1], t.Args[0].Sort) && is(t, t.Args[0].Sort)
	case logic.OpSub:
		ok = arity(3) && t.Args[0].Sort.IsSeq() && numeric(t.Args[1]) && numeric(t.Args[2]) && is(t, t.Args[0].Sort)
	case logic.OpIsNil:
		ok = arity(1) && t.Sort == logic.Bool && t.Args[0].Sort == logic.Err
	case logic.OpIs:
		ok = arity(2) && t.Sort == logic.Bool && t.Args[0].Sort == logic.Err && t.Args[1].Sort == logic.Err
	case logic.OpKey:
		ok = arity(1) && numeric(t) && t.Args[0].Sort.IsSeq()
	case logic.OpIte:
		ok = arity(3) && t.Args[0].Sort == logic.Bool && is(t.Args[1], t.Sort) && is(t.Args[2], t.Sort)
	case logic.OpEq:
		ok = arity(2) && t.Sort == logic.Bool && is(t.Args[0], t.Args[1].Sort)
	case logic.OpLe, logic.OpLt:
		ok = arity(2) && t.Sort == logic.Bool && numeric(t.Args[0]) && numeric(t.Args[1])
	case logic.OpAnd, logic.OpOr:
		ok = t.Sort == logic.Bool && allBool()
	case logic.OpNot:
		ok = arity(1) && t.Sort == logic.Bool && allBool()
	case logic.OpImplies, logic.OpIff:
		ok = arity(2) && t.Sort == logic.Bool && allBool()
	case logic.OpForall, logic.OpExists:
		ok = arity(2) && t.Sort == logic.Bool && t.Args[1].Sort == logic.Bool
	case logic.OpPred:
		ok = t.Sort == logic.Bool
	}
	if !ok {
		fault("a term whose sorts do not fit its operator: %v", t)
	}
}

// shift is a read in the body of a universally quantified fact whose index
// is the bound variable scaled and moved: the fact matters at the read of
// base at scale*x + offset, for a base and an offset that do not depend on
// the bound variable. Z3 matches a read of base against a read of base, but
// not an index against a sum, so a fact about A[k + lo] would never be
// applied to a read of A[j].
type shift struct {
	fact   *logic.Term
	base   *logic.Term
	scale  int64
	offset *logic.Term
	key    string
}

// shiftOf returns the shift of a read in a fact about the bound variable,
// if the read is one. A read of a cut of a sequence counts as a read of the
// sequence it was cut from.
func (e *encoder) shiftOf(read *logic.Term, variable string) (shift, bool) {
	if read.Op != logic.OpSelect {
		return shift{}, false
	}
	base, index := read.Args[0], read.Args[1]
	cut := false
	if base.Op == logic.OpSub && e.isGround(base.Args[1]) {
		base, index, cut = base.Args[0], logic.Add(base.Args[1], index), true
	}
	if !e.isGround(base) {
		return shift{}, false
	}
	scale, offset, ok := linear(index, variable, e.isGround)
	if !ok || scale == 0 || (offset == nil && !cut && scale == 1) {
		// The read of the variable itself is one Z3 matches.
		return shift{}, false
	}
	if offset == nil {
		offset = logic.IntLit(0)
	}
	return shift{base: base, scale: scale, offset: offset, key: fmt.Sprintf("%p|%d|%s", base, scale, offset.String())}, true
}

// shifts returns the shifted reads of a universally quantified fact that
// is asserted, one for each base, scale, and offset.
func (e *encoder) shifts(t *logic.Term) []shift {
	if t.Op != logic.OpForall || e.polarity <= 0 {
		return nil
	}
	// A fact with a quantifier inside gets no copies: each level would
	// copy the levels inside it, and the copies would outgrow the fact.
	nested := false
	walk(t.Args[1], func(inner *logic.Term) {
		nested = nested || inner.Op == logic.OpForall || inner.Op == logic.OpExists
	})
	if nested {
		return nil
	}
	variable := t.Args[0].Name
	var found []shift
	seen := map[string]bool{}
	walk(t.Args[1], func(read *logic.Term) {
		if sh, ok := e.shiftOf(read, variable); ok && !seen[sh.key] {
			seen[sh.key] = true
			sh.fact = t
			found = append(found, sh)
		}
	})
	return found
}

// shifted writes the copy of a fact for one shifted read: for every index
// i, the fact at the variable whose read is i, triggered by reads of the
// base. When the scale is not one, only an index the scale divides into
// stands for a value of the variable. In the copy, each read with this
// shift is written as the read of the base at i, which it equals, so that
// an instance mentions the read that triggered it and no other: a read at
// an index written as a sum would trigger the copy again. The copy is an
// instance of the fact for each i, so it says nothing new.
func (e *encoder) shifted(b *strings.Builder, sh shift) {
	e.names++
	index := logic.Bound("shift#"+strconv.Itoa(e.names), logic.Int)
	variable := sh.fact.Args[0].Name
	moved := logic.Sub(index, sh.offset)
	var value, guard *logic.Term
	switch sh.scale {
	case 1:
		value = moved
	case -1:
		value = logic.Neg(moved)
	default:
		value = logic.Div(moved, logic.IntLit(sh.scale))
		guard = logic.Eq(logic.Mod(moved, logic.IntLit(sh.scale)), logic.IntLit(0))
	}
	var rewrite func(t *logic.Term) *logic.Term
	rewrite = func(t *logic.Term) *logic.Term {
		if other, ok := e.shiftOf(t, variable); ok && other.key == sh.key {
			return logic.Select(sh.base, index)
		}
		if t.Op == logic.OpBound && t.Name == variable {
			return value
		}
		if len(t.Args) == 0 || e.isGround(t) {
			return t
		}
		args := make([]*logic.Term, len(t.Args))
		for i, arg := range t.Args {
			args[i] = rewrite(arg)
		}
		return logic.WithArgs(t, args)
	}
	body := rewrite(sh.fact.Args[1])
	if guard != nil {
		body = logic.Implies(guard, body)
	}
	name := e.name("b")
	e.scopes = append(e.scopes, map[string]string{index.Name: name})
	var inner, base strings.Builder
	e.term(&inner, body)
	e.term(&base, sh.base)
	e.scopes = e.scopes[:len(e.scopes)-1]
	fmt.Fprintf(b, " (forall ((%s Int)) (! %s :pattern ((select (%s.at %s) %s))))", name, inner.String(), e.sort(sh.base.Sort), base.String(), name)
}

// linear writes an index as scale*x + offset for the bound variable x,
// where the offset is ground, or nil for zero. It fails for an index that
// is not of that form.
func linear(t *logic.Term, variable string, ground func(*logic.Term) bool) (scale int64, offset *logic.Term, ok bool) {
	add := func(a, b *logic.Term) *logic.Term {
		switch {
		case a == nil:
			return b
		case b == nil:
			return a
		}
		return logic.Add(a, b)
	}
	switch {
	case t.Op == logic.OpBound && t.Name == variable:
		return 1, nil, true
	case ground(t):
		return 0, t, true
	case t.Op == logic.OpAdd:
		s1, o1, ok1 := linear(t.Args[0], variable, ground)
		s2, o2, ok2 := linear(t.Args[1], variable, ground)
		sum := new(big.Int).Add(big.NewInt(s1), big.NewInt(s2))
		if !ok1 || !ok2 || !sum.IsInt64() {
			return 0, nil, false
		}
		return sum.Int64(), add(o1, o2), true
	case t.Op == logic.OpNeg:
		s, o, ok := linear(t.Args[0], variable, ground)
		if !ok || s == math.MinInt64 {
			return 0, nil, false
		}
		if o != nil {
			o = logic.Neg(o)
		}
		return -s, o, true
	case t.Op == logic.OpMul:
		for i := range 2 {
			factor, other := t.Args[i], t.Args[1-i]
			if factor.Op != logic.OpIntLit || factor.Big != nil {
				continue
			}
			s, o, ok := linear(other, variable, ground)
			if !ok {
				return 0, nil, false
			}
			product := new(big.Int).Mul(big.NewInt(s), big.NewInt(factor.Val))
			if !product.IsInt64() {
				return 0, nil, false
			}
			if o != nil {
				o = logic.Mul(factor, o)
			}
			return product.Int64(), o, true
		}
	}
	return 0, nil, false
}

// reduceRead returns the read that a read of a constructed sequence equals,
// or nil: a read of a cut is a read of the sequence it was cut from, a
// read of a filled sequence is its value, and a read of a concatenation is
// a read of one of its halves. The definitions of the sequence functions
// say the same, through arrays built by lambdas; Z3 reasons poorly about
// reads of those, and a quantified fact about a cut would otherwise be
// matched against every read of the whole.
func reduceRead(t *logic.Term) *logic.Term {
	seq, index := t.Args[0], t.Args[1]
	switch seq.Op {
	case logic.OpSub:
		return logic.Select(seq.Args[0], logic.Add(seq.Args[1], index))
	case logic.OpFill:
		return seq.Args[1]
	case logic.OpConcat:
		first := logic.Len(seq.Args[0])
		return logic.Ite(logic.Lt(index, first), logic.Select(seq.Args[0], index), logic.Select(seq.Args[1], logic.Sub(index, first)))
	}
	return nil
}

// freshen renames the variables a formula binds to names used nowhere else.
func (e *encoder) freshen(t *logic.Term) *logic.Term {
	if len(t.Args) == 0 {
		return t
	}
	if t.Op == logic.OpForall || t.Op == logic.OpExists {
		e.names++
		renamed := logic.Bound(t.Args[0].Name+"#inline"+strconv.Itoa(e.names), t.Args[0].Sort)
		body := e.freshen(logic.Subst(t.Args[1], map[string]*logic.Term{t.Args[0].Name: renamed}))
		if t.Op == logic.OpForall {
			return logic.Forall(renamed, body)
		}
		return logic.Exists(renamed, body)
	}
	args := make([]*logic.Term, len(t.Args))
	changed := false
	for i, arg := range t.Args {
		args[i] = e.freshen(arg)
		changed = changed || args[i] != arg
	}
	if !changed {
		return t
	}
	return logic.WithArgs(t, args)
}
