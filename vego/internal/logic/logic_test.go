package logic

import (
	"fmt"
	"strings"
	"testing"
)

type testEnv map[string]*Term

// Path looks a path up by its spelling: fields are part of the name, and
// elements are read from whatever the name denotes.
func (e testEnv) Path(root string, steps []Step, when When) (*Term, error) {
	name, state := root, ""
	var indices []*Term
	measured := false
	for _, step := range steps {
		switch {
		case step.State != "":
			state = step.State
		case step.Has:
			name = "has " + name
		case step.Len:
			measured = true
		case step.Field != "":
			name += "." + step.Field
		case step.Index.Sort != Int:
			return nil, fmt.Errorf("expected an integer but the index has type %s", step.Index.Sort)
		default:
			indices = append(indices, step.Index)
		}
	}
	switch when {
	case Primed:
		name += "'"
	case Old:
		name = "old " + name
	}
	if state != "" {
		// A state is known by its spelling, as held(p').
		if t, ok := e[state+"("+name+")"]; ok {
			return t, nil
		}
		return nil, &NoState{}
	}
	t, ok := e[name]
	if !ok {
		return nil, fmt.Errorf("unknown name %s", name)
	}
	for _, index := range indices {
		if !t.Sort.IsSeq() {
			return nil, fmt.Errorf("%s has type %s, not a slice", t, t.Sort)
		}
		t = Select(t, index)
	}
	if measured {
		if !t.Sort.IsSeq() {
			return nil, fmt.Errorf("%s has type %s, not a slice", t, t.Sort)
		}
		return Len(t), nil
	}
	return t, nil
}

func (e testEnv) Qualified(path, name string, steps []Step, when When) (*Term, error) {
	return e.Path(fmt.Sprintf("%q.%s", path, name), steps, when)
}

func (e testEnv) Relation(name string, paths []Path) (*Term, error) {
	for _, path := range paths {
		name += " " + path.Root + map[When]string{Primed: "'"}[path.When]
	}
	return Pred(name), nil
}

func TestResolve(t *testing.T) {
	env := testEnv{
		"A": Const("A", IntSeq), "A'": Const("A1", IntSeq), "old A": Const("A0", IntSeq),
		"i": Const("i", Int), "j": Const("j", Int), "n": Const("n", Int),
		"found": Const("found", Bool), "flags": Const("flags", BoolSeq),
		"s.count": Const("count0", Int), "s.count'": Const("count1", Int), "old s.count": Const("count0", Int),
		"s.items'": Const("items1", IntSeq), "p": Pair(Const("p", Ref), Const("p at", Int)), "q": Pair(Const("q", Ref), Const("q at", Int)), "m": Const("m", Ref), "f": FuncVal(Const("f", Ref)), "w": IfaceVal(Const("w", Ref)), "has A": Const("has A", Bool),
		"err": Const("err", Err), "ErrEmpty": Const("ErrEmpty", Err),
		"held(p)": Const("held p", Bool), "held(p')": Const("held p1", Bool), "held(old p)": Const("held p0", Bool),
	}
	resolver := NewResolver()
	sumTo, err := ParsePredicate("sumTo(A, i, s) ::= ((i <= 0 -> s = 0) And " +
		"(i > 0 -> Exists t in Z : (sumTo(A, i-1, t) And s = t + A[i-1])))")
	if err != nil {
		t.Fatalf("parse predicate: %v", err)
	}
	marked, err := ParsePredicate("marked(F, ok, k) ::= ok = True -> F[k]")
	if err != nil {
		t.Fatalf("parse predicate: %v", err)
	}
	wraps, err := ParsePredicate("wraps(e, t) ::= is(e, t) And e != t")
	if err != nil {
		t.Fatalf("parse predicate: %v", err)
	}
	if errs := resolver.Define([]*PredDecl{sumTo, marked, wraps}); len(errs) > 0 {
		t.Fatalf("define predicates: %v", errs[0].Err)
	}

	tests := []struct {
		src  string
		want string // rendered term, or an error message fragment prefixed with "error: "
	}{
		{"n >= 0 And i > 0", "((0 <= n) And (0 < i))"},
		{"s.count' = old(s.count) + 1", "(count1 = (count0 + 1))"},
		{"s.items'[i] = s.count", "(items1[i] = count0)"},
		{"p != nil And p != q", "(~(p = 0) And ~((p = q) And ((p = 0) Or (p at = q at))))"},
		{"nil = q -> fresh(p)", "((0 = q) -> fresh p())"},
		{"within(p', q)", "within p' q()"},
		{"within(p)", "error: within takes 2 argument(s)"},
		{"has(A, i) -> A[i] = 0", "(has A -> (A[i] = 0))"},
		{"has(A)", "error: has takes a map and a key"},
		{"fresh(p')", "error: fresh takes a parameter"},
		{"p < q", "error: operator < cannot be applied to a pointer"},
		{"m < m", "error: operator < cannot be applied to a map"},
		{"f < nil", "error: operator < cannot be applied to a function value"},
		{"nil < f", "error: operator < cannot be applied to a function value"},
		{"f = m", "error: a function value can only be compared with nil"},
		{"f = 0", "error: cannot compare f (function value) with 0 (int)"},
		{"m = 0", "error: cannot compare m (map) with 0 (int)"},
		{"f = nil", "(f = 0)"},
		{"w < nil", "error: operator < cannot be applied to an interface value"},
		{"w = f", "error: can only be compared with nil"},
		{"w = m", "error: an interface value can only be compared with nil"},
		{"w = w", "error: an interface value can only be compared with nil"},
		{"nil != w", "~(0 = w)"},
		{"old(s.count')", "error: old takes a parameter"},
		{"A.size", "error: unknown name A.size"},
		{"0 <= i <= j < |A|", "((0 <= i) And (i <= j) And (j < |A|))"},
		{"n = i*j + 1", "(n = ((i * j) + 1))"},
		{"n == i / 2 % 3 - -j", "(n = (((i / 2) % 3) + --j))"},
		{"found = True -> A[i] = n", "((found <-> True) -> (A[i] = n))"},
		{"~found Or i != j", "(~found Or ~(i = j))"},
		{"!found && flags[i] || found", "((~found And flags[i]) Or found)"},
		{"found <-> i < j -> j > i", "(found <-> ((i < j) -> (i < j)))"},
		{"|A| = |A'| And old(A)[0] = 1", "((|A| = |A1|) And (A0[0] = 1))"},
		{"Forall k in Z : A[k] >= 0", "(Forall k#1 : (True -> (0 <= A[k#1])))"},
		{"Forall k in [0, n) : A[k] = 0", "(Forall k#1 : (((0 <= k#1) And (k#1 < n)) -> (A[k#1] = 0)))"},
		{"Exists k in (i, j] : A[k] = 0", "(Exists k#1 : ((i < k#1) And (k#1 <= j) And (A[k#1] = 0)))"},
		{"A[j] >= A[0:j)", "(Forall k#1 : (((0 <= k#1) And (k#1 < j)) -> (A[k#1] <= A[j])))"},
		{"A[i:j] = 0", "(Forall k#1 : (((i <= k#1) And (k#1 <= j)) -> (A[k#1] = 0)))"},
		{"A' = A", "((|A1| = |A|) And (Forall k#1 : (((0 <= k#1) And (k#1 < |A1|)) -> (A1[k#1] = A[k#1]))))"},
		{"sumTo(A, |A|, n) And marked(flags, found, i)", "(sumTo(A, |A|, n) And marked(flags, found, i))"},
		{"n >", "error: expected an expression"},
		{"n > 0 )", "error: unexpected \")\""},
		{"n $ 0", "error: unexpected character"},
		{"n = \u0661", "error: unexpected character"},
		{"Forall k : k > 0", "error: expected \"in\""},
		{"A > 0", "error: cannot compare"},
		{"found + 1 = 2", "error: expected an integer"},
		{"n And found", "error: expected a formula"},
		{"A[found] = 0", "error: expected an integer"},
		{"n[0] = 0", "error: not a slice"},
		{"sumTo(A, i) ", "error: takes 3 arguments"},
		{"sumTo(i, i, i)", "error: argument 1 of sumTo has type int"},
		{"missing(i)", "error: unknown predicate missing"},
		{"k > 0", "error: unknown name k"},
		{"A[0:i)", "error: slice range"},
		{"err = nil Or err = ErrEmpty", "((err = nil) Or (err = ErrEmpty))"},
		{"err != ErrEmpty", "~(err = ErrEmpty)"},
		{"is(err, ErrEmpty) <-> |A| = 0", "(is(err, ErrEmpty) <-> (|A| = 0))"},
		{"is(err, nil)", "is(err, nil)"},
		{"wraps(err, ErrEmpty)", "wraps(err, ErrEmpty)"},
		{"err < ErrEmpty", "error: operator < cannot be applied to errors"},
		{"is(err)", "error: is takes two errors"},
		{"is(err, n)", "error: expected an error but n has type int"},
		{"err = n", "error: cannot compare"},
		{"held(p) -> ~held(p')", "(held p -> ~held p1)"},
		{"held(old(p))", "held p0"},
		{"held(old(p'))", "error: old(p) is the value on entry and cannot be primed"},
		{"held(i)", "error: unknown predicate held"},
	}
	for _, test := range tests {
		t.Run(test.src, func(t *testing.T) {
			resolver.fresh = 0
			got := ""
			node, err := ParseFormula(test.src)
			if err == nil {
				var term *Term
				if term, err = resolver.Formula(node, env); err == nil {
					got = term.String()
				}
			}
			if err != nil {
				got = "error: " + err.Error()
			}
			if fragment, isError := strings.CutPrefix(test.want, "error: "); isError {
				if !strings.HasPrefix(got, "error: ") || !strings.Contains(got, fragment) {
					t.Fatalf("got %q, want an error containing %q", got, fragment)
				}
				return
			}
			if got != test.want {
				t.Fatalf("got  %s\nwant %s", got, test.want)
			}
		})
	}
}

func TestDefine(t *testing.T) {
	tests := []struct {
		name string
		defs []string
		want string // error fragment, or empty when the definitions are accepted
	}{
		{"accepts positive recursion", []string{"even(n) ::= n = 0 Or (n > 1 And even(n - 2))"}, ""},
		{"accepts mutual positive recursion", []string{"p(n) ::= n <= 0 Or q(n - 1)", "q(n) ::= n > 0 And p(n - 1)"}, ""},
		{"rejects recursion under negation", []string{"liar(n) ::= ~liar(n)"}, "must not occur under negation"},
		{"rejects recursion left of an implication", []string{"p(n) ::= p(n) -> n > 0"}, "must not occur under negation"},
		{"rejects mutual recursion through negation", []string{"p(n) ::= ~q(n)", "q(n) ::= p(n)"}, "must not occur under negation"},
		{"rejects recursion through an argument that the callee negates",
			[]string{"negate(b) ::= ~b", "liar(n) ::= negate(liar(n))"}, "must not occur under negation"},
		{"rejects duplicate names", []string{"p(n) ::= n > 0", "p(n) ::= n < 0"}, "already defined"},
		{"rejects free names", []string{"p(n) ::= n > m"}, "may only mention their parameters"},
		{"rejects the name is", []string{"is(n) ::= n > 0"}, "already defined"},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			var decls []*PredDecl
			for _, def := range test.defs {
				decl, err := ParsePredicate(def)
				if err != nil {
					t.Fatalf("parse %q: %v", def, err)
				}
				decls = append(decls, decl)
			}
			errs := NewResolver().Define(decls)
			switch {
			case test.want == "" && len(errs) > 0:
				t.Fatalf("unexpected error: %v", errs[0].Err)
			case test.want != "" && len(errs) == 0:
				t.Fatalf("definitions were accepted, want an error containing %q", test.want)
			case test.want != "" && !strings.Contains(errs[0].Err.Error(), test.want):
				t.Fatalf("got error %q, want one containing %q", errs[0].Err, test.want)
			}
		})
	}
}

func TestParseTargets(t *testing.T) {
	tests := []struct {
		name string
		src  string
		want string // the targets as written, or an error message fragment prefixed with "error: "
	}{
		{"accepts one variable", "A", "A"},
		{"accepts fields and elements", "s.items, cs[i + 1].n, p", "s.items | cs[i + 1].n | p"},
		{"rejects a primed path", "A'", "error: a Modifies clause lists"},
		{"rejects an expression", "A + 1", "error: unexpected"},
		{"rejects a call", "old(A)", "error: a Modifies clause lists"},
		{"rejects an empty list", "", "error: expected an expression"},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			targets, err := ParseTargets(test.src)

			got := ""
			for i, target := range targets {
				if i > 0 {
					got += " | "
				}
				got += target.String()
			}
			if err != nil {
				got = "error: " + err.Error()
			}
			if !strings.HasPrefix(got, test.want) || (err == nil && got != test.want) {
				t.Fatalf("ParseTargets(%q) = %q, want %q", test.src, got, test.want)
			}
		})
	}
}

// applyingEnv gives f(x) the meaning of the element x of a sequence F.
type applyingEnv struct{ testEnv }

func (e applyingEnv) Apply(name string, args []*Term) (*Term, bool, error) {
	if name != "f" {
		return nil, false, nil
	}
	if len(args) != 1 || args[0].Sort != Int {
		return nil, true, fmt.Errorf("f takes one integer")
	}
	return Select(Const("F", SeqOf(Bool)), args[0]), true, nil
}

// TestApply checks that an environment that knows an application gives it
// its meaning, and that any other name is still a predicate.
func TestApply(t *testing.T) {
	env := applyingEnv{testEnv{"n": Const("n", Int)}}
	r := NewResolver()
	tests := []struct {
		formula, want, err string
	}{
		{formula: "Forall i in [0, n) : f(i) -> f(i + 1)", want: "Forall"},
		{formula: "f(n) And ~f(0)", want: "F"},
		{formula: "f(n, n)", err: "f takes one integer"},
		{formula: "g(n)", err: "unknown predicate g"},
	}
	for _, test := range tests {
		node, err := ParseFormula(test.formula)
		if err != nil {
			t.Fatalf("parse %q: %v", test.formula, err)
		}
		got, err := r.Formula(node, env)
		switch {
		case test.err != "" && (err == nil || !strings.Contains(err.Error(), test.err)):
			t.Errorf("%s: got %v, want an error containing %q", test.formula, err, test.err)
		case test.err == "" && err != nil:
			t.Errorf("%s: %v", test.formula, err)
		case test.err == "" && !strings.Contains(got.String(), test.want):
			t.Errorf("%s resolves to %s, which does not contain %s", test.formula, got, test.want)
		}
	}
}
