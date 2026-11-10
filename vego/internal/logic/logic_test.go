package logic

import (
	"fmt"
	"strings"
	"testing"
)

type testEnv map[string]*Term

func (e testEnv) Var(name string, primed bool) (*Term, error) {
	if primed {
		name += "'"
	}
	if t, ok := e[name]; ok {
		return t, nil
	}
	return nil, fmt.Errorf("unknown name %s", name)
}

func (e testEnv) Old(name string) (*Term, error) { return e.Var("old "+name, false) }

func TestResolve(t *testing.T) {
	env := testEnv{
		"A": Const("A", IntSeq), "A'": Const("A1", IntSeq), "old A": Const("A0", IntSeq),
		"i": Const("i", Int), "j": Const("j", Int), "n": Const("n", Int),
		"found": Const("found", Bool), "flags": Const("flags", BoolSeq),
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
	if errs := resolver.Define([]*PredDecl{sumTo, marked}); len(errs) > 0 {
		t.Fatalf("define predicates: %v", errs[0].Err)
	}

	tests := []struct {
		src  string
		want string // rendered term, or an error message fragment prefixed with "error: "
	}{
		{"n >= 0 And i > 0", "((0 <= n) And (0 < i))"},
		{"0 <= i <= j < |A|", "((0 <= i) And (i <= j) And (j < |A|))"},
		{"n = i*j + 1", "(n = ((i * j) + 1))"},
		{"n == i / 2 % 3 - -j", "(n = (((i / 2) % 3) + --j))"},
		{"found = True -> A[i] = n", "((found <-> True) -> (A[i] = n))"},
		{"~found Or i != j", "(~found Or ~(i = j))"},
		{"!found && flags[i] || found", "((~found And flags[i]) Or found)"},
		{"found <-> i < j -> j > i", "(found <-> ((i < j) -> (i < j)))"},
		{"len(A) = |A'| And old(A)[0] = 1", "((|A| = |A1|) And (A0[0] = 1))"},
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
		{"rejects duplicate names", []string{"p(n) ::= n > 0", "p(n) ::= n < 0"}, "already defined"},
		{"rejects free names", []string{"p(n) ::= n > m"}, "may only mention their parameters"},
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
