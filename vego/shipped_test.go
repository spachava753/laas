package vego

import (
	"errors"
	"fmt"
	"go/importer"
	"go/token"
	"go/types"
	"math/big"
	"math/rand"
	"slices"
	"sort"
	"strconv"
	"strings"
	"testing"
	"unicode/utf8"

	"github.com/spachava753/laas/vego/internal/logic"
	"golang.org/x/tools/go/analysis"
)

// sample is one call of a function with a shipped contract: the arguments
// before the call, the same arguments after it, and the results.
type sample struct {
	before  []any
	after   []any
	results []any
}

// harnesses call each function that vego ships a contract for on random
// arguments. A shipped contract without a harness fails the test, so a new
// contract cannot be added without being exercised against the real function.
var harnesses = map[string]func(rng *rand.Rand) sample{
	"sort.Ints": func(rng *rand.Rand) sample {
		x := randomInts(rng)
		before := slices.Clone(x)
		sort.Ints(x)
		return sample{before: []any{before}, after: []any{x}}
	},
	"sort.IntsAreSorted": func(rng *rand.Rand) sample {
		x := randomInts(rng)
		if rng.Intn(2) == 0 {
			sort.Ints(x)
		}
		return sample{before: []any{x}, results: []any{sort.IntsAreSorted(x)}}
	},
	"sort.SearchInts": func(rng *rand.Rand) sample {
		a, x := randomInts(rng), rng.Intn(9)-4
		sort.Ints(a)
		return sample{before: []any{a, x}, results: []any{sort.SearchInts(a, x)}}
	},
	"math/rand.Intn": func(rng *rand.Rand) sample {
		n := rng.Intn(50) + 1
		return sample{before: []any{n}, results: []any{rand.Intn(n)}}
	},
	"math/rand.Int": func(*rand.Rand) sample {
		return sample{results: []any{rand.Int()}}
	},
	"strings.Contains": func(rng *rand.Rand) sample {
		s, substr := randomText(rng), randomText(rng)
		return sample{before: []any{s, substr}, results: []any{strings.Contains(s, substr)}}
	},
	"strings.HasPrefix": func(rng *rand.Rand) sample {
		s := randomText(rng)
		prefix := []string{randomText(rng), s[:rng.Intn(len(s)+1)]}[rng.Intn(2)]
		return sample{before: []any{s, prefix}, results: []any{strings.HasPrefix(s, prefix)}}
	},
	"strings.HasSuffix": func(rng *rand.Rand) sample {
		s := randomText(rng)
		suffix := []string{randomText(rng), s[rng.Intn(len(s)+1):]}[rng.Intn(2)]
		return sample{before: []any{s, suffix}, results: []any{strings.HasSuffix(s, suffix)}}
	},
	"strings.Index": func(rng *rand.Rand) sample {
		s, substr := randomText(rng), randomText(rng)
		if rng.Intn(2) == 0 && len(s) > 0 {
			start := rng.Intn(len(s))
			substr = s[start : start+rng.Intn(len(s)-start+1)]
		}
		return sample{before: []any{s, substr}, results: []any{strings.Index(s, substr)}}
	},
	"strings.TrimSpace": func(rng *rand.Rand) sample {
		s := randomText(rng)
		return sample{before: []any{s}, results: []any{strings.TrimSpace(s)}}
	},
	"strings.Repeat": func(rng *rand.Rand) sample {
		s, count := randomText(rng), rng.Intn(4)
		return sample{before: []any{s, count}, results: []any{strings.Repeat(s, count)}}
	},
	"strings.ToUpper": func(rng *rand.Rand) sample {
		s := randomText(rng)
		return sample{before: []any{s}, results: []any{strings.ToUpper(s)}}
	},
	"strings.ToLower": func(rng *rand.Rand) sample {
		s := randomText(rng)
		return sample{before: []any{s}, results: []any{strings.ToLower(s)}}
	},
	"strconv.Itoa": func(rng *rand.Rand) sample {
		i := rng.Intn(2001) - 1000
		return sample{before: []any{i}, results: []any{strconv.Itoa(i)}}
	},
	"strconv.Atoi": func(rng *rand.Rand) sample {
		s := []string{randomText(rng), strconv.Itoa(rng.Intn(100))}[rng.Intn(2)]
		n, err := strconv.Atoi(s)
		return sample{before: []any{s}, results: []any{n, err}}
	},
	"errors.Is": func(rng *rand.Rand) sample {
		target := errors.New("target")
		err := []error{nil, target, fmt.Errorf("wrapped: %w", target)}[rng.Intn(3)]
		return sample{before: []any{err, target}, results: []any{errors.Is(err, target)}}
	},
	"errors.Unwrap": func(rng *rand.Rand) sample {
		inner := errors.New("inner")
		err := []error{nil, inner, fmt.Errorf("wrapped: %w", inner)}[rng.Intn(3)]
		return sample{before: []any{err}, results: []any{errors.Unwrap(err)}}
	},
	"unicode/utf8.RuneCountInString": func(rng *rand.Rand) sample {
		s := randomText(rng)
		return sample{before: []any{s}, results: []any{utf8.RuneCountInString(s)}}
	},
}

func randomInts(rng *rand.Rand) []int {
	values := make([]int, rng.Intn(6))
	for i := range values {
		values[i] = rng.Intn(9) - 4
	}
	return values
}

// randomText returns a short string that may contain spaces, upper and lower
// case letters, multi-byte characters, and invalid UTF-8.
func randomText(rng *rand.Rand) string {
	pieces := []string{"a", "B", " ", "ab", "é", "ß", "\xff", "\t", "世"}
	var text strings.Builder
	for range rng.Intn(5) {
		text.WriteString(pieces[rng.Intn(len(pieces))])
	}
	return text.String()
}

// groundTerm converts a Go value to the term that denotes it.
func groundTerm(value any) *logic.Term {
	switch value := value.(type) {
	case int:
		return logic.IntLit(int64(value))
	case bool:
		return logic.BoolLit(value)
	case string:
		return logic.Bytes(value)
	case []int:
		seq := logic.Fill(logic.IntLit(0), logic.IntLit(0))
		for _, element := range value {
			seq = logic.Push(seq, logic.IntLit(int64(element)))
		}
		return seq
	case error:
		if value != nil {
			return logic.Const("some error", logic.Err)
		}
	case nil:
	default:
		panic(fmt.Sprintf("no term for %T", value))
	}
	return logic.NilErr()
}

// evaluator computes the value of ground terms. Quantifiers range over the
// indices from -2 to bound, which covers every sequence in the samples.
type evaluator struct {
	bound    int64
	bindings map[string]*big.Int
}

func (e *evaluator) number(t *logic.Term) *big.Int {
	x := func(i int) *big.Int { return e.number(t.Args[i]) }
	switch t.Op {
	case logic.OpIntLit:
		return t.Value()
	case logic.OpBound:
		return e.bindings[t.Name]
	case logic.OpAdd:
		return new(big.Int).Add(x(0), x(1))
	case logic.OpMul:
		return new(big.Int).Mul(x(0), x(1))
	case logic.OpNeg:
		return new(big.Int).Neg(x(0))
	case logic.OpLen:
		return big.NewInt(int64(len(e.sequence(t.Args[0]))))
	case logic.OpSelect:
		elements, index := e.sequence(t.Args[0]), x(1)
		if index.Sign() < 0 || index.Cmp(big.NewInt(int64(len(elements)))) >= 0 {
			// Outside the sequence the logic leaves the value open; any
			// fixed choice is a model.
			return big.NewInt(-99)
		}
		return elements[index.Int64()]
	}
	panic("cannot evaluate number " + t.String())
}

func (e *evaluator) sequence(t *logic.Term) []*big.Int {
	switch t.Op {
	case logic.OpFill:
		return slices.Repeat([]*big.Int{e.number(t.Args[1])}, int(e.number(t.Args[0]).Int64()))
	case logic.OpPush:
		return append(slices.Clone(e.sequence(t.Args[0])), e.number(t.Args[1]))
	}
	panic("cannot evaluate sequence " + t.String())
}

func (e *evaluator) holds(t *logic.Term) bool {
	x := func(i int) bool { return e.holds(t.Args[i]) }
	switch t.Op {
	case logic.OpTrue, logic.OpFalse:
		return t.Op == logic.OpTrue
	case logic.OpEq:
		return e.number(t.Args[0]).Cmp(e.number(t.Args[1])) == 0
	case logic.OpLe:
		return e.number(t.Args[0]).Cmp(e.number(t.Args[1])) <= 0
	case logic.OpLt:
		return e.number(t.Args[0]).Cmp(e.number(t.Args[1])) < 0
	case logic.OpNot:
		return !x(0)
	case logic.OpImplies:
		return !x(0) || x(1)
	case logic.OpIff:
		return x(0) == x(1)
	case logic.OpAnd:
		return !slices.ContainsFunc(t.Args, func(arg *logic.Term) bool { return !e.holds(arg) })
	case logic.OpOr:
		return slices.ContainsFunc(t.Args, e.holds)
	case logic.OpIsNil:
		return t.Args[0] == logic.NilErr()
	case logic.OpForall, logic.OpExists:
		for index := int64(-2); index <= e.bound; index++ {
			e.bindings[t.Args[0].Name] = big.NewInt(index)
			if e.holds(t.Args[1]) == (t.Op == logic.OpExists) {
				return t.Op == logic.OpExists
			}
		}
		return t.Op == logic.OpForall
	}
	panic("cannot evaluate formula " + t.String())
}

// TestShippedContracts runs every contract shipped with vego against the
// function it describes. For each random call whose arguments satisfy the
// contract's requires, every ensures must be true of what the function did.
// This does not prove a contract, but a wrong one is caught before it ships.
func TestShippedContracts(t *testing.T) {
	pv := &pkgVerifier{
		pass: &analysis.Pass{
			Fset:       token.NewFileSet(),
			Pkg:        types.NewPackage("shipped", "shipped"),
			TypesSizes: types.SizesFor("gc", "amd64"),
		},
		res:          logic.NewResolver(),
		trusted:      map[*types.Func]*funcInfo{},
		trustSources: map[*trustFile]*token.File{},
		reported:     map[string]bool{},
		usage:        &Usage{Entries: map[string]*EntryUse{}},
	}
	imports := importer.ForCompiler(pv.pass.Fset, "source", nil)
	for _, file := range shippedContracts() {
		for _, problem := range file.problems {
			t.Errorf("%s:%d: %s", file.path, problem.line, problem.msg)
		}
		for key := range file.entries {
			t.Run(key, func(t *testing.T) {
				harness, ok := harnesses[key]
				if !ok {
					t.Fatalf("no harness calls %s; add one to harnesses", key)
				}
				path, name, _ := splitFuncName(key)
				pkg, err := imports.Import(path)
				if err != nil {
					t.Fatalf("import %s: %v", path, err)
				}
				callee, ok := pkg.Scope().Lookup(name).(*types.Func)
				if !ok {
					t.Fatalf("package %s has no function %s", path, name)
				}
				fn := pv.trustedContract(callee)
				for _, defect := range fn.defects {
					t.Errorf("contract cannot be used: %s", defect)
				}
				rng := rand.New(rand.NewSource(1))
				checked := 0
				for range 400 {
					call := harness(rng)
					if call.after == nil {
						call.after = call.before
					}
					env := &contractEnv{pv: pv, fn: fn, args: map[*types.Var]*logic.Term{}, post: map[*types.Var]*logic.Term{}}
					eval := &evaluator{bindings: map[string]*big.Int{}}
					for i, param := range fn.params {
						env.args[param], env.post[param] = groundTerm(call.before[i]), groundTerm(call.after[i])
						if text, ok := call.before[i].(string); ok {
							eval.bound = max(eval.bound, int64(len(text))+2)
						}
						if list, ok := call.before[i].([]int); ok {
							eval.bound = max(eval.bound, int64(len(list))+2)
						}
					}
					satisfied := true
					for _, c := range fn.requires {
						formula, err := pv.res.Formula(c.node, &contractEnv{pv: pv, fn: fn, args: env.args})
						if err != nil {
							t.Fatalf("requires %q: %v", c.text, err)
						}
						satisfied = satisfied && eval.holds(formula)
					}
					if !satisfied {
						continue
					}
					checked++
					for _, result := range call.results {
						env.results = append(env.results, groundTerm(result))
						if text, ok := result.(string); ok {
							eval.bound = max(eval.bound, int64(len(text))+2)
						}
					}
					for _, c := range fn.ensures {
						formula, err := pv.res.Formula(c.node, env)
						if err != nil {
							t.Fatalf("ensures %q: %v", c.text, err)
						}
						if !eval.holds(formula) {
							t.Fatalf("ensures %q is false for the call with arguments %v, which left them as %v and returned %v",
								c.text, call.before, call.after, call.results)
						}
					}
				}
				if checked < 100 {
					t.Fatalf("only %d of 400 random calls satisfied the requires; the harness does not exercise the contract", checked)
				}
			})
		}
	}
}
