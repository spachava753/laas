package vego

import (
	"errors"
	"fmt"
	"go/importer"
	"go/token"
	"go/types"
	"io/fs"
	"math/big"
	"math/rand"
	"os"
	"path/filepath"
	"reflect"
	"slices"
	"sort"
	"strconv"
	"strings"
	"syscall"
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
		big := strings.Repeat("9", 19+rng.Intn(3))
		s := []string{randomText(rng), strconv.Itoa(rng.Intn(100)), big, "-" + big, "+" + big}[rng.Intn(5)]
		n, err := strconv.Atoi(s)
		return sample{before: []any{s}, results: []any{n, err}}
	},
	"os.Remove": func(rng *rand.Rand) sample {
		// Only inside a directory of its own, made for each call: a file,
		// a missing name, a directory that is not empty, a path through a
		// file, and a name with a NUL byte in it.
		dir, err := os.MkdirTemp(scratch, "remove")
		if err != nil {
			panic(err)
		}
		file := filepath.Join(dir, "file")
		if err := os.WriteFile(file, nil, 0o600); err != nil {
			panic(err)
		}
		full := filepath.Join(dir, "full")
		if err := os.Mkdir(full, 0o700); err != nil {
			panic(err)
		}
		if err := os.WriteFile(filepath.Join(full, "inside"), nil, 0o600); err != nil {
			panic(err)
		}
		name := []string{file, filepath.Join(dir, "missing"), full, filepath.Join(file, "below"), filepath.Join(dir, "a\x00b")}[rng.Intn(5)]
		return sample{before: []any{name}, results: []any{os.Remove(name)}}
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

// scratch is the directory the harnesses that touch files work in, made
// afresh for each run of the test.
var scratch string

// shippedVariables are the error variables the shipped contracts may name,
// by key, with their values. A contract that names another fails the test
// until it is added here.
var shippedVariables = map[string]error{
	"strconv.ErrSyntax": strconv.ErrSyntax,
	"strconv.ErrRange":  strconv.ErrRange,
	"io/fs.ErrNotExist": fs.ErrNotExist,
}

// reviewedErrorTypes are the dynamic types that may occur in the tree of an
// error a shipped contract vouches for. Each was read against what vouches
// claims: its methods return, write nothing a caller can see, and call no
// method of their arguments; == on it is identity; and what errors.Is
// reports for it does not change. A type not listed fails the test until
// someone has read its methods and added it.
var reviewedErrorTypes = map[string]bool{
	"*strconv.NumError":   true,
	"*errors.errorString": true,
	"*fs.PathError":       true,
	"syscall.Errno":       true,
}

// grounder converts Go values to the terms that denote them. Each error that
// is not nil gets a constant of its own, which stands for that value.
type grounder struct {
	errs []error
}

// errorName begins the names of the constants that stand for errors.
const errorName = "error #"

func (g *grounder) error(t *logic.Term) error {
	switch {
	case t == logic.NilErr():
		return nil
	case strings.HasPrefix(t.Name, errorName):
		i, _ := strconv.Atoi(strings.TrimPrefix(t.Name, errorName))
		return g.errs[i]
	case strings.HasPrefix(t.Name, sentinelName):
		if value, ok := shippedVariables[strings.TrimPrefix(t.Name, sentinelName)]; ok {
			return value
		}
	}
	panic("no Go error for " + t.String() + "; add the variable to shippedVariables")
}

// groundTerm converts a Go value to the term that denotes it.
func (g *grounder) groundTerm(value any) *logic.Term {
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
			g.errs = append(g.errs, value)
			return logic.Const(fmt.Sprintf("%s%d", errorName, len(g.errs)-1), logic.Err)
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
	errors   *grounder
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
		if t.Args[0].Sort == logic.Err {
			return e.errors.error(t.Args[0]) == e.errors.error(t.Args[1])
		}
		return e.number(t.Args[0]).Cmp(e.number(t.Args[1])) == 0
	case logic.OpIs:
		return errors.Is(e.errors.error(t.Args[0]), e.errors.error(t.Args[1]))
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
		return e.errors.error(t.Args[0]) == nil
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
	scratch = t.TempDir()
	pv := &pkgVerifier{
		pass: &analysis.Pass{
			Fset:       token.NewFileSet(),
			Pkg:        types.NewPackage("shipped", "shipped"),
			TypesSizes: types.SizesFor("gc", "amd64"),
			// The error variables the contracts name hold their values in
			// the evaluation below, whatever kind of stable variable they
			// are; nothing in the build writes them.
			ImportPackageFact: func(pkg *types.Package, fact analysis.Fact) bool {
				published, ok := fact.(*sentinelsFact)
				if !ok {
					return false
				}
				published.Vars = map[string]sentinelInfo{}
				for key := range shippedVariables {
					if path, name := key[:strings.LastIndex(key, ".")], key[strings.LastIndex(key, ".")+1:]; path == pkg.Path() {
						published.Vars[name] = sentinelInfo{Kind: stableMade}
					}
				}
				return true
			},
			AllPackageFacts: func() []analysis.PackageFact { return nil },
		},
		res:          logic.NewResolver(),
		trusted:      map[*types.Func]*funcInfo{},
		trustSources: map[*trustFile]*token.File{},
		reported:     map[string]bool{},
		usage:        &Usage{},
		reliedKeys:   map[string]bool{},
	}
	imports := importer.ForCompiler(pv.pass.Fset, "source", nil)
	// A contract names the variables of a package by its path, which must
	// be in the build.
	var built []*types.Package
	for key := range shippedVariables {
		pkg, err := imports.Import(key[:strings.LastIndex(key, ".")])
		if err != nil {
			t.Fatalf("import %s: %v", key, err)
		}
		built = append(built, pkg)
	}
	pv.pass.Pkg.SetImports(built)
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
					env := &specEnv{
						v: &fnVerifier{pkgVerifier: pv, fn: fn}, fn: fn,
						given: map[*types.Var]*logic.Term{}, givenPost: map[*types.Var]*logic.Term{},
					}
					g := &grounder{}
					eval := &evaluator{bindings: map[string]*big.Int{}, errors: g}
					for i, param := range fn.params {
						env.given[param], env.givenPost[param] = g.groundTerm(call.before[i]), g.groundTerm(call.after[i])
						if text, ok := call.before[i].(string); ok {
							eval.bound = max(eval.bound, int64(len(text))+2)
						}
						if list, ok := call.before[i].([]int); ok {
							eval.bound = max(eval.bound, int64(len(list))+2)
						}
					}
					satisfied := true
					for _, c := range fn.requires {
						formula, err := pv.res.Formula(c.node, env)
						if err != nil {
							t.Fatalf("requires %q: %v", c.text, err)
						}
						satisfied = satisfied && eval.holds(formula)
					}
					if !satisfied {
						continue
					}
					checked++
					for i, result := range call.results {
						if fn.vouches[i] {
							checkVouched(t, result)
						}
						env.givenResults = append(env.givenResults, g.groundTerm(result))
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

// checkVouched checks an error that a shipped contract vouches for: every
// error in its tree has a dynamic type someone has read, and == on it is
// identity.
func checkVouched(t *testing.T, result any) {
	t.Helper()
	for err, _ := result.(error); err != nil; err = errors.Unwrap(err) {
		if _, several := err.(interface{ Unwrap() []error }); several {
			t.Fatalf("%v wraps several errors, which vouches does not cover", err)
		}
		name := reflect.TypeOf(err).String()
		if !reviewedErrorTypes[name] {
			t.Fatalf("the tree of %q holds a %s, which is not among the reviewed error types; read its methods against what vouches claims and add it", result, name)
		}
		if err != err { //nolint:staticcheck // == on the error must be identity
			t.Fatalf("%q is not equal to itself", err)
		}
	}
}

// TestRemoveOutcomes checks that the harness of os.Remove produces each
// outcome it is meant to, so that the errors checkVouched sees include
// every kind os.Remove returns here.
func TestRemoveOutcomes(t *testing.T) {
	scratch = t.TempDir()
	seen := map[string]bool{}
	rng := rand.New(rand.NewSource(1))
	for range 400 {
		err, _ := harnesses["os.Remove"](rng).results[0].(error)
		var errno syscall.Errno
		switch {
		case err == nil:
			seen["success"] = true
		case errors.As(err, &errno):
			seen[errno.Error()] = true
		}
	}
	for _, want := range []string{"success", syscall.ENOENT.Error(), syscall.ENOTEMPTY.Error(), syscall.ENOTDIR.Error(), syscall.EINVAL.Error()} {
		if !seen[want] {
			t.Errorf("no call of os.Remove ended with %s; got %v", want, seen)
		}
	}
}
