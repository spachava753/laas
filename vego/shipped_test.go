package vego

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"go/importer"
	"go/token"
	"go/types"
	"io/fs"
	"maps"
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
	// calls holds, for each function parameter with a contract under calls,
	// the arguments of every call the function made of it, and answers, for
	// one that the contract applies, what it returns for each argument.
	calls   map[string][][]any
	answers map[string]func(int64) int64
}

// table returns a function that answers what a random table says, the
// same for the same argument, and the table as an answer to an
// application. Half the time the table is false and then true, or
// positive, then zero, then negative.
func table[R int | bool](rng *rand.Rand, calls map[string][][]any, name string) (func(int) R, func(int64) int64) {
	values := make([]int64, 12)
	monotone := rng.Intn(2) == 0
	for i := range values {
		values[i] = int64(rng.Intn(3) - 1)
	}
	if monotone {
		slices.Sort(values)
		slices.Reverse(values)
	}
	answer := func(i int64) int64 {
		if i < 0 || i >= int64(len(values)) {
			return 0
		}
		var zero R
		if _, isBool := any(zero).(bool); isBool && monotone {
			// False, then true: true where the sorted value is not positive.
			if values[i] <= 0 {
				return 1
			}
			return 0
		}
		if _, isBool := any(zero).(bool); isBool {
			return values[i] & 1
		}
		return values[i]
	}
	return func(i int) R {
		calls[name] = append(calls[name], []any{i})
		var result R
		switch r := any(&result).(type) {
		case *bool:
			*r = answer(int64(i)) != 0
		case *int:
			*r = int(answer(int64(i)))
		}
		return result
	}, answer
}

// fixedRunes returns a predicate on code points that answers what a random
// table says, the same for the same code point, as FieldsFunc assumes.
func fixedRunes(rng *rand.Rand, calls map[string][][]any) func(rune) bool {
	seed := rng.Int63()
	return func(r rune) bool {
		calls["f"] = append(calls["f"], []any{r})
		return rand.New(rand.NewSource(seed+int64(r))).Intn(2) == 0
	}
}

// recorder returns a function that answers at random and records the
// arguments of each call in calls under name.
func recorder[A, R any](rng *rand.Rand, calls map[string][][]any, name string, answer func(rng *rand.Rand, a A) R) func(A) R {
	return func(a A) R {
		calls[name] = append(calls[name], []any{a})
		return answer(rng, a)
	}
}

// randomBool answers true or false at random, whatever it is asked.
func randomBool[A any](rng *rand.Rand, _ A) bool { return rng.Intn(2) == 0 }

// runeHarness calls a function of package strings that is handed a
// predicate on code points, with one that answers at random.
func runeHarness[R any](call func(s string, f func(rune) bool) R) func(rng *rand.Rand) sample {
	return func(rng *rand.Rand) sample {
		s, calls := randomText(rng), map[string][][]any{}
		f := recorder(rng, calls, "f", randomBool[rune])
		return sample{before: []any{s, f}, results: []any{call(s, f)}, calls: calls}
	}
}

// bytesHarness calls a function of package bytes that is handed a
// predicate on code points, with one that answers at random and, at times,
// writes the slice the function is reading.
func bytesHarness[R any](call func(s []byte, f func(rune) bool) R) func(rng *rand.Rand) sample {
	return func(rng *rand.Rand) sample {
		s, calls := []byte(randomText(rng)), map[string][][]any{}
		before := slices.Clone(s)
		f := recorder(rng, calls, "f", func(rng *rand.Rand, r rune) bool {
			if len(s) > 0 && rng.Intn(4) == 0 {
				s[rng.Intn(len(s))] = "a\xff "[rng.Intn(3)]
			}
			return rng.Intn(2) == 0
		})
		result := call(s, f)
		return sample{before: []any{before, f}, after: []any{s, f}, results: []any{result}, calls: calls}
	}
}

// randomRune answers with what mapping may return: the code point it is
// given, one of another length, an invalid one, or a negative number.
func randomRune(rng *rand.Rand, r rune) rune {
	return []rune{r, 'é', '世', -1, 0x110000, 0xD800}[rng.Intn(6)]
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
	"sort.Search": func(rng *rand.Rand) sample {
		n, calls := rng.Intn(14)-2, map[string][][]any{}
		f, answers := table[bool](rng, calls, "f")
		return sample{before: []any{n, f}, results: []any{sort.Search(n, f)}, calls: calls, answers: map[string]func(int64) int64{"f": answers}}
	},
	"sort.Find": func(rng *rand.Rand) sample {
		n, calls := rng.Intn(14)-2, map[string][][]any{}
		cmp, answers := table[int](rng, calls, "cmp")
		i, found := sort.Find(n, cmp)
		return sample{before: []any{n, cmp}, results: []any{i, found}, calls: calls, answers: map[string]func(int64) int64{"cmp": answers}}
	},
	"strings.FieldsFunc": func(rng *rand.Rand) sample {
		s, calls := randomText(rng), map[string][][]any{}
		f := fixedRunes(rng, calls)
		return sample{before: []any{s, f}, results: []any{strings.FieldsFunc(s, f)}, calls: calls}
	},
	"bytes.FieldsFunc": func(rng *rand.Rand) sample {
		s, calls := []byte(randomText(rng)), map[string][][]any{}
		f := fixedRunes(rng, calls)
		return sample{before: []any{slices.Clone(s), f}, results: []any{bytes.FieldsFunc(s, f)}, calls: calls}
	},
	"strings.IndexFunc":     runeHarness(strings.IndexFunc),
	"strings.LastIndexFunc": runeHarness(strings.LastIndexFunc),
	"strings.ContainsFunc":  runeHarness(strings.ContainsFunc),
	"strings.TrimFunc":      runeHarness(strings.TrimFunc),
	"strings.TrimLeftFunc":  runeHarness(strings.TrimLeftFunc),
	"strings.TrimRightFunc": runeHarness(strings.TrimRightFunc),
	"strings.Map": func(rng *rand.Rand) sample {
		s, calls := randomText(rng), map[string][][]any{}
		mapping := recorder(rng, calls, "mapping", randomRune)
		return sample{before: []any{mapping, s}, results: []any{strings.Map(mapping, s)}, calls: calls}
	},
	"bytes.IndexFunc":     bytesHarness(bytes.IndexFunc),
	"bytes.LastIndexFunc": bytesHarness(bytes.LastIndexFunc),
	"bytes.ContainsFunc":  bytesHarness(bytes.ContainsFunc),
	"bytes.TrimFunc":      bytesHarness(bytes.TrimFunc),
	"bytes.TrimLeftFunc":  bytesHarness(bytes.TrimLeftFunc),
	"bytes.TrimRightFunc": bytesHarness(bytes.TrimRightFunc),
	"bytes.Map": func(rng *rand.Rand) sample {
		s, calls := []byte(randomText(rng)), map[string][][]any{}
		mapping := recorder(rng, calls, "mapping", randomRune)
		return sample{before: []any{mapping, slices.Clone(s)}, results: []any{bytes.Map(mapping, s)}, calls: calls}
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
	"strconv.ErrSyntax":        strconv.ErrSyntax,
	"strconv.ErrRange":         strconv.ErrRange,
	"io/fs.ErrNotExist":        fs.ErrNotExist,
	"context.Canceled":         context.Canceled,
	"context.DeadlineExceeded": context.DeadlineExceeded,
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
	// The type of context.DeadlineExceeded, an empty struct whose methods
	// Error, Timeout, and Temporary return constants.
	"context.deadlineExceededError": true,
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
	case int32:
		return logic.IntLit(int64(value))
	case []int:
		seq := logic.Fill(logic.IntLit(0), logic.IntLit(0))
		for _, element := range value {
			seq = logic.Push(seq, logic.IntLit(int64(element)))
		}
		return seq
	case []byte:
		seq := logic.Fill(logic.IntLit(0), logic.IntLit(0))
		for _, element := range value {
			seq = logic.Push(seq, logic.IntLit(int64(element)))
		}
		return seq
	case []string, [][]byte:
		// No shipped contract reads the fields of FieldsFunc yet; a
		// formula that did would fail on this constant, which the
		// evaluator cannot read.
		return logic.Const("unreadable", logic.IntSeq)
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
	// callbacks answers, by the name of the sequence that stands for a
	// function a contract applies, what the function returns.
	callbacks map[string]func(int64) int64
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
		if answer, ok := e.callbacks[t.Args[0].Name]; ok && t.Args[0].Op == logic.OpConst {
			return big.NewInt(answer(x(1).Int64()))
		}
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
	case logic.OpSelect:
		return e.number(t).Sign() != 0
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
			// No type of a shipped contract has an invariant.
			ImportObjectFact: func(types.Object, analysis.Fact) bool { return false },
		},
		res:          logic.NewResolver(),
		trusted:      map[*types.Func]*funcInfo{},
		trustSources: map[*trustFile]*token.File{},
		reported:     map[string]bool{},
		usage:        &Usage{},
		reliedKeys:   map[string]bool{},
		typeEntries:  map[string]*funcInfo{},
		// The types of the methods of sync are structs, whose invariants
		// are looked up.
		invariants: map[*types.TypeName]*invariantSet{},
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
				path, name, _ := splitFuncName(key)
				pkg, err := imports.Import(path)
				if err != nil {
					t.Fatalf("import %s: %v", path, err)
				}
				if fn := shippedTypeContract(pv, pkg, name); fn != nil {
					checkTypeContract(t, pv, key, fn)
					return
				}
				if strings.HasPrefix(key, "(*sync.") {
					checkLockEntry(t, pv, pkg, key)
					return
				}
				callee, ok := pkg.Scope().Lookup(name).(*types.Func)
				if !ok {
					t.Fatalf("package %s has no function %s", path, name)
				}
				harness, ok := harnesses[key]
				if !ok {
					t.Fatalf("no harness calls %s; add one to harnesses", key)
				}
				fn := pv.trustedContract(callee)
				for _, defect := range fn.defects {
					t.Errorf("contract cannot be used: %s", defect)
				}
				checkContract(t, pv, key, fn, harness, false)
			})
		}
	}
}

// checkContract runs a harness 400 times and checks every call whose
// arguments satisfy the requires of the contract fn: what the function
// called through calls was given, the vouched errors, and every ensures.
// With unchanged, the parameters that its modifies does not list must be
// as they were before the call.
func checkContract(t *testing.T, pv *pkgVerifier, key string, fn *funcInfo, harness func(*rand.Rand) sample, unchanged bool) {
	t.Helper()
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
		eval := &evaluator{bindings: map[string]*big.Int{}, errors: g, callbacks: map[string]func(int64) int64{}}
		// What a function the contract applies returns is what
		// the harness answers.
		env.applied = map[*types.Var]*logic.Term{}
		for _, param := range fn.params {
			if cb := fn.calls[param]; cb != nil && cb.applied {
				sort, _ := sortOf(cb.sig.Results().At(0).Type())
				name := "callback " + param.Name()
				env.applied[param] = logic.Const(name, logic.SeqOf(sort))
				eval.callbacks[name] = call.answers[param.Name()]
			}
		}
		for i, param := range fn.params {
			// A function is one reference, which no formula of an
			// entry reads.
			if _, isFunc := param.Type().Underlying().(*types.Signature); isFunc {
				env.given[param], env.givenPost[param] = logic.RefLit(1), logic.RefLit(1)
				continue
			}
			env.given[param], env.givenPost[param] = g.groundTerm(call.before[i]), g.groundTerm(call.after[i])
			if text, ok := call.before[i].(string); ok {
				eval.bound = max(eval.bound, int64(len(text))+2)
			}
			if list, ok := call.before[i].([]int); ok {
				eval.bound = max(eval.bound, int64(len(list))+2)
			}
			if list, ok := call.before[i].([]byte); ok {
				eval.bound = max(eval.bound, int64(len(list))+2)
			}
			// A quantifier over [0, n) needs the indices up to n.
			if number, ok := call.before[i].(int); ok {
				eval.bound = max(eval.bound, int64(number)+2)
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
		for i, param := range fn.params {
			listed := slices.ContainsFunc(fn.modifies, func(m *modTarget) bool { return m.name == param.Name() })
			if unchanged && !listed && !reflect.DeepEqual(call.before[i], call.after[i]) {
				t.Fatalf("%s changed %s, which its modifies does not list: %v became %v", key, param.Name(), call.before[i], call.after[i])
			}
		}
		// The function called what it was handed only with
		// arguments that the requires of calls allow.
		for _, param := range fn.params {
			cb := fn.calls[param]
			if cb == nil {
				continue
			}
			for _, args := range call.calls[param.Name()] {
				given := maps.Clone(env.given)
				for i, p := range cb.params {
					given[p] = g.groundTerm(args[i])
				}
				inner := &specEnv{v: env.v, fn: cb.fn, given: given, givenPost: map[*types.Var]*logic.Term{}}
				for _, c := range cb.requires {
					formula, err := pv.res.Formula(c.node, inner)
					if err != nil {
						t.Fatalf("calls requires %q: %v", c.text, err)
					}
					if !eval.holds(formula) {
						t.Fatalf("%s called %s with %v, for which the calls requires %q is false, in the call with arguments %v",
							key, param.Name(), args, c.text, call.before)
					}
				}
			}
		}
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
