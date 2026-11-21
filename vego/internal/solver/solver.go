// Package solver discharges vego's proof obligations with Z3. A problem of
// the logic is written as SMT-LIB text and handed to a Z3 process of the
// pinned version; see encode.go for the translation.
//
// A goal is proved when Z3 shows that the hypotheses together with the
// negated goal have no model. Every other reply, including one that Z3
// cannot settle within the resource limit, leaves the goal unproved.
package solver

import (
	"errors"
	"fmt"
	"sync/atomic"
	"math/big"
	"strconv"
	"strings"
	"time"

	"github.com/spachava753/laas/vego/internal/logic"
)

// Result is the outcome of a proof attempt or a satisfiability check.
type Result int

// Outcomes. For Prove, Proved means the goal follows and Refuted that Z3
// found a model of the hypotheses that falsifies it. For Check, Proved
// means the facts have no model and Refuted that Z3 found one. The other
// outcomes leave the question open: Z3 ran out of its resource limit, it
// gave up for another reason, it ran past the wall-clock limit, which
// unlike the resource limit depends on the machine, or it ran out of the
// memory a process may use.
//
// A model Z3 found is a model of the translation, which describes more
// states than Go has: a map whose count disagrees with its keys, a
// division by zero with a chosen value. Refuted is therefore never
// evidence that a Go state exists.
const (
	Unknown Result = iota
	Proved
	Refuted
	Exhausted
	Timeout
	OutOfMemory
)

func (r Result) String() string {
	return [...]string{"unknown", "proved", "refuted", "exhausted", "timed out", "out of memory"}[r]
}

// DefaultEffort is the resource limit of a problem when Options sets none.
// Z3 counts resources deterministically, so one Z3 binary gives a problem
// the same answer on every run, whatever the load of the machine.
const DefaultEffort = 4_000_000

// MaxEffort is the largest resource limit Z3 accepts.
const MaxEffort = 1<<32 - 1

// Options configures one problem.
type Options struct {
	// Preds holds the definitions of the predicates that may occur.
	Preds map[string]*logic.PredDef
	// Effort is Z3's resource limit for the problem. Zero selects
	// DefaultEffort.
	Effort int
	// Forall lists constants that Check quantifies universally around all
	// the facts: the facts then have a model when some values of the other
	// constants satisfy them for every value of these.
	Forall []*logic.Term
	// Observe, when set, is told what the problem cost.
	Observe func(Cost)
	// Speculative is set for a problem asked only so that its answer is in
	// the cache when the verification that needs it asks: such a problem
	// never delays another, and gets no answer when its process is needed
	// elsewhere; see acquire.
	Speculative bool
	// ModelFirst, when not zero, is the resource limit of a first attempt
	// at a satisfiability check without e-matching; see Model.
	ModelFirst int
	// withoutEMatching solves every problem without e-matching, as the
	// first attempt does, so that the tests can check Z3's proofs in that
	// setting; see Model.
	withoutEMatching bool
	// withoutExtensionality makes every problem be solved without the
	// axiom of extensionality, so that the tests can check Z3's proofs in
	// that setting on problems of every shape; see encode.
	withoutExtensionality bool
}

// Cost is what one problem took. Bytes is the length of the SMT-LIB text
// sent to Z3, which has no comments; see encode. Effort is the
// resources Z3 counted while solving it, which, like the
// answer, is the same on every run of one binary; it is -1 when the
// problem stopped at a limit that depends on the machine. A problem that
// was answered from the cache has Cached set, the Effort Z3 counted when it
// solved the same text, and no Time.
type Cost struct {
	Result Result
	Bytes  int
	Effort int64
	Cached bool
	// Stored is set when the answer was read from the cache on disk, by
	// this problem or by one with the same text before it in the process.
	Stored bool
	Time   time.Duration
}

// Fault is panicked when Z3 fails in a way that is not an answer: it
// crashed, could not be started, or replied with something other than an
// answer. The problem it was given is saved in File, with comments that
// name the terms of the logic, which the text sent to Z3 leaves out.
type Fault struct {
	Err  error
	File string
}

func (f *Fault) Error() string {
	return fmt.Sprintf("%v (the problem is saved in %s)", f.Err, f.File)
}

// Prove reports whether goal follows from the hypotheses.
func (s *Solver) Prove(hyps []*logic.Term, goal *logic.Term, opts Options) Result {
	return s.Check(append(hyps[:len(hyps):len(hyps)], logic.Not(goal)), opts)
}

// Check reports whether the facts have a model: Proved if they have none,
// Refuted if Z3 found one.
func (s *Solver) Check(facts []*logic.Term, opts Options) Result {
	result, _ := s.Model(facts, opts, nil)
	return result
}

// Model checks the facts as Check does and, unless they have no model,
// returns the values Z3 gave the constants asked for, as literals. Only
// integer, reference, and boolean constants have values; another
// constant, or one Z3 gave no value, is missing from the map. Z3 may
// offer values after an unknown outcome too. The values are a candidate
// for the caller to confirm by proof, never evidence by themselves.
func (s *Solver) Model(facts []*logic.Term, opts Options, consts []*logic.Term) (Result, map[string]*logic.Term) {
	// A satisfiability check whose ModelFirst is set is asked first without
	// e-matching, at that limit, and, when that answer is open, as any other
	// problem. Without e-matching, Z3 instantiates
	// quantified facts only through its model-based instantiation, which on
	// some problems builds a model at once where e-matching keeps making new
	// instances to the limit: the contradiction check of the shipped entry of
	// slices.Delete, whose facts quantify over a row written through a store,
	// is sat in 5,956 units that way and open at 4,000,754 units otherwise.
	//
	// Either answer of the attempt is used. An unsat is an unsat whatever the
	// search: e-matching only adds instances of the facts, so leaving it out
	// cannot make Z3 find a contradiction that the facts do not have. A sat
	// says that the facts have a model in the logic. This is not a model taken
	// as evidence that a Go state exists, which the verifier never does (see
	// Refuted): a satisfiability check asks only whether the facts of the logic
	// contradict each other, and sat says that they do not, as an open answer
	// says nothing more than that no contradiction was found. In Z3 5.4.1 the
	// option is read only by the e-matching plugin and by pattern inference; a
	// sat with quantifiers rests on the same check of the candidate model by
	// model-based instantiation either way. TestProveIsSound solves its random
	// problems in this setting too.
	if opts.ModelFirst > 0 && len(consts) == 0 {
		first := opts
		first.Effort, first.ModelFirst, first.withoutEMatching = min(opts.ModelFirst, effortOf(opts)), 0, true
		result, _ := s.Model(facts, first, nil)
		if (result == Refuted || result == Proved) && compareModelFirst.Load() {
			full := opts
			full.ModelFirst, full.Observe = 0, nil
			if again, _ := s.Model(facts, full, nil); again == Refuted && result == Proved || again == Proved && result == Refuted {
				_, script, remarked := encode(facts, first)
				panic(&Fault{fmt.Errorf("the first attempt at a satisfiability check answers %v and the check in full %v:\n%s", result, again, script), dump(remarked)})
			}
			compared.Add(1)
		}
		if result == Proved || result == Refuted {
			return result, nil
		}
	}
	e, script, remarked := encode(facts, opts)
	var names []string
	byName := map[string]*logic.Term{}
	for _, c := range consts {
		if c.Op != logic.OpConst || !(plain(c.Sort) == logic.Int || c.Sort == logic.Bool) {
			fault("asking for the value of %v", c)
		}
		if name, ok := e.consts[c.Name]; ok && byName[name] == nil {
			names = append(names, name)
			byName[name] = c
		}
	}
	a, cached, err := s.answer(script, names, opts.Speculative)
	result := Unknown
	switch {
	case err == errTimeout:
		result = Timeout
	case err == errMemory:
		result = OutOfMemory
	case err == errPreempted:
		result = Unknown
	case errors.As(err, new(*CacheError)):
		panic(err)
	case err != nil:
		panic(&Fault{err, dump(remarked)})
	case a.status == "unsat":
		result = Proved
	case a.status == "sat":
		result = Refuted
	case machineBound(a.reason):
		result = OutOfMemory
	case exhausted(a.reason):
		result = Exhausted
	}
	if opts.Observe != nil {
		effort := a.effort
		if err != nil || result == OutOfMemory {
			effort = -1
		}
		opts.Observe(Cost{Result: result, Bytes: len(script), Effort: effort, Cached: cached, Stored: a.stored, Time: a.took})
	}
	if result == Proved || err != nil {
		return result, nil
	}
	var values map[string]*logic.Term
	for name, text := range a.values {
		c := byName[name]
		if c == nil {
			panic(&Fault{fmt.Errorf("a value for %s, which was not asked for", name), dump(remarked)})
		}
		if values == nil {
			values = map[string]*logic.Term{}
		}
		values[c.Name] = literal(c.Sort, text)
	}
	return result, values
}

// literal turns a value Z3 printed into a term of the sort.
func literal(sort logic.Sort, text string) *logic.Term {
	switch {
	case sort == logic.Bool:
		return logic.BoolLit(text == "true")
	default:
		n, ok := new(big.Int).SetString(text, 10)
		if !ok {
			fault("value %q is not a number", text)
		}
		if sort == logic.Ref {
			if !n.IsInt64() {
				fault("reference %v does not fit 64 bits", n)
			}
			return logic.RefLit(n.Int64())
		}
		return logic.BigLit(n)
	}
}

// machineBound reports whether Z3 gave up for want of memory, a limit that
// depends on the machine and on what the process did before.
func machineBound(reason string) bool {
	return strings.Contains(reason, "memout") || strings.Contains(reason, "memory")
}

// exhausted reports whether Z3 gave up because a limit was reached.
func exhausted(reason string) bool {
	for _, word := range []string{"resource", "canceled"} {
		if strings.Contains(reason, word) {
			return true
		}
	}
	return false
}

// tactic is how every problem is solved: the simplifications Z3's default
// tactic applies to problems with quantifiers, then its core solver. The
// default tactic itself picks a tactic by the kind of problem, and for some
// kinds tries one solver for a fixed time before another, which would make
// the answer depend on the speed of the machine. This chain has no such
// step, so the resource limit alone bounds the work.
//
// The default tactic's ctx-simplify is left out. On the corpus it proved
// nothing that the chain without it does not, and it used the whole limit
// on goals that the core solver proves at once, such as what a field
// written through ten pointers that may be the same holds afterwards, and
// most of the count of late obligations of long functions; see
// TestManyWrites.
const tactic = "(then simplify propagate-values simplify elim-uncnstr smt)"

// tacticWithoutExtensionality is tactic with the core solver told not to
// use the axiom of extensionality, by which two arrays with the same
// elements are equal.
//
// This can never make a proof wrong, whatever problem it is used for.
// Without the axiom the theory is weaker, so a problem that has no model
// without it has none with it, and every unsat Z3 gives stands. Soundness
// does not rest on the rule below that picks the problems.
//
// The rule is there so that no proof is lost. The axiom is needed only to
// equate two arrays that something tells apart, and in a problem of the
// logic nothing does unless a function takes a sequence: the logic has no
// equality of sequences (the encoder refuses one), and every other symbol
// applied to a sequence (a read, a write, a fill, a cut, a concatenation, a
// condition, the constructor and the fields of the datatype, a quantifier)
// gives equal results for sequences with equal elements. In a model without
// the axiom, identifying the arrays with equal elements then gives a model
// with it, so such a problem has a model with the axiom exactly when it has
// one without it. A key function and a recursive predicate with a sequence
// parameter can tell sequences apart, so a problem with either keeps the
// axiom (tellsApart). That the two have the same models does not make Z3
// give the same answer: its procedure is incomplete with quantifiers, and
// without the axiom it may stop at a limit, or give up on the quantifiers
// at once, where with it the new indices of its axioms led to a
// contradiction. That was measured, not proved; see The prover in the
// ROADMAP.
//
// Which of the problems the rule allows leave the axiom out is a choice of
// search, made from measurements of the corpus, not a law. Where a region
// holds sequences (strings, slices of strings, or slices held as map
// values, inside structs or slices), Z3 kept adding axioms of
// extensionality between the rows of the region, each with a new index
// that matched the quantified facts of what the types guarantee of their
// contents, and ran to the limit on questions without a model: the call of
// a trusted function returning a *http.Response took 80 s, and without the
// axiom takes a second. Leaving it out of every problem the rule allows
// lost one proof of the corpus, and made 22 problems that Z3 answers sat
// quickly with it, since it uses it to finish a model, and 23 in all, run
// to a limit.
const tacticWithoutExtensionality = "(then simplify propagate-values simplify elim-uncnstr (using-params smt :array.extensional false))"

// compareModelFirst makes every first attempt at a satisfiability check
// that settles it be followed by the full check, which must not settle it
// the other way: Z3 would then have given one problem a model and a proof
// that it has none. compared counts the checks compared. A test that runs
// on request sets it, through CompareModelFirst.
var (
	compareModelFirst atomic.Bool
	compared          atomic.Int64
)

// CompareModelFirst turns on the comparison of compareModelFirst until the
// returned function is called, which says how many checks were compared.
// Only a test calls it.
func CompareModelFirst() func() int64 {
	compareModelFirst.Store(true)
	before := compared.Load()
	return func() int64 {
		compareModelFirst.Store(false)
		return compared.Load() - before
	}
}

// effortOf returns the resource limit of a problem.
func effortOf(opts Options) int {
	if opts.Effort == 0 {
		return DefaultEffort
	}
	return opts.Effort
}

// Script returns the SMT-LIB text of a satisfiability check of the facts,
// ending in its check-sat-using, as it is sent to Z3.
func Script(facts []*logic.Term, opts Options) string {
	_, script, _ := encode(facts, opts)
	return script
}

// encode writes a satisfiability check of the facts. It returns the text
// sent to Z3, which has no comments, and the same text with a comment that
// names the term of the logic after each declaration, which is what a fault
// saves for a person to read. The text sent is what an answer is kept by:
// the comments carry numbers that depend on what the process did before,
// so two texts that differ only in them would be asked twice.
func encode(facts []*logic.Term, opts Options) (e *encoder, script, remarked string) {
	effort := effortOf(opts)
	if effort < 0 || effort > MaxEffort {
		fault("resource limit %d is outside what Z3 accepts", effort)
	}
	e = &encoder{
		preds:      opts.Preds,
		sorts:      map[logic.Sort]string{},
		keyed:      map[logic.Sort]bool{},
		consts:     map[string]string{},
		constSorts: map[string]string{},
		defined:    map[string]string{},
		defining:   map[string]string{},
		uses:       map[*logic.Term]int{},
		shared:     map[*logic.Term]string{},
		ground:     map[*logic.Term]bool{},
	}
	for _, f := range facts {
		e.count(f)
	}
	if len(opts.Forall) == 0 {
		for _, f := range facts {
			e.assert(f)
		}
	} else {
		e.assertForall(opts.Forall, facts)
	}
	e.keyFacts()
	// A problem in which a region holds sequences, and in which no
	// function tells sequences apart, is solved without extensionality;
	// see tacticWithoutExtensionality.
	chain := tactic
	if opts.withoutExtensionality || (e.nested && !e.tellsApart) {
		chain = tacticWithoutExtensionality
	}
	if opts.withoutEMatching {
		chain = strings.Replace(chain, "(using-params smt ", "(using-params smt :ematching false ", 1)
		chain = strings.Replace(chain, " smt)", " (using-params smt :ematching false))", 1)
	}
	head, body, tail := "(set-option :rlimit "+strconv.Itoa(effort)+")\n", e.out.String(), "(check-sat-using "+chain+")\n"
	var plain strings.Builder
	plain.Grow(len(head) + len(body) + len(tail))
	plain.WriteString(head)
	last := 0
	for _, r := range e.remarks {
		plain.WriteString(body[last:r[0]])
		last = r[1]
	}
	plain.WriteString(body[last:])
	plain.WriteString(tail)
	return e, plain.String(), head + body + tail
}
