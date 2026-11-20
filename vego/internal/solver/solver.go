// Package solver discharges vego's proof obligations with Z3. A problem of
// the logic is written as SMT-LIB text and handed to a Z3 process of the
// pinned version; see encode.go for the translation.
//
// A goal is proved when Z3 shows that the hypotheses together with the
// negated goal have no model. Every other reply, including one that Z3
// cannot settle within the resource limit, leaves the goal unproved.
package solver

import (
	"fmt"
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
}

// Cost is what one problem took. Bytes is the length of its SMT-LIB text
// without the comments that name the terms of the logic, which carry
// numbers that depend on what the process did before; Effort is the
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
	Time   time.Duration
}

// Fault is panicked when Z3 fails in a way that is not an answer: it
// crashed, could not be started, or replied with something other than an
// answer. The problem it was given is saved in File.
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
	e, script := encode(facts, opts)
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
	a, cached, err := s.answer(script, names)
	result := Unknown
	switch {
	case err == errTimeout:
		result = Timeout
	case err == errMemory:
		result = OutOfMemory
	case err != nil:
		panic(&Fault{err, dump(script)})
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
		opts.Observe(Cost{Result: result, Bytes: len(script) - e.remarks, Effort: effort, Cached: cached, Time: a.took})
	}
	if result == Proved || err != nil {
		return result, nil
	}
	var values map[string]*logic.Term
	for name, text := range a.values {
		c := byName[name]
		if c == nil {
			panic(&Fault{fmt.Errorf("a value for %s, which was not asked for", name), dump(script)})
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
const tactic = "(then simplify propagate-values ctx-simplify simplify elim-uncnstr smt)"

// Script returns the SMT-LIB text of a satisfiability check of the facts,
// ending in its check-sat-using.
func Script(facts []*logic.Term, opts Options) string {
	_, script := encode(facts, opts)
	return script
}

func encode(facts []*logic.Term, opts Options) (*encoder, string) {
	effort := opts.Effort
	if effort == 0 {
		effort = DefaultEffort
	}
	if effort < 0 || effort > MaxEffort {
		fault("resource limit %d is outside what Z3 accepts", effort)
	}
	e := &encoder{
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
	return e, "(set-option :rlimit " + strconv.Itoa(effort) + ")\n" + e.out.String() + "(check-sat-using " + tactic + ")\n"
}
