package vego

import (
	"slices"

	"github.com/spachava753/laas/vego/internal/logic"
	"github.com/spachava753/laas/vego/internal/solver"
)

// The verifier hands every question it cannot settle by reading the code to
// Z3, through the solver package. Z3 is started only when a package has
// something to prove, so a project without annotations does not need it.

// quickEffort bounds a proof whose failure is an ordinary outcome and
// decides nothing by itself, such as whether an append can happen in place.
const quickEffort = 200_000

// solverUnavailable is panicked when Z3 cannot be used at all. The run of
// the package then ends with the error instead of a report for every
// obligation.
type solverUnavailable struct{ err error }

// solver returns the solver for the package, starting it on first use.
func (pv *pkgVerifier) solver() *solver.Solver {
	if pv.z3 == nil {
		s, err := solver.Open(pv.z3Path, pv.cacheDir)
		if err != nil {
			panic(solverUnavailable{err})
		}
		pv.z3 = s
	}
	return pv.z3
}

// options returns the options of a problem with the given resource limit;
// zero selects the one the flags set. What the problem costs counts as a
// question of the given kind unless the caller set another; see asking.
func (pv *pkgVerifier) options(effort int, kind question) solver.Options {
	if pv.speculative && pv.stopSpeculation() {
		panic(stopped{})
	}
	if effort == 0 {
		effort = pv.effort
	}
	opts := solver.Options{Preds: pv.res.Preds, Effort: effort, Observe: pv.observe(kind), Speculative: pv.speculative, Stop: pv.speculationStop}
	// A contradiction check is asked first without e-matching; see
	// solver.Options.ModelFirst. Only a check that counts as one, as
	// observe counts it: a question of a search for an input reads an open
	// answer as a limit the search stopped at, which the report says. The
	// attempt has a tenth of the check's limit: at the full limit of a quick
	// check, a check whose attempt is open too would cost twice, which on
	// the corpus cost more time than the attempts saved.
	if pv.effectiveKind(kind) == contradictionCheck {
		opts.ModelFirst = min(modelFirstEffort, effort/10)
	}
	return opts
}

// modelFirstEffort is the largest resource limit of the first attempt at a
// contradiction check.
const modelFirstEffort = 200_000

// proves reports whether goal provably follows from the hypotheses.
func (pv *pkgVerifier) proves(hyps []*logic.Term, goal *logic.Term, effort int) bool {
	kind := obligation
	switch {
	case goal.Op == logic.OpFalse:
		kind = contradictionCheck
	case effort == quickEffort:
		kind = quickCheck
	}
	result := pv.solver().Prove(hyps, goal, pv.options(effort, kind))
	pv.noteLimit(result)
	return result == solver.Proved
}

// noteLimit records that a question of a search for an input stopped at a
// limit, for the report of what the search did not find; see searchLimit.
func (pv *pkgVerifier) noteLimit(result solver.Result) {
	if pv.searching > 0 && limitNote(result) != "" {
		pv.searchLimit = result
	}
}

// contradictory reports whether the facts provably have no model.
func (pv *pkgVerifier) contradictory(facts []*logic.Term) bool {
	return pv.solver().Check(facts, pv.options(0, contradictionCheck)) == solver.Proved
}

// quickly is prove with a small budget.
func (v *fnVerifier) quickly(st *state, guard []*logic.Term, goal *logic.Term) bool {
	return v.proves(append(slices.Clip(st.hyps), guard...), goal, quickEffort)
}

// attempt tries to prove a goal from the facts of a state together with the
// conditions under which the current expression is evaluated.
func (v *fnVerifier) attempt(st *state, guard []*logic.Term, goal *logic.Term) solver.Result {
	return v.solver().Prove(append(slices.Clip(st.hyps), guard...), goal, v.options(0, obligation))
}

// limitNote returns what a report of an obligation that was not proved adds
// when Z3 stopped at a limit. More effort may prove such an obligation,
// unlike one Z3 refuted or gave up on; saying which keeps an agent from
// raising the limit in vain or from adding facts that are not missing.
func limitNote(result solver.Result) string {
	switch result {
	case solver.Exhausted:
		return " (Z3 reached its resource limit; -vego.rlimit raises it)"
	case solver.Timeout:
		return " (Z3 ran past its time limit, which depends on the machine)"
	case solver.OutOfMemory:
		return " (Z3 ran out of memory)"
	}
	return ""
}

// prove reports whether a goal follows from the facts of a state together
// with the conditions under which the current expression is evaluated.
func (v *fnVerifier) prove(st *state, guard []*logic.Term, goal *logic.Term) bool {
	return v.proves(append(slices.Clip(st.hyps), guard...), goal, 0)
}
