package vego

import (
	"fmt"
	"go/token"
	"io"
	"os"
	"slices"
	"strings"
	"sync"
	"time"

	"github.com/spachava753/laas/vego/internal/solver"
)

// What verifying a function costs is counted for every function, question
// by question, and printed with -vego.cost. The counts other than time are
// the same on every run of one Z3 binary: an answer read from the solver's
// cache counts with what Z3 counted when it solved the text. The test of
// the corpus compares them with the table in testdata/costs.txt.

// question says what a question to Z3 is for; see pkgVerifier.asking.
type question int

const (
	obligation question = iota
	failureCheck
	contradictionCheck
	modifiesCheck
	quickCheck
)

// questionNames holds the name of each kind of question, in the singular and the
// plural.
var questionNames = [...][2]string{
	{"proof obligation", "proof obligations"},
	{"question of the always-fails check", "questions of the always-fails check"},
	{"contradiction check", "contradiction checks"},
	{"check whether a Modifies entry is needed", "checks whether a Modifies entry is needed"},
	{"quick check", "quick checks"},
}

// fnCost is what verifying a function asked of Z3: the problems, the
// resources Z3 counted for them, and the bytes of their text; the wall
// time spent on the function, other functions it led to excluded; and, by
// the line and the kind of question, the problems that stopped at a limit;
// and the problems Z3 left open, at a limit or for another reason.
type fnCost struct {
	fn       *funcInfo
	problems int
	effort   int64
	bytes    int64
	elapsed  time.Duration
	limits   map[costLimit]int
	open     int
	// kinds counts the problems of each kind.
	kinds [len(questionNames)]int
	// stored counts the problems answered from the cache on disk.
	stored int
}

// costLimit is a place and kind of question that stopped at a limit.
type costLimit struct {
	pos  token.Pos
	kind question
}

// costOf returns the cost record of a function, made on first use.
func (pv *pkgVerifier) costOf(fn *funcInfo) *fnCost {
	if pv.costs == nil {
		pv.costs = map[*funcInfo]*fnCost{}
	}
	c := pv.costs[fn]
	if c == nil {
		c = &fnCost{fn: fn, limits: map[costLimit]int{}}
		pv.costs[fn] = c
		pv.costOrder = append(pv.costOrder, c)
	}
	return c
}

// costing makes fn the function that the questions asked until the
// returned function is called count against, at its declaration until a
// statement or an obligation says otherwise, and adds the time spent to
// it, less the time spent on other functions meanwhile.
func (pv *pkgVerifier) costing(fn *funcInfo) func() {
	saved, savedAt, savedNested := pv.costFn, pv.askAt, pv.nested
	pv.costFn, pv.nested = fn, 0
	if fn.decl != nil {
		pv.askAt = fn.decl.Name.Pos()
	} else if fn.obj != nil {
		pv.askAt = fn.obj.Pos()
	}
	began := time.Now()
	return func() {
		took := time.Since(began)
		pv.costOf(fn).elapsed += took - pv.nested
		pv.costFn, pv.askAt, pv.nested = saved, savedAt, savedNested+took
	}
}

// at makes pos the place the questions asked until the returned function is
// called come from.
func (pv *pkgVerifier) at(pos token.Pos) func() {
	saved := pv.askAt
	if pos.IsValid() {
		pv.askAt = pos
	}
	return func() { pv.askAt = saved }
}

// asking makes the questions asked until the returned function is called of
// the given kind, unless a narrower kind is set inside.
func (pv *pkgVerifier) asking(kind question) func() {
	saved, savedSet := pv.purpose, pv.purposeSet
	pv.purpose, pv.purposeSet = kind, true
	return func() { pv.purpose, pv.purposeSet = saved, savedSet }
}

// observe returns what a problem's cost is told to: it counts against the
// function being verified, at the place and of the kind set, or else of
// the kind given.
func (pv *pkgVerifier) observe(kind question) func(solver.Cost) {
	if pv.purposeSet {
		kind = pv.purpose
	}
	if pv.searching > 0 {
		kind = failureCheck
	}
	fn, at := pv.costFn, pv.askAt
	if fn == nil {
		// Every question is asked while some function is verified or
		// checked, so that the cost of each is counted against one.
		panic("vego: a question to Z3 was asked outside the verification of any function")
	}
	return func(c solver.Cost) {
		record := pv.costOf(fn)
		record.problems++
		record.kinds[kind]++
		record.bytes += int64(c.Bytes)
		if c.Stored {
			record.stored++
		}
		if c.Effort > 0 {
			record.effort += c.Effort
		}
		if limitNote(c.Result) != "" {
			record.limits[costLimit{at, kind}]++
		}
		if limitNote(c.Result) != "" || c.Result == solver.Unknown {
			record.open++
		}
	}
}

// costsMu keeps the costs of packages verified side by side apart.
var costsMu sync.Mutex

// printCosts writes the costs of the functions of the package, for
// -vego.cost: for each function in the order it was first asked about, a
// line with its totals, the name saying whether the contract is a trusted
// one or one of a type, and then a line for each place and kind of
// question that stopped at a limit, in the order of the source.
func (pv *pkgVerifier) printCosts(w io.Writer) {
	if len(pv.costOrder) == 0 {
		return
	}
	var out strings.Builder
	for _, c := range pv.costOrder {
		out.WriteString(costText(pv.pass.Fset, c))
	}
	costsMu.Lock()
	defer costsMu.Unlock()
	io.WriteString(w, out.String())
}

// costText returns what -vego.cost prints for one function: a line with
// what it asked, and a line for each place and kind of question that
// stopped at a limit.
func costText(fset *token.FileSet, c *fnCost) string {
	var out strings.Builder
	// A contract is named as the trust report and the other messages
	// name it.
	name := c.fn.obj.Name()
	switch {
	case c.fn.trust != nil:
		name = "the trusted contract of " + c.fn.trust.key
	case c.fn.methodOf != nil:
		name = "the contract of " + methodTitle(c.fn.methodOf)
	case c.fn.valueOf != nil:
		name = "the contract of " + c.fn.obj.Name()
	}
	at := c.fn.obj.Pos()
	if c.fn.decl != nil {
		at = c.fn.decl.Name.Pos()
	}
	problems := "problems"
	if c.problems == 1 {
		problems = "problem"
	}
	stored := ""
	if c.stored > 0 {
		stored = fmt.Sprintf(", %d answered from the answer cache on disk", c.stored)
	}
	fmt.Fprintf(&out, "%s: vego cost of %s: %d %s, %d resource units, %d bytes, %.2f s%s\n",
		fset.Position(at), name, c.problems, problems, c.effort, c.bytes, c.elapsed.Seconds(), stored)
	limits := slices.Collect(func(yield func(costLimit) bool) {
		for l := range c.limits {
			if !yield(l) {
				return
			}
		}
	})
	slices.SortFunc(limits, func(a, b costLimit) int {
		if a.pos != b.pos {
			return int(a.pos - b.pos)
		}
		return int(a.kind - b.kind)
	})
	for _, l := range limits {
		names := questionNames[l.kind]
		name := names[1]
		if c.limits[l] == 1 {
			name = names[0]
		}
		fmt.Fprintf(&out, "\t%s: %d %s stopped at a limit\n", fset.Position(l.pos), c.limits[l], name)
	}
	return out.String()
}

// noteStored says on w how many of the answers the package rests on came
// from the answer cache on disk, when any did, and records the directory in
// what the proofs rely on, so that a proof that rests on stored answers
// does not look like one that does not.
func (pv *pkgVerifier) noteStored(w io.Writer) {
	problems, stored := 0, 0
	for _, c := range pv.costOrder {
		problems += c.problems
		stored += c.stored
	}
	if stored == 0 {
		return
	}
	pv.usage.AnswerCaches = append(pv.usage.AnswerCaches, pv.z3.CacheDir())
	costsMu.Lock()
	defer costsMu.Unlock()
	fmt.Fprintf(w, "vego: %d of the %d answers of Z3 for %s came from the answer cache in %s\n",
		stored, problems, pv.pass.Pkg.Path(), pv.z3.CacheDir())
}

// costStderr is where -vego.cost prints, and where a package says how many
// of its answers came from the cache on disk.
var costStderr io.Writer = os.Stderr
