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
// the line and the kind of question, the problems that stopped at a limit.
type fnCost struct {
	fn       *funcInfo
	problems int
	effort   int64
	bytes    int64
	elapsed  time.Duration
	limits   map[costLimit]int
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
		record.bytes += int64(c.Bytes)
		if c.Effort > 0 {
			record.effort += c.Effort
		}
		if limitNote(c.Result) != "" {
			record.limits[costLimit{at, kind}]++
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
	fset := pv.pass.Fset
	for _, c := range pv.costOrder {
		name := c.fn.obj.Name()
		if c.fn.trust != nil {
			name = "the trusted contract of " + c.fn.obj.FullName()
		} else if c.fn.methodOf != nil || c.fn.valueOf != nil {
			name = "the contract of " + c.fn.obj.FullName()
		}
		at := c.fn.obj.Pos()
		if c.fn.decl != nil {
			at = c.fn.decl.Name.Pos()
		}
		fmt.Fprintf(&out, "%s: vego cost of %s: %d problems, %d resource units, %d bytes, %.2f s\n",
			fset.Position(at), name, c.problems, c.effort, c.bytes, c.elapsed.Seconds())
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
	}
	costsMu.Lock()
	defer costsMu.Unlock()
	io.WriteString(w, out.String())
}

// costStderr is where -vego.cost prints.
var costStderr io.Writer = os.Stderr
