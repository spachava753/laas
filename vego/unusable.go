package vego

import (
	"fmt"
	"go/token"
	"go/types"
	"path/filepath"
	"slices"

	"github.com/spachava753/laas/vego/internal/logic"
)

// A contract that cannot be read, in whole or in part, is reported where it
// is used, in the declaration whose verification uses it, so that this
// declaration fails there and its own faults are still reported: a call of
// a function whose Ensures cannot be read does not hide what is wrong in
// the caller. What follows the use depends on what can be read.
//
//   - A function of this package whose every Requires and Modifies clause
//     can be read is called with the clauses that can be read: an Ensures
//     that cannot be read is not assumed.
//   - One whose Modifies can be read but a Requires cannot is called with
//     no Requires and no Ensures, so that nothing is assumed of an outcome
//     whose precondition was not checked: what Modifies lists is forgotten
//     and nothing more is known.
//   - Any other contract that cannot be used ends the path at the use, as
//     a panic would: nothing after it is checked on that path.
//
// The declaration has failed at the report in each case, so nothing it
// proves afterwards is accepted; the rest of its reports are what the reader
// would otherwise see only once the contract is fixed.

// contractView is what a use of a contract may rely on: the contract
// itself, the problems to report where it is used, and whether the path
// ends at the use.
type contractView struct {
	// of is the contract as written, and fn what a use relies on.
	of, fn   *funcInfo
	problems []string
	cut      bool
	// partial is set for a contract of a type or an interface method of
	// which only a call may use the clauses that can be read.
	partial bool
}

// unreadClause is a clause of a contract that cannot be resolved, with why.
type unreadClause struct {
	clause *clause
	err    error
}

// viewOf returns what a use of a contract may rely on. A contract without
// problems is used as it is.
func (pv *pkgVerifier) viewOf(fn *funcInfo) *contractView {
	if view, done := pv.views[fn]; done {
		return view
	}
	view := &contractView{of: fn, fn: fn}
	if pv.views == nil {
		pv.views = map[*funcInfo]*contractView{}
	}
	pv.views[fn] = view
	if (fn.valueOf != nil || fn.methodOf != nil) && signatureHoldsArray(fn.obj.Type().(*types.Signature)) {
		// Every call and every value of such a type would pass arrays
		// through code no verified caller sees, which is not built.
		view.problems = []string{"its signature takes or returns an array, and function types and methods of interfaces whose signatures hold arrays are not supported yet"}
		view.cut = true
		view.fn = blank(fn)
		return view
	}
	own := fn.decl != nil && fn.trust == nil && fn.imported == nil && fn.valueOf == nil && fn.methodOf == nil && fn.annotated()
	switch {
	case own && fn.broken:
		view.problems = []string{fmt.Sprintf("some annotations of %s could not be read, as reported at them", fn.obj.Name())}
		view.cut = true
		view.fn = blank(fn)
	case own:
		unread := pv.unreadClauses(fn)
		if len(unread) == 0 {
			return view
		}
		skipped := map[*clause]bool{}
		requires, modifies := true, true
		for _, u := range unread {
			skipped[u.clause] = true
			switch u.clause.kind {
			case "Requires":
				requires = false
			case "Modifies":
				modifies = false
			}
		}
		consequence := "so this call is verified without it"
		switch {
		case !modifies:
			consequence = "so nothing after this call is verified on this path"
			view.cut = true
		case !requires:
			consequence = "so this call is verified with none of its Requires and Ensures: what its Modifies lists is forgotten and nothing more is known after it"
		}
		for _, u := range unread {
			at := pv.pass.Fset.Position(u.clause.pos)
			view.problems = append(view.problems, fmt.Sprintf("its %s annotation at %s:%d:%d cannot be read (%v), %s",
				u.clause.kind, filepath.Base(at.Filename), at.Line, at.Column, u.err, consequence))
		}
		if view.cut {
			view.fn = blank(fn)
			return view
		}
		usable := *fn
		usable.requires, usable.ensures = nil, nil
		if requires {
			usable.requires = fn.requires
			for _, c := range fn.ensures {
				if !skipped[c] {
					usable.ensures = append(usable.ensures, c)
				}
			}
		}
		if usable.measure != nil && skipped[usable.measure] {
			usable.measure = nil
		}
		view.fn = &usable
	case fn.broken && fn.trust == nil && fn.imported == nil && len(fn.defects) == 0 && !fn.faulted && pv.declaredHere(fn):
		// The contract of a type or of a method of an interface in source
		// that was refused only for clauses that cannot be read. Its other
		// clauses were never checked, satisfiable or free of contradiction,
		// so nothing it ensures is assumed; a call checks what it requires
		// and forgets what it modifies. A check of a value against it is
		// not made at all.
		unread := pv.unreadClauses(fn)
		modifies := !slices.ContainsFunc(unread, func(u unreadClause) bool { return u.clause.kind == "Modifies" })
		consequence := "so this call is verified with none of its Ensures: what its Modifies lists is forgotten and nothing more is known after it"
		if !modifies || len(unread) == 0 {
			consequence = "so nothing after this use is verified on this path"
			view.cut = true
		}
		for _, u := range unread {
			at := pv.pass.Fset.Position(u.clause.pos)
			view.problems = append(view.problems, fmt.Sprintf("its %s annotation at %s:%d:%d cannot be read (%v), %s",
				u.clause.kind, filepath.Base(at.Filename), at.Line, at.Column, u.err, consequence))
		}
		if len(unread) == 0 {
			view.problems = []string{"it was refused where it is declared, as reported there, " + consequence}
		}
		if view.cut {
			view.fn = blank(fn)
			return view
		}
		usable := *fn
		usable.ensures, usable.broken = nil, false
		usable.requires = slices.DeleteFunc(slices.Clone(fn.requires), func(c *clause) bool {
			return slices.ContainsFunc(unread, func(u unreadClause) bool { return u.clause == c })
		})
		view.fn, view.partial = &usable, true
	case fn.broken:
		view.problems = fn.defects
		if len(view.problems) == 0 {
			view.problems = []string{"it was refused where it is declared, as reported there"}
		}
		view.cut = true
		view.fn = blank(fn)
	}
	return view
}

// signatureHoldsArray reports whether a parameter or a result of a
// signature holds an array by value.
func signatureHoldsArray(sig *types.Signature) bool {
	for _, tuple := range []*types.Tuple{sig.Params(), sig.Results()} {
		for variable := range tuple.Variables() {
			if holdsArrayValue(variable.Type()) {
				return true
			}
		}
	}
	return false
}

// declaredHere reports whether a contract is that of a function type or of
// a method of an interface declared in this package, in source.
func (pv *pkgVerifier) declaredHere(fn *funcInfo) bool {
	switch {
	case fn.valueOf != nil:
		return fn.valueOf.Pkg() == pv.pass.Pkg
	case fn.methodOf != nil:
		return fn.methodOf.Pkg() == pv.pass.Pkg
	}
	return false
}

// blank returns a contract of the same signature that requires, promises,
// and writes nothing, for a use after which the path has ended.
func blank(fn *funcInfo) *funcInfo {
	empty := newFuncInfo(fn.obj)
	empty.decl, empty.receiver, empty.valueOf, empty.methodOf = fn.decl, fn.receiver, fn.valueOf, fn.methodOf
	return empty
}

// unreadClauses resolves each clause of a contract of this package on its
// own, in the state on entry, and returns those that cannot be resolved.
func (pv *pkgVerifier) unreadClauses(fn *funcInfo) []unreadClause {
	var unread []unreadClause
	v := pv.newVerifier(fn)
	v.lenient = true
	v.misreadAs = func(c *clause, err error) { unread = append(unread, unreadClause{c, err}) }
	attempt := func(resolve func()) bool {
		ok := true
		func() {
			defer func() {
				switch r := recover().(type) {
				case nil:
				case abort, unsupported:
					ok = false
				default:
					panic(r)
				}
			}()
			resolve()
		}()
		return ok
	}
	// The state on entry, without the clauses, which are resolved one by
	// one below.
	requires, modifies := fn.requires, fn.modifies
	fn.requires, fn.modifies = nil, nil
	var st *state
	entered := attempt(func() { st = v.enter() })
	fn.requires, fn.modifies = requires, modifies
	if !entered {
		return nil
	}
	pre := &specEnv{v: v, sink: st, fn: fn, args: v.entry, now: memory{}}
	for _, c := range fn.requires {
		attempt(func() { v.formula(c, c.node, pre) })
	}
	if fn.measure != nil {
		c := fn.measure
		attempt(func() {
			if _, left := v.readKeysLeft(c, pre); !left {
				v.intTerm(c, pre)
			}
		})
	}
	for _, m := range fn.modifies {
		if _, _, err := v.locateTarget(fn, m, v.entry, st, memory{}); err != nil {
			unread = append(unread, unreadClause{m.clause, err})
		}
	}
	results := make([]value, len(fn.results))
	for i, result := range fn.results {
		if _, ok := layoutOf(result.Type()); ok {
			results[i] = v.unknown("out", result.Type(), st)
		}
	}
	post := &specEnv{v: v, sink: st, fn: fn, args: v.entry, outs: v.unknownOuts(fn, st), results: results, now: memory{}, post: st.mem, before: st.brk}
	for _, c := range fn.ensures {
		attempt(func() { v.calleeFormula(c, post) })
	}
	return unread
}

// reportUnusable reports, at the place of a use, what in a contract cannot
// be used there, naming the contract as title says.
func (v *fnVerifier) reportUnusable(pos token.Pos, view *contractView, title string) {
	fn := view.of
	for _, problem := range view.problems {
		if entry := fn.trust; entry != nil && entry.file != nil {
			if at := v.pkgVerifier.typeArgsNamed(fn.obj); at != "" {
				v.report(pos, "the trusted contract of %s (%s:%d) cannot be used with %s: %s%s", entry.key, filepath.Base(entry.file.path), entry.line,
					at, problem, v.pkgVerifier.insteadOf(fn, entry, problem))
				continue
			}
			v.report(pos, "the trusted contract of %s (%s:%d) cannot be used: %s", entry.key, filepath.Base(entry.file.path), entry.line, problem)
			continue
		}
		v.report(pos, "the contract of %s cannot be used: %s", title, problem)
	}
}

// cut ends the path at a use whose contract cannot be relied on: under the
// guard of the use, nothing more holds.
func (v *fnVerifier) cut(st *state, guard []*logic.Term) {
	st.assume(logic.Not(logic.And(guard...)))
}
