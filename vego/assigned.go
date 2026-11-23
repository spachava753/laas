package vego

import (
	"errors"
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"slices"
	"strings"

	"github.com/spachava753/laas/vego/internal/logic"
)

// Assigned package-level variables (part 2 of package-level variables).
//
// A variable of this package that the build changes only by assigning it,
// or a part of it reached through struct fields, is kind 2: its storage
// lies in regions of its own, one for each leaf, keyed varRegion, its key,
// and the leaf's path, at a constant reference that existed on entry (V1
// in the ROADMAP). No pointer refers to that storage, so nothing aliases
// it, and no footprint row holds a cell of it: a write through an interface
// value keeps it (see inEpoch). Reads are recorded reads of memory, so the
// order rule, the versions of a unit, joins, the layers of loops, and the
// havocs of calls work on it as on any memory.

// changeKind says how the build changes a package-level variable.
type changeKind uint8

const (
	changeAssigned changeKind = 1 << iota
	changeAddress
	changeLinked
	// changedOutsideInit is set when some change stands outside the body
	// of an init function of the variable's own package, or inside a
	// function literal or a go statement there, which may run later.
	changedOutsideInit
)

// kindOfChange reads the kind from what findChanges says of a change.
func kindOfChange(what string) changeKind {
	switch {
	case strings.HasPrefix(what, "is assigned"):
		return changeAssigned
	case strings.HasPrefix(what, "has its address taken"):
		return changeAddress
	default:
		return changeLinked
	}
}

// inInitBody reports whether the use at the end of stack lies in the body
// of a function init of the package itself, outside every function literal
// and go statement, so that it runs while the package is initialised.
func inInitBody(stack []ast.Node) bool {
	for i := len(stack) - 1; i >= 0; i-- {
		switch n := stack[i].(type) {
		case *ast.FuncLit, *ast.GoStmt:
			return false
		case *ast.FuncDecl:
			return n.Recv == nil && n.Name.Name == "init"
		}
	}
	return false
}

// varRegion begins the key of a region that holds a leaf of the storage of
// an assigned package-level variable.
const varRegion = "var "

// isVarRegion reports whether a region holds the storage of an assigned
// package-level variable.
func isVarRegion(key string) bool {
	return strings.HasPrefix(key, varRegion)
}

// assignedWhy reports why a variable of this package that the build
// changes is not an assigned variable that a verified function can read and
// write, or "" when it is one.
func (pv *pkgVerifier) assignedWhy(variable *types.Var) string {
	kinds := pv.changeKinds[variable]
	spelled := pv.spelling(variable)
	t := variable.Type()
	switch {
	case kinds&changeLinked != 0:
		return fmt.Sprintf("%s %s; a variable that a directive or assembly names is another symbol's storage, which code writes under the other name, "+
			"so it cannot be verified", spelled, pv.changeOf[variable])
	case kinds&changeAddress != 0:
		return fmt.Sprintf("%s %s; package-level variables whose address is taken are not supported yet", spelled, pv.ownChanges[variable])
	case isError(t):
		return fmt.Sprintf("%s %s; package-level error variables that are changed are not supported yet", spelled, pv.ownChanges[variable])
	}
	if _, ok := layoutOf(t); !ok {
		return fmt.Sprintf("%s has type %s, which is not supported%s", spelled, t, unsupportedHint(t))
	}
	if !pv.dataType(t, map[types.Type]bool{}) {
		return fmt.Sprintf("%s has type %s, which can hold a function value, an interface value, an error, a channel, or an unsafe.Pointer; "+
			"package-level variables of such types that are changed are not supported yet", spelled, t)
	}
	return ""
}

// isAssigned reports whether a package-level variable is an assigned
// variable of this package that a verified function can read and write.
func (pv *pkgVerifier) isAssigned(variable *types.Var) bool {
	return variable != nil && variable.Pkg() == pv.pass.Pkg && variable.Parent() == variable.Pkg().Scope() &&
		pv.reassigned[variable] && pv.assignedWhy(variable) == ""
}

// globalCells returns the cells of the storage of an assigned variable:
// those of its type, each in a region of its own.
func (pv *pkgVerifier) globalCells(variable *types.Var) []cell {
	cells := slices.Clone(pv.cellsOf(variable.Type()))
	leaves := mustLayout(variable.Type())
	for i := range cells {
		cells[i].key = varRegion + errorKey(variable) + leaves[i].path
	}
	return cells
}

// globalRef is the reference at which the storage of an assigned variable
// lies.
func globalRef(variable *types.Var) *logic.Term {
	return logic.Const("varref "+errorKey(variable), logic.Ref)
}

// noteGlobal states, once on a path, that the storage of an assigned
// variable existed on entry.
func (v *fnVerifier) noteGlobal(st *state, variable *types.Var) {
	if st == nil {
		return
	}
	if v.assignedMet == nil {
		v.assignedMet = map[string]*types.Var{}
	}
	v.assignedMet[errorKey(variable)] = variable
	note := "var " + errorKey(variable)
	if st.noted[note] {
		return
	}
	st.noted[note] = true
	ref := globalRef(variable)
	st.assume(logic.And(logic.Not(logic.Eq(ref, logic.RefLit(0))), logic.Lt(ref, v.entryBrk)))
}

// readGlobal reads the value of an assigned variable where it is now.
func (v *fnVerifier) readGlobal(variable *types.Var, pos token.Pos, st *state, guard []*logic.Term) value {
	v.noteGlobal(st, variable)
	cells, ref := v.globalCells(variable), globalRef(variable)
	return v.readAt(st, guard, v.unit.start(), v.spelling(variable), pos, func(sink *state, mem memory) value {
		val := v.fetch(sink, mem, cells, ref, logic.IntLit(0))
		v.noteTyped(sink, val, variable.Type())
		return val
	})
}

// variableTarget locates a Modifies entry whose path starts at a
// package-level variable. For an assigned variable of this package the path
// starts in its storage; the entry that names the variable alone covers
// that storage and what an entry of a parameter of its type covers, as
// also. For a fixed variable, whose value is a constant, it covers what the
// variable refers to.
func (v *fnVerifier) variableTarget(fn *funcInfo, m *modTarget, variable *types.Var, sink *state, mem memory) (shape, target, error) {
	spelled := v.spelling(variable)
	symbolic := mem == nil
	t := variable.Type()
	if fn.spelling().trust != nil || fn.spelling().valueOf != nil || fn.spelling().methodOf != nil {
		return shape{}, target{}, fmt.Errorf("%s is a package-level variable, which a Modifies clause of a trusted contract or of a type cannot name yet", spelled)
	}
	if variable.Pkg() != v.pass.Pkg {
		return shape{}, target{}, fmt.Errorf("%s is a package-level variable of another package, which a Modifies clause cannot name yet", spelled)
	}
	if !v.reassigned[variable] {
		if !holdsMemory(t) || isError(t) {
			return shape{}, target{}, fmt.Errorf("%s is a package-level variable that nothing changes, and what it holds refers to no memory, so there is nothing to modify", spelled)
		}
		if _, why := v.usableFixed(variable); why != "" {
			return shape{}, target{}, errors.New(why)
		}
		root := located{typ: t}
		if !symbolic {
			val, why := v.fixedValue(sink, variable)
			if why != "" {
				return shape{}, target{}, errors.New(why)
			}
			root.val = val
		}
		return v.walkTarget(fn, m, nil, root, t, symbolic, nil, sink, mem)
	}
	if why := v.assignedWhy(variable); why != "" {
		return shape{}, target{}, errors.New(why)
	}
	cells, ref := v.globalCells(variable), globalRef(variable)
	root := located{typ: t, ref: ref, at: logic.IntLit(0), cells: cells}
	if !symbolic {
		v.noteGlobal(sink, variable)
		root.val = v.fetch(sink, mem, cells, ref, root.at)
		v.noteTyped(sink, root.val, t)
	}
	if len(m.steps) > 0 {
		return v.walkTarget(fn, m, nil, root, t, symbolic, nil, sink, mem)
	}
	// The storage itself.
	lo, hi := bounds(cells)
	form := shape{cells: cells, lo: lo, hi: hi}
	whole := target{text: m.text, clause: m.clause, cells: cells, single: true}
	if !symbolic {
		whole.ref, whole.lo, whole.hi = ref, logic.IntLit(lo), logic.IntLit(hi)
	}
	// And what its value refers to, as for a parameter of its type.
	if holdsMemory(t) && !isStructType(t) {
		contents := located{typ: t, val: root.val}
		cform, ct, err := v.walkTarget(fn, m, nil, contents, t, symbolic, nil, sink, mem)
		if err != nil {
			return shape{}, target{}, err
		}
		form.also, whole.also = []shape{cform}, []target{ct}
	}
	return form, whole, nil
}

// locateAssigned follows a path of an annotation that starts at an
// assigned variable: in a contract its value when the function is called,
// primed its value on return, and inside a body its current value, or with
// old its value when the function was entered.
func (e *specEnv) locateAssigned(variable *types.Var, steps []logic.Step, when logic.When) (reached, error) {
	spelled := e.v.spelling(variable)
	hops, final, err := plan(variable.Type(), steps, e.writtenIn())
	if err != nil {
		return reached{}, fmt.Errorf("%s%v", spelled, err)
	}
	mem := e.now
	switch when {
	case logic.Old:
		if e.fn != nil {
			return reached{}, fmt.Errorf("old(%s) is only allowed inside a body; in a contract %s already denotes the value on entry", spelled, spelled)
		}
		mem = memory{}
	case logic.Primed:
		switch {
		case e.fn == nil:
			return reached{}, fmt.Errorf("%s' is only allowed in Ensures; inside a body %s already denotes the current value", spelled, spelled)
		case e.post == nil:
			return reached{}, fmt.Errorf("%s' describes the state on return and is only allowed in Ensures", spelled)
		}
		mem = e.post
	}
	e.v.noteGlobal(e.sink, variable)
	val := e.v.fetch(e.sink, mem, e.v.globalCells(variable), globalRef(variable), logic.IntLit(0))
	e.v.noteTyped(e.sink, val, variable.Type())
	cur, ground := e.v.follow(e.sink, mem, val, hops)
	found := reached{val: cur, typ: final, mem: mem, hops: len(hops)}
	if ground {
		found.sink = e.sink
	}
	return found, nil
}

// callableElsewhere reports whether code of another package can call a
// function of this package: it is exported, a method with an exported
// name, or named anywhere in the package other than as the function of a
// call, so that it may be made into a value.
func (pv *pkgVerifier) callableElsewhere(obj types.Object) bool {
	if obj == nil || obj.Exported() {
		return true
	}
	if pv.asValues == nil {
		pv.asValues = map[types.Object]bool{}
		for _, file := range pv.pass.Files {
			var stack []ast.Node
			ast.Inspect(file, func(n ast.Node) bool {
				if n == nil {
					stack = stack[:len(stack)-1]
					return true
				}
				stack = append(stack, n)
				id, ok := n.(*ast.Ident)
				if !ok {
					return true
				}
				used := pv.info.Uses[id]
				if _, isFunc := used.(*types.Func); !isFunc {
					return true
				}
				var expr ast.Node = id
				i := len(stack) - 2
				if i >= 0 {
					if sel, ok := stack[i].(*ast.SelectorExpr); ok && sel.Sel == id {
						expr, i = sel, i-1
					}
				}
				for i >= 0 {
					if paren, ok := stack[i].(*ast.ParenExpr); ok {
						expr, i = paren, i-1
						continue
					}
					break
				}
				if call, ok := stack[max(i, 0)].(*ast.CallExpr); i >= 0 && ok && call.Fun == expr {
					return true
				}
				pv.asValues[used] = true
				return true
			})
		}
	}
	return pv.asValues[obj]
}

// checkHiddenRequires reports each top-level conjunct of a Requires of a
// function that code of another package can call, when it reads a
// package-level variable that is not exported: no caller there can name the
// condition, establish it, or see it fail (F12 of the design review).
func (v *fnVerifier) checkHiddenRequires(st *state) {
	if v.fn.decl == nil || !v.callableElsewhere(v.fn.obj) {
		return
	}
	for _, c := range v.fn.requires {
		if c.node == nil {
			continue
		}
		for _, conjunct := range c.node.Conjuncts() {
			scratch := st.clone()
			env := &specEnv{v: v, sink: scratch, fn: v.fn, args: v.entry, now: memory{}}
			t := v.formula(c, conjunct, env)
			regions := map[string]*types.Var{}
			for _, variable := range v.assignedMet {
				for _, c := range v.globalCells(variable) {
					regions[entryRegion+c.key] = variable
				}
			}
			var hidden *types.Var
			seen := map[*logic.Term]bool{}
			var walk func(t *logic.Term)
			walk = func(t *logic.Term) {
				if seen[t] || hidden != nil {
					return
				}
				seen[t] = true
				if variable := regions[t.Name]; t.Op == logic.OpConst && variable != nil && !variable.Exported() {
					hidden = variable
				}
				for _, arg := range t.Args {
					walk(arg)
				}
			}
			walk(t)
			if hidden == nil {
				continue
			}
			v.report(c.pos, "the Requires clause %s reads %s, a package-level variable that is not exported, and code of another package can call %s, "+
				"where no caller can name the condition or see it fail; test the value in the body instead", conjunct, hidden.Name(), v.fn.obj.Name())
		}
	}
}
