package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"slices"

	"github.com/spachava753/laas/vego/internal/logic"
)

// A logger in a package-level variable (step 7 of F32).
//
// var logger = log.New(w, prefix, flags), which nothing assigns, can be
// read when its initialiser runs as code and verifies, and every use of it
// in the package is a comparison with nil or the receiver of a call of
// (*log.Logger).Printf, Print, or Println under their shipped entries,
// which keep the logger's output and prefix and ensure ready(l'). Then
// ready holds of what the variable points to at every point outside such
// a call: log.New ensures it, each of those methods ensures it again, and
// nothing else writes the Logger, whose fields are unexported in another
// module and which the copy rule keeps from being copied or overwritten. So
// a call of one of them assumes ready of its receiver before it.
//
// When the writer the initialiser gives is inert, as os.Stderr or a value
// of a concrete type whose methods that io.Writer takes write nothing
// behind their receiver, a call of one of them changes nothing a caller can
// see: the writer's footprint is empty and stays so, its output never
// changes by the rule on uses, and of the Logger's own cells only ready is
// something a formula can read, which the call restores. Such a call drops
// the targets of its receiver, so nothing need be listed. Otherwise the
// function lists the logger, which covers the Logger and what it owns, the
// footprint and states of its writer, as Modifies of a pointer to an owner
// does.
//
// An exported logger is not supported: code of another package could use it
// in other ways.

// printingLoggerMethods are the methods of *log.Logger a logger in a variable may
// be the receiver of.
var printingLoggerMethods = []string{"(*log.Logger).Printf", "(*log.Logger).Print", "(*log.Logger).Println"}

// isLoggerType reports whether t is *log.Logger.
func isLoggerType(t types.Type) bool {
	pointer, ok := types.Unalias(t).(*types.Pointer)
	if !ok {
		return false
	}
	named, ok := types.Unalias(pointer.Elem()).(*types.Named)
	return ok && named.Obj().Pkg() != nil && named.Obj().Pkg().Path() == "log" && named.Obj().Name() == "Logger"
}

// loggerWhy says why a package-level variable of type *log.Logger cannot be
// read, or "" when it is a logger in a variable as above.
func (pv *pkgVerifier) loggerWhy(variable *types.Var) string {
	spelled := pv.spelling(variable)
	switch {
	case variable.Pkg() != pv.pass.Pkg:
		return fmt.Sprintf("%s is a logger of package %s, and reading one of another package is not supported yet", spelled, variable.Pkg().Path())
	case variable.Exported():
		return fmt.Sprintf("%s is an exported logger, which code of another package could use in other ways; a logger in a variable that verified code reads must not be exported", spelled)
	case pv.reassigned[variable]:
		return fmt.Sprintf("%s %s; a logger in a variable must be given its value only by its initialiser", spelled, pv.ownChanges[variable])
	}
	if why, done := pv.loggerUse[variable]; done {
		return why
	}
	why := pv.loggerUses(variable)
	// One whose initialiser did not verify is reported with why, by
	// initialiserWhy.
	if why == "" && !pv.loggerMade[variable] && pv.initWhy[variable] == "" {
		why = fmt.Sprintf("%s is not given its value by a call of log.New in its initialiser that verifies", spelled)
	}
	pv.loggerUse[variable] = why
	return why
}

// loggerUses returns where a use of a logger in a variable is something
// other than a comparison with nil or the receiver of one of printingLoggerMethods
// under its shipped entry, or "".
func (pv *pkgVerifier) loggerUses(variable *types.Var) string {
	found := ""
	for _, file := range pv.pass.Files {
		var stack []ast.Node
		ast.Inspect(file, func(n ast.Node) bool {
			if n == nil {
				stack = stack[:len(stack)-1]
				return true
			}
			stack = append(stack, n)
			id, ok := n.(*ast.Ident)
			if !ok || found != "" || pv.info.Uses[id] != variable {
				return true
			}
			if !pv.loggerUseAllowed(stack) {
				found = fmt.Sprintf("%s is used at %s other than as the receiver of Printf, Print, or Println or in a comparison with nil, "+
					"so what it holds is not known", variable.Name(), pv.placeOfPos(id.Pos()))
			}
			return true
		})
	}
	return found
}

// loggerUseAllowed reports whether the use of a logger in a variable at the
// end of stack is a comparison with nil or the receiver of a call, not in
// a go statement, of one of printingLoggerMethods under its shipped entry.
func (pv *pkgVerifier) loggerUseAllowed(stack []ast.Node) bool {
	i := len(stack) - 1
	var cur ast.Expr = stack[i].(*ast.Ident)
	for i--; i >= 0; i-- {
		paren, ok := stack[i].(*ast.ParenExpr)
		if !ok {
			break
		}
		cur = paren
	}
	if i < 0 {
		return false
	}
	switch parent := stack[i].(type) {
	case *ast.BinaryExpr:
		other := parent.X
		if other == cur {
			other = parent.Y
		}
		return (parent.Op == token.EQL || parent.Op == token.NEQ) && pv.info.Types[other].IsNil()
	case *ast.SelectorExpr:
		selection := pv.info.Selections[parent]
		if parent.X != cur || selection == nil || selection.Kind() != types.MethodVal || i == 0 {
			return false
		}
		call, ok := stack[i-1].(*ast.CallExpr)
		if !ok || call.Fun != parent {
			return false
		}
		if i >= 2 {
			if _, inGo := stack[i-2].(*ast.GoStmt); inGo {
				return false
			}
		}
		method, _ := selection.Obj().(*types.Func)
		if method == nil || !slices.Contains(printingLoggerMethods, method.FullName()) {
			return false
		}
		entry := pv.entryFor(method.FullName())
		return entry != nil && entry.file.shipped
	}
	return false
}

// loggerInitialiser reports, of an initialiser that runs as code, whether
// it gives a logger in a variable its value by a call of log.New, and
// whether the writer it gives is inert. runInitialiser records it when the
// run verifies.
func (v *fnVerifier) loggerInitialiser(init *types.Initializer) (made, inert bool) {
	if len(init.Lhs) != 1 || init.Lhs[0] == nil || !isLoggerType(init.Lhs[0].Type()) {
		return false, false
	}
	call, ok := ast.Unparen(init.Rhs).(*ast.CallExpr)
	if !ok || len(call.Args) != 3 {
		return false, false
	}
	callee := v.calleeAt(call)
	if callee == nil || callee.FullName() != "log.New" {
		return false, false
	}
	w := ast.Unparen(call.Args[0])
	want := callee.Type().(*types.Signature).Params().At(0).Type()
	if root := v.namedVariable(w); root != nil && root.Pkg() != nil && root.Parent() == root.Pkg().Scope() && isIface(root.Type()) {
		return true, v.inertFixed(root)
	}
	from := v.info.TypeOf(w)
	return true, from != nil && !isIface(from) && !v.info.Types[w].IsNil() && !v.hasStates(want) && v.writingImplementation(from, want) == nil
}

// loggerCall prepares a call of one of printingLoggerMethods whose receiver is a
// logger in a variable: it assumes ready of the receiver, in the memory of
// the call, and reports whether the logger is inert.
func (v *fnVerifier) loggerCall(call *ast.CallExpr, fn *funcInfo, pre *specEnv, st *state) (inert bool) {
	if fn.trust == nil || fn.obj == nil || !slices.Contains(printingLoggerMethods, fn.obj.FullName()) {
		return false
	}
	sel, ok := ast.Unparen(call.Fun).(*ast.SelectorExpr)
	if !ok {
		return false
	}
	variable := v.namedVariable(ast.Unparen(sel.X))
	if variable == nil || !isLoggerType(variable.Type()) || v.loggerWhy(variable) != "" {
		return false
	}
	ready, err := pre.Path(fn.params[0].Name(), []logic.Step{{State: "ready"}}, logic.Now)
	if err != nil {
		panic(fmt.Sprintf("vego: internal error: ready of the receiver of %s cannot be read: %v", fn.obj.FullName(), err))
	}
	st.assume(ready)
	return v.loggerInert[variable]
}

// trustedRuns returns, for a call of a trusted function, which of its
// operands, the arguments and then the receiver, the entry says it may run
// the code of during the call, or nil when the callee is not trusted.
func (pv *pkgVerifier) trustedRuns(call *ast.CallExpr, callee *types.Func) func(i, args int) bool {
	if isGeneric(callee) || callee.Origin() != callee {
		return nil
	}
	fn := pv.trustedContract(callee)
	if fn == nil || fn.trust == nil || len(fn.defects) > 0 {
		return nil
	}
	recv := callee.Type().(*types.Signature).Recv() != nil && !pv.methodExpression(call)
	return func(i, args int) bool {
		index := i
		switch {
		case i >= args:
			index = 0
		case recv:
			index = i + 1
		}
		if len(fn.params) == 0 {
			return true
		}
		p := fn.params[min(index, len(fn.params)-1)]
		return fn.runs.get(p) || fn.calls.get(p) != nil || p == fn.formatted || p == fn.prints || p == fn.encoded
	}
}
