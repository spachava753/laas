package vego

import (
	"fmt"
	"go/token"
	"go/types"
	"strings"

	"github.com/spachava753/laas/vego/internal/logic"
)

// Functions that may end the process (F37, step 1).
//
// os.Exit ends the process: it does not return, and it runs no deferred
// call. An entry says that its function may do so with exits, and that it
// always does with exits and an ensures that is the single clause False. A
// verified function says it with an Exits annotation, and with Ensures
// False when it never returns. A call of such a function is checked like
// any call; on the path where it ends the process nothing follows, no
// deferred call runs, and nothing is checked, since nothing runs. Where the
// function returns, its Ensures holds.
//
// A function that may reach such a call must say so, and so must its
// callers in turn, so that a caller cannot end the process without its
// contract saying it may. main and init need not: what calls them is the
// runtime. The initialiser of a package-level variable need not either,
// for the same reason. A main that its package calls or uses as a value is
// a function like any other there, and says so if it may end the process.
//
// What could end the process where no call is written is refused: a
// method with Exits, or an entry of a method or of a type with exits,
// since fmt, errors, and conversions to interfaces call methods without a
// call in source; a function value made of a function that may exit; a
// function handed to a trusted function under calls, whose contract
// assumes that each call returns; and a deferred call that may exit, whose
// path would end in the deferred run at a return.

const (
	exitsOnlyFunctions = "exits is allowed only in the entry of a package-level function: fmt, errors, and conversions to interfaces " +
		"call methods and values of function types where no call is written, and a run that ends the process there would not be seen"
	exitsOnMethod = "a method cannot have an Exits annotation yet: fmt, errors, and conversions to interfaces call methods where no call is written, " +
		"and a run that ends the process there would not be seen; end the process in a function"
)

// placeExits records the Exits annotation of a function declaration.
func (pv *pkgVerifier) placeExits(fn *funcInfo, c *clause) {
	switch {
	case strings.TrimSpace(c.text) != "":
		pv.report(c.pos, "an Exits annotation takes nothing after the keyword: the form with a condition, as in // @Exits %s, is not supported yet", strings.TrimSpace(c.text))
		fn.broken = true
	case fn.obj.Type().(*types.Signature).Recv() != nil:
		pv.report(c.pos, "%s", exitsOnMethod)
		fn.broken = true
	case fn.exitsClause != nil:
		pv.report(c.pos, "function %s already has an Exits annotation", fn.obj.Name())
		fn.broken = true
	default:
		fn.exits, fn.exitsClause = true, c
	}
}

// neverReturns reports whether a contract says that its function never
// returns: it may end the process, and its only Ensures is False.
func neverReturns(fn *funcInfo) bool {
	if fn == nil || !fn.exits || len(fn.ensures) != 1 {
		return false
	}
	node := fn.ensures[0].node
	return node != nil && node.Kind == logic.NBool && node.Val == 0
}

// isEntryPoint reports whether a function is one that only the runtime
// calls: init, or main of package main.
func (pv *pkgVerifier) isEntryPoint(obj *types.Func) bool {
	if obj == nil || obj.Pkg() != pv.pass.Pkg || obj.Type().(*types.Signature).Recv() != nil {
		return false
	}
	switch obj.Name() {
	case "init":
		return true
	case "main":
		return pv.pass.Pkg.Name() == "main" && pv.pass.Pkg.Scope().Lookup("main") == obj
	}
	return false
}

// findMainReference records where the package refers to its main
// function, a call of it or a value of it, if it does.
func (pv *pkgVerifier) findMainReference() {
	pv.mainRef = token.NoPos
	if pv.pass.Pkg.Name() != "main" {
		return
	}
	main, _ := pv.pass.Pkg.Scope().Lookup("main").(*types.Func)
	if main == nil {
		return
	}
	for id, obj := range pv.info.Uses {
		if obj == main && (pv.mainRef == token.NoPos || id.Pos() < pv.mainRef) {
			pv.mainRef = id.Pos()
		}
	}
}

// mainReference returns where the package refers to its main function, or
// NoPos.
func (pv *pkgVerifier) mainReference() token.Pos { return pv.mainRef }

// mayExit reports whether a call of a contract may end the process.
func mayExit(fn *funcInfo) bool {
	return fn != nil && fn.exits
}

// checkExitAllowed checks that the code being verified may make a call that
// may end the process, of callee: what holds the call says so.
func (v *fnVerifier) checkExitAllowed(pos token.Pos, callee string) {
	switch {
	case len(v.forbidden) > 0:
		v.unsupported(pos, fmt.Sprintf("it calls %s, which may end the process, in a function handed to %s; a function handed to a trusted function "+
			"may not end the process, since the contract of what calls it assumes that each call returns", callee, v.forbidden[len(v.forbidden)-1].by))
	case v.fn.spelled != nil:
		v.unsupported(pos, fmt.Sprintf("it calls %s, which may end the process, in a function literal used as a value of type %s; "+
			"a call of a function value is assumed to return, since a function type cannot have an Exits annotation yet", callee, v.fn.spelled.obj.Name()))
	case v.deferring > 0:
		v.unsupported(pos, fmt.Sprintf("it calls %s, which may end the process, in a deferred call; a deferred call that may end the process "+
			"is not supported yet", callee))
	case v.inInitialiser:
		return
	case v.fn.decl == nil:
		v.unsupported(pos, fmt.Sprintf("it calls %s, which may end the process, where that cannot be said", callee))
	}
	v.exitReached = true
	// init, and a main that its package does not refer to, need no Exits:
	// only the runtime runs them.
	entry := v.pkgVerifier.isEntryPoint(v.fn.obj)
	if v.fn.exits || entry && (v.fn.obj.Name() == "init" || v.pkgVerifier.mainReference() == token.NoPos) {
		return
	}
	if entry {
		v.report(pos, "main calls %s, which may end the process, and main is referred to at %s; a main that its package calls or uses as a value "+
			"says so with // @Exits in its doc comment, as any function does", callee, v.placeOf(v.pkgVerifier.mainReference()))
		return
	}
	if v.fn.obj.Type().(*types.Signature).Recv() != nil {
		v.report(pos, "%s calls %s, which may end the process, and a method cannot end the process yet; return an error, "+
			"or end the process in a function that calls %s", v.fn.obj.Name(), callee, v.fn.obj.Name())
		return
	}
	v.report(pos, "%s calls %s, which may end the process; add // @Exits to the doc comment of %s if it may end the process, "+
		"or call something that returns", v.fn.obj.Name(), callee, v.fn.obj.Name())
}
