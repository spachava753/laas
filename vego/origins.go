package vego

import (
	"go/ast"
	"go/token"
	"go/types"

	"golang.org/x/tools/go/types/typeutil"
)

// An error may be formatted only when it is known where it comes from.
// Formatting runs the error's methods and, for some verbs, methods of what
// the error contains; an error from outside could use them to write memory
// the function reasons about. An error of known origin cannot. It is one of
// two kinds:
//
//   - made: errors.New or fmt.Errorf made it, here, in a verified function
//     this one called, or in the initialiser of a sentinel, and nothing but
//     plain values and other made errors went into it. Its methods, and
//     those of every error in its tree, are those of the standard library.
//   - vouched: a trusted function returned it in a result its contract
//     lists under vouches, or it holds such an error in its tree, or a
//     verified function returned it. Nothing is known of its type. The author of the contract claims that every method of it,
//     of every error in its tree, and of every value these hold returns
//     without panicking and writes nothing a caller can see, whatever it
//     is passed; that == on these errors cannot panic and is identity, so
//     that errors.Is answers the same for errors and for targets that ==
//     reports equal; and that what errors.Is reports for it never changes.
//
// What is concluded from a known origin needs only what both kinds give:
// formatting it, the first argument of errors.Is, the safe side of ==, and
// handing it to a trusted function without runs all rest on its methods
// and its == alone. What needs a made error is not drawn from knownError:
// that an error is not nil and differs from others, and what errors.Is finds
// in it, are noted where errors.New and fmt.Errorf are called and for
// sentinels; see noteError and noteTree.
//
// Origin is decided from the text of a function, without regard to the path
// taken: an error variable has a known origin when every assignment to it in
// the function gives it one.

// origins holds, for one function body, what each error variable is assigned.
// A variable that is assigned in a way that is not understood is unknown.
type origins struct {
	sources map[*types.Var][]source
	unknown map[*types.Var]bool
}

// source is something assigned to an error variable: an expression, or the
// result with the given index of a call that returns several values.
type source struct {
	expr  ast.Expr
	index int
}

// originsOf collects the assignments to variables in a function body.
func (pv *pkgVerifier) originsOf(body *ast.BlockStmt) *origins {
	if known, ok := pv.origins[body]; ok {
		return known
	}
	o := &origins{sources: map[*types.Var][]source{}, unknown: map[*types.Var]bool{}}
	pv.origins[body] = o
	variable := func(e ast.Expr) *types.Var {
		id, ok := ast.Unparen(e).(*ast.Ident)
		if !ok {
			return nil
		}
		found, _ := pv.info.ObjectOf(id).(*types.Var)
		return found
	}
	assign := func(targets, values []ast.Expr) {
		for i, target := range targets {
			to := variable(target)
			switch {
			case to == nil:
			case len(values) == len(targets):
				o.sources[to] = append(o.sources[to], source{values[i], -1})
			case len(values) == 1:
				o.sources[to] = append(o.sources[to], source{values[0], i})
			default:
				o.unknown[to] = true
			}
		}
	}
	ast.Inspect(body, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.AssignStmt:
			if n.Tok != token.ASSIGN && n.Tok != token.DEFINE {
				for _, target := range n.Lhs {
					o.unknown[variable(target)] = true
				}
				break
			}
			assign(n.Lhs, n.Rhs)
		case *ast.ValueSpec:
			targets := make([]ast.Expr, len(n.Names))
			for i, name := range n.Names {
				targets[i] = name
			}
			// Without a value the variable starts as nil.
			if len(n.Values) > 0 {
				assign(targets, n.Values)
			}
		case *ast.RangeStmt:
			for _, target := range []ast.Expr{n.Key, n.Value} {
				if target != nil {
					o.unknown[variable(target)] = true
				}
			}
		case *ast.UnaryExpr:
			if n.Op == token.AND {
				o.unknown[variable(n.X)] = true
			}
		}
		return true
	})
	// The parameters of a literal used in place are assigned the arguments
	// of its calls, which are all in the body. Those of any other literal
	// could be given anything.
	bound, _ := literalUses(pv.info, body)
	inPlace := map[*ast.FuncLit]bool{}
	for _, lit := range bound {
		inPlace[lit] = true
	}
	ast.Inspect(body, func(n ast.Node) bool {
		call, ok := n.(*ast.CallExpr)
		if !ok {
			return true
		}
		var lit *ast.FuncLit
		switch fun := ast.Unparen(call.Fun).(type) {
		case *ast.FuncLit:
			lit = fun
		case *ast.Ident:
			lit = bound[variable(fun)]
		}
		if lit == nil {
			return true
		}
		inPlace[lit] = true
		params := pv.info.TypeOf(lit).(*types.Signature).Params()
		for i := range params.Len() {
			if len(call.Args) != params.Len() {
				o.unknown[params.At(i)] = true
				continue
			}
			o.sources[params.At(i)] = append(o.sources[params.At(i)], source{call.Args[i], -1})
		}
		return true
	})
	ast.Inspect(body, func(n ast.Node) bool {
		if lit, ok := n.(*ast.FuncLit); ok && !inPlace[lit] {
			for param := range pv.info.TypeOf(lit).(*types.Signature).Params().Variables() {
				o.unknown[param] = true
			}
		}
		return true
	})
	return o
}

// knownError reports whether an error expression in a function body has a
// known origin: nil, a new error, an error variable of this package or of
// another that always holds a new error into which nothing of unknown origin
// went, the result of a function that only returns such errors, or a local
// variable that is only ever assigned such errors.
// visiting holds the variables being decided, which settles a variable that
// is assigned from itself.
func (pv *pkgVerifier) knownError(o *origins, e ast.Expr, index int, visiting map[*types.Var]bool) bool {
	e = ast.Unparen(e)
	if pv.info.Types[e].IsNil() {
		return true
	}
	switch e := e.(type) {
	case *ast.CallExpr:
		callee := typeutil.StaticCallee(pv.info, e)
		if errorConstructor(callee) {
			return true
		}
		// What a function is known for is the errors it returns, not
		// whatever else it returns that happens to be assigned to an error.
		result := pv.info.TypeOf(e)
		at := 0
		if tuple, ok := result.(*types.Tuple); ok && index >= 0 && index < tuple.Len() {
			result, at = tuple.At(index).Type(), index
		}
		return callee != nil && isError(result) && (pv.returnsKnownErrors(callee) || pv.vouchedResult(callee, at))
	case *ast.Ident:
		variable, ok := pv.info.ObjectOf(e).(*types.Var)
		return ok && index < 0 && isError(variable.Type()) && pv.knownVariable(o, variable, visiting)
	case *ast.SelectorExpr:
		variable := pv.namedVariable(e)
		return variable != nil && index < 0 && isError(variable.Type()) && pv.knownVariable(o, variable, visiting)
	}
	return false
}

// knownVariable reports whether an error variable only ever holds errors of
// known origin.
func (pv *pkgVerifier) knownVariable(o *origins, variable *types.Var, visiting map[*types.Var]bool) bool {
	if r, ok := pv.homemadeValue(variable); ok {
		pv.rely(r.keys)
		return true
	}
	switch {
	case visiting[variable]:
		return true
	case o.unknown[variable] || (variable.Pkg() != nil && variable.Parent() == variable.Pkg().Scope()) || pv.isParameter[variable]:
		return false
	}
	visiting[variable] = true
	defer delete(visiting, variable)
	for _, from := range o.sources[variable] {
		if !pv.knownError(o, from.expr, from.index, visiting) {
			return false
		}
	}
	return true
}

// returnsKnownErrors reports whether every error a function returns has a
// known origin. Only verified functions qualify: for one of this package the
// answer is computed from its body, for one of another package it was
// published with its contract.
func (pv *pkgVerifier) returnsKnownErrors(callee *types.Func) bool {
	if fn := pv.funcs[callee]; fn != nil {
		return pv.knownReturns[fn]
	}
	imported := pv.importedContract(callee)
	return imported != nil && imported.imported.KnownErrors
}

// vouchedResult reports whether a function is trusted and its contract
// vouches for the errors of the result with the given index. A contract that
// cannot be used makes the call itself an error, so its claim is read here
// as written.
func (pv *pkgVerifier) vouchedResult(callee *types.Func, index int) bool {
	if own := pv.funcs[callee]; (own != nil && own.annotated()) || pv.importedContract(callee) != nil {
		return false
	}
	fn := pv.trustedContract(callee)
	return fn != nil && fn.vouches[index]
}

// findKnownReturns decides for every annotated function of the package
// whether all errors it returns have a known origin. A function qualifies
// only through functions that qualify, so the answer is the least fixed
// point: functions that only return each other's errors do not qualify.
func (pv *pkgVerifier) findKnownReturns() {
	for _, fn := range pv.order {
		for _, param := range fn.params {
			pv.isParameter[param] = true
		}
	}
	for changed := true; changed; {
		changed = false
		for _, fn := range pv.order {
			if pv.knownReturns[fn] || !fn.annotated() || fn.decl.Body == nil || !pv.allReturnsKnown(fn) {
				continue
			}
			pv.knownReturns[fn], changed = true, true
		}
	}
}

// allReturnsKnown reports whether every return statement of a function
// returns errors of known origin, given what is known of other functions.
func (pv *pkgVerifier) allReturnsKnown(fn *funcInfo) bool {
	o := pv.originsOf(fn.decl.Body)
	known := true
	check := func(e ast.Expr, index int) {
		known = known && pv.knownError(o, e, index, map[*types.Var]bool{})
	}
	ast.Inspect(fn.decl.Body, func(n ast.Node) bool {
		if _, isLiteral := n.(*ast.FuncLit); isLiteral {
			return false
		}
		ret, ok := n.(*ast.ReturnStmt)
		if !ok {
			return true
		}
		for i, result := range fn.results {
			switch {
			case !isError(result.Type()):
			case len(ret.Results) == 0:
				// A bare return yields the named result.
				known = known && pv.knownVariable(o, result, map[*types.Var]bool{})
			case len(ret.Results) == len(fn.results):
				check(ret.Results[i], -1)
			default:
				check(ret.Results[0], i)
			}
		}
		return true
	})
	return known
}
