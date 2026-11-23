package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"maps"
	"math/big"
	"path/filepath"
	"slices"
	"strings"

	"github.com/spachava753/laas/vego/internal/logic"
	"github.com/spachava753/laas/vego/internal/solver"
	"golang.org/x/tools/go/types/typeutil"
)

// findSentinels records the package-level error variables that hold one
// error for as long as code of their importers runs: those never assigned
// or addressed anywhere in the package, provided that no code of the
// package can run before they are initialised. Such a variable is stable,
// and of one of three kinds; see stableKind. Each of them is published as a
// fact for the packages built with this one, which run only once its
// initialisation is over and so need no such proviso. That another package
// does not assign to it is checked where both that package and a proof that
// relies on the variable are known; see reportSentinelWrites.
func (pv *pkgVerifier) findSentinels() {
	pv.sentinels = map[*types.Var]bool{}
	pv.unsettled = map[*types.Var]string{}
	pv.reliedKeys = map[string]bool{}
	pv.reliedValues = map[string]bool{}
	pv.readOnlyRefs = map[string]string{}
	pv.fixedRefs = map[string]string{}
	pv.returnedBy = map[string]returned{}
	pv.homemade = map[*types.Var]bool{}
	pv.candidates = map[*types.Var]sentinelInfo{}
	// What this package writes of the error variables of other packages
	// is published, whichever way this returns.
	defer func() {
		if len(pv.writes) > 0 {
			pv.pass.ExportPackageFact(&sentinelWritesFact{Writes: pv.writes})
		}
	}()
	// The error variables of the package in the order of their
	// declarations, with what each is initialised with: a value of its
	// own, or the result at index of a call that gives several.
	type declared struct {
		value ast.Expr
		index int
	}
	declarations := map[*types.Var]declared{}
	var variables []*types.Var
	bodies := map[*types.Func]*ast.FuncDecl{}
	for _, file := range pv.pass.Files {
		for _, decl := range file.Decls {
			if fd, ok := decl.(*ast.FuncDecl); ok {
				if fn, ok := pv.info.Defs[fd.Name].(*types.Func); ok {
					bodies[fn] = fd
				}
				continue
			}
			gen, ok := decl.(*ast.GenDecl)
			if !ok || gen.Tok != token.VAR {
				continue
			}
			for _, spec := range gen.Specs {
				spec := spec.(*ast.ValueSpec)
				for i, name := range spec.Names {
					variable, _ := pv.info.Defs[name].(*types.Var)
					if variable == nil || !isError(variable.Type()) {
						continue
					}
					d := declared{index: -1}
					switch {
					case len(spec.Values) == len(spec.Names):
						d.value = spec.Values[i]
					case len(spec.Values) == 1:
						d.value, d.index = spec.Values[0], i
					}
					declarations[variable] = d
					variables = append(variables, variable)
				}
			}
		}
	}
	pv.findChanges()
	// Each stable variable is of one kind, read from its initialiser.
	made := map[*types.Var]*ast.CallExpr{}
	aliases := map[*types.Var]*types.Var{}
	var stable []*types.Var
	for _, variable := range variables {
		if pv.reassigned[variable] {
			continue
		}
		stable = append(stable, variable)
		d := declarations[variable]
		call, isCall := ast.Unparen(d.value).(*ast.CallExpr)
		switch target := pv.aliasTarget(d.value, bodies); {
		case d.index < 0 && isCall && errorConstructor(typeutil.StaticCallee(pv.info, call)):
			made[variable] = call
			pv.sentinels[variable] = true
		case d.index < 0 && target != nil:
			aliases[variable] = target
			pv.candidates[variable] = sentinelInfo{Kind: stableAlias, Alias: errorKey(target)}
		default:
			info := sentinelInfo{Kind: stableOpaque}
			if d.value != nil {
				info.NonNil, info.Comparable = concreteError(pv.info.Types[d.value], d.index)
			}
			pv.candidates[variable] = info
		}
	}
	// resolved follows an alias of this package to the variable it holds
	// in the end, which is not an alias of this package; nil when the
	// chain ends in a variable of this package that is not stable.
	var resolved func(variable *types.Var, seen map[*types.Var]bool) *types.Var
	resolved = func(variable *types.Var, seen map[*types.Var]bool) *types.Var {
		target, isAlias := aliases[variable]
		switch {
		case variable.Pkg() != pv.pass.Pkg || made[variable] != nil:
			return variable
		case !isAlias || seen[variable]:
			return nil
		}
		seen[variable] = true
		return resolved(target, seen)
	}
	// An alias that holds a sentinel of this package, or a variable of
	// another package, holds no code of this package, as a sentinel does
	// not; see hiddenInitCode. A variable of another package holds code of
	// this package only if this package handed it over, which is looked for
	// where that happens. An alias of an opaque variable of this package is
	// decided by the initialiser of that variable.
	for variable := range aliases {
		if final := resolved(variable, map[*types.Var]bool{}); final != nil && (final.Pkg() != pv.pass.Pkg || made[final] != nil) {
			pv.sentinels[variable] = true
		}
	}
	// homemadeOf says whether an error variable that went into an error
	// holds one into which nothing of unknown origin went.
	homemadeOf := func(other *types.Var) bool {
		final := resolved(other, map[*types.Var]bool{})
		switch {
		case final == nil:
			return false
		case final.Pkg() == pv.pass.Pkg:
			return pv.homemade[final]
		}
		_, ok := pv.homemadeValue(final)
		return ok
	}
	// An initialiser is not verified code, so nobody has checked what went
	// into the error it makes. The error is not nil whatever went in; its
	// origin is known only if nothing went in that brings code: plain values,
	// and other such variables. With %w anything else stays inside the
	// error, where Unwrap finds it.
	for again := true; again; {
		again = false
		for variable, call := range made {
			if pv.homemade[variable] {
				continue
			}
			plain := !slices.ContainsFunc(call.Args, func(arg ast.Expr) bool {
				if pv.info.Types[arg].IsNil() {
					return false
				}
				if other := pv.namedVariable(arg); other != nil && isError(other.Type()) {
					return !homemadeOf(other)
				}
				return plainReason(pv.info.TypeOf(arg), map[types.Type]bool{}) != ""
			})
			if plain {
				pv.homemade[variable], again = true, true
			}
		}
	}
	// What is known of a sentinel rests on the variables that went into
	// its error, on the variables they hold, and on what theirs rests on.
	var restsOf func(variable *types.Var) []string
	keysOf := func(other *types.Var) []string {
		keys := []string{errorKey(other)}
		if other.Pkg() != pv.pass.Pkg {
			if r, why := pv.resolve(other); why == "" {
				keys = r.keys
			}
			return keys
		}
		seen := map[*types.Var]bool{}
		for at := other; aliases[at] != nil && !seen[at]; at = aliases[at] {
			seen[at] = true
			keys = append(keys, errorKey(aliases[at]))
			if target := aliases[at]; target.Pkg() != pv.pass.Pkg {
				if r, why := pv.resolve(target); why == "" {
					keys = append(keys, r.keys...)
				}
				return keys
			}
		}
		if final := resolved(other, map[*types.Var]bool{}); final != nil && made[final] != nil {
			keys = append(keys, restsOf(final)...)
		}
		return keys
	}
	restsOf = func(variable *types.Var) []string {
		if info, done := pv.candidates[variable]; done {
			return info.Rests
		}
		var rests []string
		for _, arg := range made[variable].Args {
			other := pv.namedVariable(arg)
			if other == nil || other.Pkg() == nil || other.Parent() != other.Pkg().Scope() || !isError(other.Type()) {
				continue
			}
			rests = append(rests, keysOf(other)...)
		}
		slices.Sort(rests)
		rests = slices.Compact(rests)
		info := sentinelInfo{Kind: stableMade, Homemade: pv.homemade[variable], Rests: rests}
		var wrapped ast.Expr
		info.Tree, wrapped = pv.callWraps(made[variable])
		if wrapped != nil {
			// Only a variable that went into the error is a value that
			// can be named; anything else leaves the tree unknown.
			other := pv.namedVariable(wrapped)
			if other == nil || other.Pkg() == nil || other.Parent() != other.Pkg().Scope() {
				info.Tree = treeUnknown
			} else {
				info.Wraps = errorKey(other)
			}
		}
		pv.candidates[variable] = info
		return rests
	}
	published := map[string]sentinelInfo{}
	for _, variable := range stable {
		if made[variable] != nil {
			restsOf(variable)
		}
		published[variable.Name()] = pv.candidates[variable]
	}
	changes := map[string]string{}
	for _, variable := range variables {
		if why := pv.ownChanges[variable]; why != "" {
			changes[variable.Name()] = why
		}
	}
	if len(published) > 0 || len(changes) > 0 {
		pv.pass.ExportPackageFact(&sentinelsFact{Vars: published, Changed: changes})
	}
	if len(stable) == 0 {
		return
	}
	if hidden := pv.hiddenInitCode(); hidden != "" {
		for _, variable := range stable {
			pv.unsettled[variable] = hidden
		}
		clear(pv.sentinels)
	}
}

// aliasTarget returns the package-level error variable whose value an
// initialiser gives to the variable it initialises, if it is one of these:
// the variable itself, as in ErrNotExist = fs.ErrNotExist, or a call of a
// function of this package that takes nothing, is not generic, and whose
// whole body is a return of the variable, as in errNotExist() of io/fs.
// Go initialises the variable before the call is made: one of another
// package before this package, one of this package before every variable
// whose initialiser refers to a function that refers to it.
func (pv *pkgVerifier) aliasTarget(value ast.Expr, bodies map[*types.Func]*ast.FuncDecl) *types.Var {
	if value == nil {
		return nil
	}
	if target := pv.namedErrorVariable(value); target != nil {
		return target
	}
	call, ok := ast.Unparen(value).(*ast.CallExpr)
	if !ok || len(call.Args) > 0 {
		return nil
	}
	id, ok := ast.Unparen(call.Fun).(*ast.Ident)
	if !ok {
		return nil
	}
	fn, ok := pv.info.Uses[id].(*types.Func)
	if !ok || fn.Pkg() != pv.pass.Pkg {
		return nil
	}
	sig := fn.Type().(*types.Signature)
	decl := bodies[fn]
	if sig.Recv() != nil || sig.TypeParams() != nil || sig.Params().Len() > 0 || sig.Results().Len() != 1 || decl == nil || decl.Body == nil {
		return nil
	}
	if len(decl.Body.List) != 1 {
		return nil
	}
	ret, ok := decl.Body.List[0].(*ast.ReturnStmt)
	if !ok || len(ret.Results) != 1 {
		return nil
	}
	return pv.namedErrorVariable(ret.Results[0])
}

// namedErrorVariable returns the package-level variable of type error that
// an expression names, or nil.
func (pv *pkgVerifier) namedErrorVariable(e ast.Expr) *types.Var {
	variable := pv.namedVariable(e)
	if variable == nil || variable.Pkg() == nil || variable.Parent() != variable.Pkg().Scope() || !isError(variable.Type()) {
		return nil
	}
	return variable
}

// concreteError reads what the static type of an initialiser says of the
// error it gives a variable: when it is a type other than an interface, the
// value is not nil, since converting a value of such a type to an interface,
// even a nil pointer, makes an interface that is not nil; and when, beyond
// that, == on values of the type is identity and cannot panic, comparing
// the variable with any error cannot panic either. index is the result of a
// call that gives several, or -1.
func concreteError(tv types.TypeAndValue, index int) (nonNil, comparable bool) {
	t := tv.Type
	if tuple, ok := t.(*types.Tuple); ok {
		if index < 0 || index >= tuple.Len() {
			return false, false
		}
		t = tuple.At(index).Type()
	} else if tv.IsNil() {
		return false, false
	}
	if t == nil || types.IsInterface(t) {
		return false, false
	}
	if basic, ok := t.(*types.Basic); ok && basic.Kind() == types.UntypedNil {
		return false, false
	}
	return true, identityComparable(t, map[types.Type]bool{})
}

// identityComparable reports whether == on two values of a type cannot panic
// and holds exactly when the values are the same: the type is a pointer,
// integer, string, or boolean type, or an array or struct type made only of
// these. An interface may hold an uncomparable value, and for a float or
// complex number == is not identity: NaN differs from itself, and 0 equals
// -0.
func identityComparable(t types.Type, seen map[types.Type]bool) bool {
	if seen[t] {
		return true
	}
	seen[t] = true
	switch u := t.Underlying().(type) {
	case *types.Basic:
		return u.Info()&(types.IsFloat|types.IsComplex) == 0 && u.Kind() != types.UntypedNil
	case *types.Pointer:
		return true
	case *types.Array:
		return identityComparable(u.Elem(), seen)
	case *types.Struct:
		for field := range u.Fields() {
			if !identityComparable(field.Type(), seen) {
				return false
			}
		}
		return true
	}
	return false
}

// hiddenInitCode looks for code that runs while the package-level variables
// are being initialised and that Go's ordering of initialisers does not see.
// Go initialises a variable after everything its initialiser refers to,
// following calls of named functions. A call of a function value or of an
// interface method, a goroutine, and a function of another package that is
// handed something of this package to call back are not followed, so through
// them a function of this package may run before a variable it reads has
// its value. It returns a description of the first such place, or "".
func (pv *pkgVerifier) hiddenInitCode() string {
	bodies := map[*types.Func]*ast.FuncDecl{}
	values := map[*types.Var]ast.Expr{}
	var initialisers []ast.Expr
	for _, file := range pv.pass.Files {
		for _, decl := range file.Decls {
			switch decl := decl.(type) {
			case *ast.FuncDecl:
				if fn, ok := pv.info.Defs[decl.Name].(*types.Func); ok {
					bodies[fn] = decl
				}
			case *ast.GenDecl:
				for _, spec := range decl.Specs {
					if spec, ok := spec.(*ast.ValueSpec); ok && decl.Tok == token.VAR {
						initialisers = append(initialisers, spec.Values...)
						for i, name := range spec.Names {
							if variable, ok := pv.info.Defs[name].(*types.Var); ok && len(spec.Values) > 0 {
								values[variable] = spec.Values[min(i, len(spec.Values)-1)]
							}
						}
					}
				}
			}
		}
	}
	at := func(pos token.Pos, what string) string {
		position := pv.pass.Fset.Position(pos)
		return fmt.Sprintf("%s at %s:%d", what, filepath.Base(position.Filename), position.Line)
	}
	// named returns the package-level variable or the function that an
	// expression names, if it names one.
	named := func(e ast.Expr) types.Object {
		e = ast.Unparen(e)
		if sel, ok := e.(*ast.SelectorExpr); ok && pv.info.Selections[sel] == nil {
			e = sel.Sel
		}
		id, ok := e.(*ast.Ident)
		if !ok {
			return nil
		}
		switch obj := pv.info.Uses[id].(type) {
		case *types.Func:
			return obj
		case *types.Var:
			if obj.Pkg() != nil && obj.Parent() == obj.Pkg().Scope() {
				return obj
			}
		}
		return nil
	}
	// These hold no code of this package: something whose type has no
	// room for any; a variable of another package and what a function of
	// another package returns, since code of this package gets into the
	// hands of another package only by being handed over, which is itself
	// looked for below; and a variable of this package that is never
	// assigned and was declared with such a value, as a sentinel is.
	visiting := map[*types.Var]bool{}
	var inert func(e ast.Expr) bool
	inert = func(e ast.Expr) bool {
		if pv.codeless(pv.info.TypeOf(e), map[types.Type]bool{}) {
			return true
		}
		if variable, ok := named(e).(*types.Var); ok {
			if variable.Pkg() != pv.pass.Pkg || pv.sentinels[variable] {
				return true
			}
			if values[variable] == nil || pv.reassigned[variable] || visiting[variable] {
				return false
			}
			visiting[variable] = true
			defer delete(visiting, variable)
			return inert(values[variable])
		}
		call, ok := ast.Unparen(e).(*ast.CallExpr)
		if !ok {
			return false
		}
		callee := typeutil.StaticCallee(pv.info, call)
		return callee != nil && callee.Pkg() != pv.pass.Pkg
	}
	seen := map[*types.Func]bool{}
	var scan func(root ast.Node) string
	scan = func(root ast.Node) string {
		found := ""
		ast.Inspect(root, func(n ast.Node) bool {
			if found != "" {
				return false
			}
			switch n := n.(type) {
			case *ast.FuncLit:
				// Writing a function down does not run it. Calling it, or
				// handing it to another package, is seen where that
				// happens.
				return false
			case *ast.GoStmt:
				found = at(n.Pos(), "a goroutine is started")
			case *ast.AssignStmt:
				// What is put into a variable of another package, or into
				// anything but a plain variable, which may be memory that
				// another package can reach, may be called from there.
				for i, lhs := range n.Lhs {
					value := n.Rhs[min(i, len(n.Rhs)-1)]
					_, plain := ast.Unparen(lhs).(*ast.Ident)
					variable, isVariable := named(lhs).(*types.Var)
					if (isVariable && variable.Pkg() != pv.pass.Pkg) || (!plain && !inert(value)) {
						found = at(lhs.Pos(), fmt.Sprintf("%s is assigned, which another package may read", types.ExprString(lhs)))
					}
				}
			case *ast.SendStmt:
				if !inert(n.Value) {
					found = at(n.Pos(), "something of this package is sent on a channel")
				}
			case *ast.RangeStmt:
				// A range clause assigns too.
				for _, target := range []ast.Expr{n.Key, n.Value} {
					if target == nil || n.Tok != token.ASSIGN {
						continue
					}
					_, plain := ast.Unparen(target).(*ast.Ident)
					variable, isVariable := named(target).(*types.Var)
					if (isVariable && variable.Pkg() != pv.pass.Pkg) || (!plain && !pv.codeless(pv.info.TypeOf(target), map[types.Type]bool{})) {
						found = at(target.Pos(), fmt.Sprintf("%s is assigned, which another package may read", types.ExprString(target)))
					}
				}
				// Ranging over a function calls it.
				if !rangesByCalling(pv.info.TypeOf(n.X)) {
					break
				}
				ranged, _ := named(n.X).(*types.Func)
				decl := bodies[ranged]
				switch {
				case ranged == nil || decl == nil || decl.Body == nil:
					found = at(n.X.Pos(), "a function that is not a named function of this package is ranged over")
				case !seen[ranged]:
					seen[ranged] = true
					found = scan(decl.Body)
				}
			case *ast.CallExpr:
				// Some built-in functions pass on what they are given:
				// append and copy may write into an array that another
				// package holds, and panic hands its value to the runtime,
				// which asks it for a text. Those that only measure, make,
				// or remove things do not.
				id, _ := ast.Unparen(n.Fun).(*ast.Ident)
				if builtin, ok := pv.info.Uses[id].(*types.Builtin); ok && id != nil {
					keeps := []string{"len", "cap", "new", "make", "delete", "clear", "min", "max", "real", "imag", "complex", "print", "println", "recover"}
					if !slices.Contains(keeps, builtin.Name()) && slices.ContainsFunc(n.Args, func(arg ast.Expr) bool { return !inert(arg) }) {
						found = at(n.Pos(), fmt.Sprintf("something of this package is handed to %s", builtin.Name()))
					}
				}
				if tv := pv.info.Types[n.Fun]; tv.IsType() || tv.IsBuiltin() {
					break
				}
				callee := typeutil.StaticCallee(pv.info, n)
				switch {
				case callee == nil:
					// A function written out and called on the spot is
					// read like one that has a name.
					if literal, ok := ast.Unparen(n.Fun).(*ast.FuncLit); ok {
						found = scan(literal.Body)
						break
					}
					found = at(n.Pos(), "a function value or an interface method is called")
				case callee.Pkg() == pv.pass.Pkg:
					decl := bodies[callee.Origin()]
					switch {
					case decl == nil || decl.Body == nil:
						found = at(n.Pos(), callee.Name()+", whose body is not available, is called")
					case !seen[callee.Origin()]:
						seen[callee.Origin()] = true
						found = scan(decl.Body)
					}
				default:
					// A type argument can carry code too: the methods of a
					// type of this package.
					for _, argument := range pv.typeArguments(n) {
						if !pv.codeless(argument, map[types.Type]bool{}) {
							found = at(n.Pos(), fmt.Sprintf("the type %s is handed to %s.%s, which may call its methods",
								argument, callee.Pkg().Name(), callee.Name()))
						}
					}
					operands := slices.Clone(n.Args)
					if sel, ok := ast.Unparen(n.Fun).(*ast.SelectorExpr); ok && pv.info.Selections[sel] != nil {
						operands = append(operands, sel.X)
					}
					for _, operand := range operands {
						if !inert(operand) {
							found = at(operand.Pos(), fmt.Sprintf("%s is handed to %s.%s, which may call back into this package",
								types.ExprString(operand), callee.Pkg().Name(), callee.Name()))
							break
						}
					}
				}
			}
			return true
		})
		return found
	}
	for _, initialiser := range initialisers {
		if found := scan(initialiser); found != "" {
			return found
		}
	}
	return ""
}

// codeless reports whether no value of a type can hold code of this
// package: the type has no interface, function, or channel in it, however
// deep, and no type declared in this package, whose methods a value brings
// with it, also not as a type argument.
func (pv *pkgVerifier) codeless(t types.Type, seen map[types.Type]bool) bool {
	if t == nil {
		return false
	}
	if seen[t] {
		return true
	}
	seen[t] = true
	if held, replaced := heldAs(t); replaced {
		return held == nil || pv.codeless(held, seen)
	}
	// A type declared here brings its methods, and a generic type of
	// another package those of the types it is instantiated with.
	if named, ok := types.Unalias(t).(*types.Named); ok {
		if named.Obj().Pkg() == pv.pass.Pkg {
			return false
		}
		for argument := range named.TypeArgs().Types() {
			if !pv.codeless(argument, seen) {
				return false
			}
		}
	}
	switch u := t.Underlying().(type) {
	case *types.Basic:
		return u.Kind() != types.UnsafePointer
	case *types.Pointer:
		return pv.codeless(u.Elem(), seen)
	case *types.Slice:
		return pv.codeless(u.Elem(), seen)
	case *types.Array:
		return pv.codeless(u.Elem(), seen)
	case *types.Map:
		return pv.codeless(u.Key(), seen) && pv.codeless(u.Elem(), seen)
	case *types.Struct:
		for field := range u.Fields() {
			if !pv.codeless(field.Type(), seen) {
				return false
			}
		}
		return true
	}
	return false
}

// typeArguments returns the type arguments a call instantiates its callee
// with, written out or inferred.
func (pv *pkgVerifier) typeArguments(call *ast.CallExpr) []types.Type {
	fun := ast.Unparen(call.Fun)
	switch indexed := fun.(type) {
	case *ast.IndexExpr:
		fun = indexed.X
	case *ast.IndexListExpr:
		fun = indexed.X
	}
	if sel, ok := fun.(*ast.SelectorExpr); ok {
		fun = sel.Sel
	}
	id, ok := fun.(*ast.Ident)
	if !ok {
		return nil
	}
	var arguments []types.Type
	for argument := range pv.info.Instances[id].TypeArgs.Types() {
		arguments = append(arguments, argument)
	}
	return arguments
}

// outcome is what verifying a function established about its failure,
// beyond the diagnostics it produced.
type outcome struct {
	// complete is set when verification ran to the end; the rest is only
	// meaningful then, and only for functions that return an error.
	complete bool
	// forces says whether the contract makes the function succeed for some
	// input: Refuted when Z3 found such an input, Proved when there is
	// none; see forcesSuccess. limited is the limit a question of that
	// search stopped at, if one did.
	forces  solver.Result
	limited solver.Result
	// final, when the search found no input, asks whether any state the
	// logic describes forces success; only the report of a contract that
	// may always fail reads it. See forcesSuccess.
	final func() solver.Result
	// outside is set when execution reached a call without a contract that
	// returns an error; reached holds the verified callees returning an
	// error that it reached.
	outside bool
	reached map[*funcInfo]bool
	// pending, when set, runs the search for an input on which the
	// contract forces success, which was put off because the function
	// reported something of its own; see verified.
	pending func()
}

// settle runs the search that was put off, if it was.
func (o *outcome) settle() {
	if o.pending != nil {
		pending := o.pending
		o.pending = nil
		pending()
	}
}

// verified verifies a function once and records the outcome.
func (pv *pkgVerifier) verified(fn *funcInfo) {
	if _, done := pv.outcomes[fn]; done {
		return
	}
	result := &outcome{}
	pv.outcomes[fn] = result
	pv.current = fn
	defer func() { pv.current = nil }()
	// The searches for inputs while the body is verified, for the
	// exception below, and the one for the contract itself, are what the
	// report of an always-failing contract rests on.
	pv.searchLimit = solver.Unknown
	pv.run(fn, func(v *fnVerifier) {
		v.tracksFailure = len(errorResults(fn)) > 0
		v.verify()
		search := func() {
			result.forces, result.final = v.forcesSuccess()
			result.limited = pv.searchLimit
		}
		tie := func() {
			if v.tieLater {
				v.tieFailures()
			}
			result.outside, result.reached = v.outside, v.reached
		}
		switch {
		case !v.tracksFailure:
			tie()
		case fn.reportedHere:
			// A function that has reported a fault of its own is not
			// judged by the always-fails check until the fault is fixed:
			// its contract will change, and the search, which is the
			// costliest question of the check, rarely finds anything on a
			// function that does not verify. Whether its contract forces
			// success still decides whether a caller that reaches it is
			// excused, so the search is kept, in the state it would have run
			// in, and run only if a caller needs it.
			result.pending = func() {
				defer pv.costing(fn)()
				saved := pv.searchLimit
				pv.searchLimit = solver.Unknown
				tie()
				search()
				pv.searchLimit = saved
			}
		default:
			tie()
			search()
		}
		result.complete = true
	})
}

// reportAlwaysFailing rejects every contract that its function could meet
// by failing on every call. A postcondition of the form "err = nil -> ..."
// alone says what success looks like but never that success happens.
//
// A function is excused when it cannot promise success: its contract forces
// none, and it reaches a call whose failure no contract predicts, either
// directly or through a verified callee that is itself excused. The excused
// functions are the least fixed point of that rule, so a cycle of functions
// that only call each other excuses nobody, and the order of declarations
// does not matter.
func (pv *pkgVerifier) reportAlwaysFailing() map[*funcInfo]bool {
	excused := map[*funcInfo]bool{}
	judged := func(fn *funcInfo) bool {
		result := pv.outcomes[fn]
		return result != nil && result.complete && len(errorResults(fn)) > 0
	}
	// The functions whose contracts are judged are those that reported
	// nothing of their own; whether one is excused depends on the callees
	// it reached, so those are looked at too, and only they settle a search
	// that was put off.
	needed := map[*funcInfo]bool{}
	var pending []*funcInfo
	for _, fn := range pv.order {
		if judged(fn) && !fn.reportedHere {
			needed[fn] = true
			pending = append(pending, fn)
		}
	}
	for len(pending) > 0 {
		fn := pending[len(pending)-1]
		pending = pending[:len(pending)-1]
		pv.outcomes[fn].settle()
		for callee, reached := range pv.outcomes[fn].reached {
			if reached && judged(callee) && !needed[callee] {
				needed[callee] = true
				pending = append(pending, callee)
			}
		}
	}
	candidate := func(fn *funcInfo) bool {
		if !needed[fn] {
			return false
		}
		result := pv.outcomes[fn]
		result.settle()
		return result.forces != solver.Refuted
	}
	for changed := true; changed; {
		changed = false
		for _, fn := range pv.order {
			if !candidate(fn) || excused[fn] {
				continue
			}
			through := slices.ContainsFunc(slices.Collect(maps.Keys(pv.outcomes[fn].reached)), func(callee *funcInfo) bool {
				return pv.outcomes[fn].reached[callee] && excused[callee]
			})
			if pv.outcomes[fn].outside || through {
				excused[fn], changed = true, true
			}
		}
	}
	for _, fn := range pv.order {
		if !fn.reportedHere && candidate(fn) && !excused[fn] {
			fn.failed = true
			// Proved means that no state the logic describes forces success,
			// so no input does; otherwise only the search found none.
			why := "no simple input was found for which it forces success" + limitNote(pv.outcomes[fn].limited)
			advice := "where the condition is about the inputs and a small input satisfies it"
			// The question forcesSuccess left counts against the
			// function, its time included.
			none := false
			if final := pv.outcomes[fn].final; final != nil {
				done := pv.costing(fn)
				none = final() == solver.Proved
				done()
			}
			if none {
				why, advice = "it requires success for no input", "where the condition is about the inputs"
			}
			pv.report(fn.decl.Name.Pos(), "the contract of %s may also be met by a function that always returns an error: %s; "+
				"state when it succeeds with a clause such as \"condition -> err = nil\", %s", fn.obj.Name(), why, advice)
		}
	}
	return excused
}

// trustForces reports whether a trusted contract forces success for some
// input. One that does not is a source of unpredictable failure: nothing
// says when the function succeeds.
func (pv *pkgVerifier) trustForces(fn *funcInfo) bool {
	if fn.forces != nil {
		return *fn.forces
	}
	forces := false
	fn.forces = &forces
	// The contract is examined on its own; parts of the signature of types
	// vego does not model take no part in it.
	pv.run(fn, func(v *fnVerifier) {
		v.lenient = true
		// Whether no state forces success is not asked: only whether
		// some input does is read here.
		found, _ := v.forcesSuccess()
		forces = found == solver.Refuted
	})
	if fn.use != nil && len(errorResults(fn)) > 0 {
		fn.use.Unpredictable = !forces
	}
	return forces
}

// errorResults returns the indices of the results of type error.
func errorResults(fn *funcInfo) []int {
	var indices []int
	for i, result := range fn.results {
		if sort, ok := sortOf(result.Type()); ok && sort == logic.Err {
			indices = append(indices, i)
		}
	}
	return indices
}

// contractInstance resolves the contract on the state a function is entered
// in. It returns the facts of that state, which are what the precondition
// and the types of the parameters give; everything that then holds after
// any function meeting the contract has run, namely what the types of its
// outputs guarantee and the postcondition; and the terms standing for the
// error results.
func (v *fnVerifier) contractInstance(entry *state) (pre, post, failures []*logic.Term) {
	fn := v.fn
	st := entry.clone()
	for _, t := range v.frame {
		// What the footprint of an interface value an owner owns holds
		// is memory the contract cannot name. Forgetting it starts an
		// epoch, which makes every region an unknown of the outcome, and
		// the always-fails search over every such outcome is what Z3 gives
		// up on. Keeping it only narrows the outcomes, which can make the
		// check find success forced where it is not, and a contradiction
		// where there is none: both are reported, never hidden.
		if t.part && t.fp {
			continue
		}
		v.havoc(st, t, nil)
	}
	st.brk = v.fresh("brk", logic.Ref)
	st.assume(logic.Le(entry.brk, st.brk))
	results := make([]value, len(fn.results))
	for i, result := range fn.results {
		if _, ok := layoutOf(result.Type()); ok {
			results[i] = v.unknown("out", result.Type(), st)
			st.assume(v.deepFacts(st.mem, results[i], result.Type(), st.brk))
		}
	}
	// What the types say of the parameters in memory on return matters,
	// beyond what they say in memory on entry, only to an Ensures that
	// reads the memory on return. A contract that writes a footprint makes
	// every region unknown on return, and Z3 gives up on a question over
	// them; without such a clause its facts are stated in memory on entry,
	// which is part of the input, and each is true there.
	stated := st.mem
	if !primedEnsures(fn) && slices.ContainsFunc(v.frame, func(t target) bool { return t.fp || t.part }) {
		stated = memory{}
	}
	for _, param := range fn.params {
		if v.entry[param] != nil {
			typed := v.deepFacts(stated, v.entry[param], param.Type(), st.brk)
			v.typing[typed] = true
			st.assume(typed)
		}
	}
	env := &specEnv{v: v, sink: st, fn: fn, args: v.entry, results: results, now: memory{}, post: st.mem, before: entry.brk}
	for _, c := range fn.ensures {
		// A clause about a result that has no value in the logic says
		// nothing here.
		st.assume(v.calleeFormula(c, env))
	}
	// A verified function also keeps the invariants of what it hands back.
	if fn.trust == nil {
		for _, param := range fn.params {
			if v.entry[param] != nil {
				v.assumeInvariants(st, nil, st.mem, v.entry[param], param.Type(), "")
			}
		}
		for i, result := range fn.results {
			if results[i] != nil {
				v.assumeInvariants(st, nil, st.mem, results[i], result.Type(), "")
			}
		}
	}
	for _, index := range errorResults(fn) {
		failures = append(failures, results[index][0])
	}
	return entry.hyps, st.hyps, failures
}

// maxShapes bounds the shapes of input tried when looking for one on which
// a contract forces success or a path is reached, and maxRounds the
// candidates Z3 proposes for one shape.
const (
	maxShapes = 32
	maxRounds = 4
)

// maxSampleDepth is how many pointers a sample follows from a parameter,
// and maxSampleLen the greatest length of a sampled slice or string.
const (
	maxSampleDepth = 2
	maxSampleLen   = 4096
)

// forcesSuccess decides whether the contract makes the function succeed for
// some input: some state on entry satisfies the precondition, and from it
// every outcome that meets the postcondition has a nil error. Without such
// an input, an implementation that fails on every call may well satisfy
// the contract, whatever else the contract demands.
//
// It returns Refuted when it found such an input, which is a concrete input
// that someInput builds and for which both facts are proved. Otherwise it
// returns Unknown and a function that asks the further question: it returns
// Proved when not even the states the logic describes, which include every
// input Go has, contain one, and the outcome of that question when Z3 could
// not settle it. The further question is the costliest of the check and
// only decides the wording of a report, so it is asked only for a contract
// that is reported. One input has to force every error result to be nil: a
// function with two of them succeeds only when both are, and inputs that
// each force one of them say nothing about that.
func (v *fnVerifier) forcesSuccess() (solver.Result, func() solver.Result) {
	defer v.asking(failureCheck)()
	entry := v.enter()
	pre, post, failures := v.contractInstance(entry)
	nils := make([]*logic.Term, len(failures))
	for i, failure := range failures {
		nils[i] = logic.IsNil(failure)
	}
	// The sample errors are the samples that are not literals; all that
	// is known of them is that they are not nil and differ from each other.
	known := v.knownFacts()
	forced := func(input *witness) *logic.Term {
		return logic.And(logic.And(input.apply(pre)...), logic.Implies(logic.And(input.apply(post)...), logic.And(input.apply(nils)...)))
	}
	// The search asks for values of the sample under which the body holds
	// for every outcome, first with the parts of the entry state that the
	// sample leaves open left to Z3, which is the easier question, and then
	// for every value of those too, as the proofs that accept a sample ask.
	found := v.someInput(post, func(input *witness) ([]*logic.Term, [][]*logic.Term) {
		body := forced(input)
		return []*logic.Term{body}, [][]*logic.Term{v.produced(body), v.unsampled(body)}
	}, func(input *witness) bool {
		known := input.fixedOnly().apply(known)
		if !v.proves(known, logic.And(input.apply(pre)...), 0) {
			return false
		}
		outcome := append(slices.Clip(known), input.apply(post)...)
		return !slices.ContainsFunc(input.apply(nils), func(none *logic.Term) bool { return !v.proves(outcome, none, 0) })
	})
	if found {
		return solver.Refuted, nil
	}
	// Every input satisfies what its types guarantee in full, which the
	// facts of the entry state only say of what the contract reads.
	var wellFormed []*logic.Term
	for _, param := range v.fn.params {
		if v.entry[param] != nil {
			wellFormed = append(wellFormed, v.deepFacts(entry.mem, v.entry[param], param.Type(), entry.brk))
		}
	}
	body := logic.And(logic.And(wellFormed...), forced(&witness{consts: map[string]*logic.Term{}, memo: map[*logic.Term]*logic.Term{}}))
	opts := v.options(0, failureCheck)
	opts.Forall = v.produced(body)
	facts := append(known, body)
	return solver.Unknown, func() solver.Result {
		if result := v.solver().Check(facts, opts); result != solver.Refuted {
			return result
		}
		return solver.Unknown
	}
}

// sampleErrors are the values a sample gives to errors that are not nil.
// They are different errors, as different calls of errors.New make, so
// that a sample can hold two errors that differ as well as two that are
// the same.
var sampleErrors = func() []*logic.Term {
	errs := make([]*logic.Term, maxSampleErrors)
	for i := range errs {
		errs[i] = logic.Const(fmt.Sprintf("%s%d", sampleErrorName, i), logic.Err)
	}
	return errs
}()

// sampleErrorName begins the names of the sample errors, and
// maxSampleErrors is how many there are.
const (
	sampleErrorName = "some error "
	maxSampleErrors = 6
)

// isSampleError reports whether a term is one of the sample errors.
func isSampleError(t *logic.Term) bool {
	return t.Op == logic.OpConst && t.Sort == logic.Err && strings.HasPrefix(t.Name, sampleErrorName)
}

// sampleErrorFacts states what is known of the sample errors: none is nil,
// and no two are the same. Distinct errors made by errors.New are a Go
// input with these properties.
func sampleErrorFacts() []*logic.Term {
	var facts []*logic.Term
	for i, e := range sampleErrors {
		facts = append(facts, logic.Not(logic.IsNil(e)))
		for _, other := range sampleErrors[:i] {
			facts = append(facts, logic.Not(logic.Eq(e, other)))
		}
	}
	return facts
}

// produced returns the constants of a formula that do not stand for the
// state on entry or for part of a sample, in the order they occur.
func (v *fnVerifier) produced(t *logic.Term) []*logic.Term {
	var found []*logic.Term
	seen := map[*logic.Term]bool{}
	names := map[string]bool{}
	var walk func(t *logic.Term)
	walk = func(t *logic.Term) {
		if seen[t] {
			return
		}
		seen[t] = true
		if t.Op == logic.OpConst && !v.isInput(t) && !isSampleError(t) && !names[t.Name] {
			names[t.Name] = true
			found = append(found, t)
		}
		for _, arg := range t.Args {
			walk(arg)
		}
	}
	walk(t)
	return found
}

// unsampled returns the constants of a formula other than those of a
// sample, the sample errors, sentinels, and nil.
func (v *fnVerifier) unsampled(t *logic.Term) []*logic.Term {
	var found []*logic.Term
	seen := map[*logic.Term]bool{}
	names := map[string]bool{}
	var walk func(t *logic.Term)
	walk = func(t *logic.Term) {
		if seen[t] {
			return
		}
		seen[t] = true
		if t.Op == logic.OpConst && t != logic.NilErr() && !isSampleError(t) && !isFixedTerm(t) && !strings.HasPrefix(t.Name, sampleName) && !names[t.Name] {
			names[t.Name] = true
			found = append(found, t)
		}
		for _, arg := range t.Args {
			walk(arg)
		}
	}
	walk(t)
	return found
}

// isInput reports whether a constant stands for part of the state on
// entry, a parameter or the memory, or for part of a sample of it, or is
// the nil error, a sentinel, or another package-level variable that keeps
// its value, which are the same for every input.
func (v *fnVerifier) isInput(t *logic.Term) bool {
	return t == logic.NilErr() || isFixedTerm(t) || v.inputs[t.Name] || strings.HasPrefix(t.Name, entryRegion) || strings.HasPrefix(t.Name, sampleName)
}

// canReach reports whether there is evidence that execution can arrive at
// the current point, given the facts that hold on the path to it. A path
// that is provably impossible cannot. Beyond that, the facts that speak
// about the inputs alone must be satisfied together by some concrete input;
// failing to refute them is not enough. Facts that depend on values the
// verifier treats as unknown, such as the result of an earlier call or the
// state after a loop, have no such witness and are taken as possible unless
// refuted, so this is an over-approximation for such paths.
func (v *fnVerifier) canReach(path []*logic.Term) bool {
	if v.contradictory(path) {
		return false
	}
	// What must hold on the path is split into its necessary parts, so that
	// a condition on the inputs is found even inside a conjunction with
	// something unknown. Those parts must be proved for a concrete input,
	// and under the same input the path as a whole must not be refutable.
	var required []*logic.Term
	for _, fact := range path {
		for _, part := range necessary(fact) {
			if v.inputsOnly(part) {
				required = append(required, part)
			}
		}
	}
	known := v.knownFacts()
	// A sample gives a home only to the interface values of the input, and
	// every other reference the home of one of them, which is not what a
	// value that a call made after entry has: a contract that says such a
	// value is new, as fresh(result) does, would contradict it. So the
	// facts that read the home of a reference that is not the input's are
	// left out where a sample is applied; that can only make the path more
	// likely to be reached, which is the side this check errs on.
	var sampled []*logic.Term
	for _, fact := range path {
		if !v.readsLaterHome(fact) {
			sampled = append(sampled, fact)
		}
	}
	return v.someInput(path, func(input *witness) ([]*logic.Term, [][]*logic.Term) {
		return append(input.apply(required), input.apply(sampled)...), [][]*logic.Term{nil}
	}, func(input *witness) bool {
		known := input.fixedOnly().apply(known)
		return v.proves(known, logic.And(input.apply(required)...), 0) &&
			!v.contradictory(append(slices.Clip(known), input.apply(sampled)...))
	})
}

// readsLaterHome reports whether a term reads the home of an interface
// value whose reference is not one of the input; see canReach.
func (v *fnVerifier) readsLaterHome(t *logic.Term) bool {
	if t.Op == logic.OpSelect && t.Args[0].Op == logic.OpConst && t.Args[0].Name == homes.Name && !v.inputsOnly(t.Args[1]) {
		return true
	}
	return slices.ContainsFunc(t.Args, v.readsLaterHome)
}

// inputsOnly reports whether a formula mentions nothing but the state on
// entry.
func (v *fnVerifier) inputsOnly(t *logic.Term) bool {
	if t.Op == logic.OpConst && !v.isInput(t) {
		return false
	}
	return !slices.ContainsFunc(t.Args, func(arg *logic.Term) bool { return !v.inputsOnly(arg) })
}

// necessary splits a formula into formulas that must each hold whenever it
// does: the conjuncts of a conjunction, and what the negation of a
// disjunction or of an implication entails.
func necessary(t *logic.Term) []*logic.Term {
	var parts []*logic.Term
	switch {
	case t.Op == logic.OpAnd:
		for _, arg := range t.Args {
			parts = append(parts, necessary(arg)...)
		}
	case t.Op == logic.OpNot && t.Args[0].Op == logic.OpOr:
		for _, arg := range t.Args[0].Args {
			parts = append(parts, necessary(logic.Not(arg))...)
		}
	case t.Op == logic.OpNot && t.Args[0].Op == logic.OpImplies:
		parts = append(necessary(t.Args[0].Args[0]), necessary(logic.Not(t.Args[0].Args[1]))...)
	default:
		parts = []*logic.Term{t}
	}
	return parts
}

// witness is an input: values for the constants that stand for the
// parameters, and contents for the memory they refer to. Applying it to a
// formula about the state on entry gives the formula for that one input.
// While it is being searched for, its numbers, booleans, and some of its
// choices are constants that Z3 picks; see sampler.
type witness struct {
	consts map[string]*logic.Term
	memo   map[*logic.Term]*logic.Term
	// fixed holds the arrays whose sampled contents are a literal, which
	// the sample for single elements must then leave alone.
	fixed map[string]bool
}

// store sets one cell of a region of the sampled memory.
func (s *witness) store(key string, sort logic.Sort, ref, written *logic.Term) {
	name := entryRegion + key
	region, ok := s.consts[name]
	if !ok {
		region = logic.Const(name, sort)
	}
	s.consts[name] = logic.Store(region, ref, written)
}

// storeAt sets one position of one allocation in a region of the sampled
// memory.
func (s *witness) storeAt(c cell, ref, written *logic.Term) {
	name := entryRegion + c.key
	region, ok := s.consts[name]
	if !ok {
		region = logic.Const(name, logic.SeqOf(logic.SeqOf(c.sort)))
	}
	row := logic.Store(logic.Select(region, ref), logic.IntLit(c.off), written)
	s.consts[name] = logic.Store(region, ref, row)
}

// apply replaces the constants of the entry state by their sampled values.
func (s *witness) apply(terms []*logic.Term) []*logic.Term {
	var replace func(t *logic.Term) *logic.Term
	replace = func(t *logic.Term) *logic.Term {
		if t.Op == logic.OpConst {
			if replacement, ok := s.consts[t.Name]; ok {
				return replacement
			}
			return t
		}
		if len(t.Args) == 0 {
			return t
		}
		if done, ok := s.memo[t]; ok {
			return done
		}
		args := make([]*logic.Term, len(t.Args))
		changed := false
		for i, arg := range t.Args {
			args[i] = replace(arg)
			changed = changed || args[i] != arg
		}
		result := t
		switch {
		case changed && t.Op == logic.OpIsNil:
			// Whether the nil error is nil is decided where the term is
			// built.
			result = logic.IsNil(args[0])
		case changed:
			result = logic.WithArgs(t, args)
		}
		s.memo[t] = result
		return result
	}
	replaced := make([]*logic.Term, len(terms))
	for i, t := range terms {
		replaced[i] = replace(t)
	}
	return replaced
}

// fixedOnly returns the part of the witness that gives values to
// package-level variables. What is known of every input speaks of them as
// of the constants they are, and a sample replaces those.
func (s *witness) fixedOnly() *witness {
	only := &witness{consts: map[string]*logic.Term{}, memo: map[*logic.Term]*logic.Term{}}
	for name, t := range s.consts {
		if strings.HasPrefix(name, fixedName) {
			only.consts[name] = t
		}
	}
	return only
}

// bind returns the witness with the constants of the sample replaced by
// the given values.
func (s *witness) bind(values map[string]*logic.Term) *witness {
	with := &witness{consts: values, memo: map[*logic.Term]*logic.Term{}}
	bound := &witness{consts: map[string]*logic.Term{}, memo: map[*logic.Term]*logic.Term{}, fixed: s.fixed}
	for name, t := range s.consts {
		bound.consts[name] = with.apply([]*logic.Term{t})[0]
	}
	return bound
}

// slot is one independent choice of shape in a sample: each of its
// alternatives fills in part of the sample.
type slot []func(s *witness)

// sampleName begins the names of the constants that stand for the numbers
// and booleans of a sample.
const sampleName = "sample "

// sampler lists the slots for the inputs of a function. A sample has a
// shape chosen among the alternatives of the slots: each pointer is nil or
// refers to an object of its own, each slice has an array of its own whose
// elements are all alike or a literal the formulas mention, each map is
// nil or has a single key. Its numbers, booleans, and lengths, and whether
// an error is nil, are constants that Z3 picks, each within the range of
// its type, so that every value Z3 picks makes the sample an input Go has.
type sampler struct {
	v        *fnVerifier
	slots    []slot
	literals []*logic.Term
	// mentioned holds the names of the constants that occur in the formulas
	// the samples are for, other than in what the types alone guarantee.
	mentioned map[string]bool
	// refs counts the objects and arrays the samples contain, each of which
	// gets a reference of its own.
	refs int64
	// vars are the constants of the samples, and facts the ranges their
	// types give them.
	vars  []*logic.Term
	facts []*logic.Term
	// errs counts the leaves of type error sampled so far, and sentinels
	// holds the sentinels the formulas mention, which a leaf may hold.
	errs      int
	sentinels []*logic.Term
	// homes holds the home of each reference of an interface value of a
	// sample with states, and under 0 the one home of every other
	// reference; see ifacestate.go.
	homes map[int64]*logic.Term
}

// number returns a new constant for a number of an integer type.
func (b *sampler) number(t types.Type) *logic.Term {
	c := logic.Const(fmt.Sprintf("%s%d", sampleName, len(b.vars)), logic.Int)
	b.vars = append(b.vars, c)
	if lo, hi, ok := b.v.intRange(t); ok {
		b.facts = append(b.facts, logic.Le(logic.BigLit(lo), c), logic.Le(c, logic.BigLit(hi)))
	}
	return c
}

// within returns a new constant for a number from lo to hi.
func (b *sampler) within(lo, hi int64) *logic.Term {
	c := logic.Const(fmt.Sprintf("%s%d", sampleName, len(b.vars)), logic.Int)
	b.vars = append(b.vars, c)
	b.facts = append(b.facts, logic.Le(logic.IntLit(lo), c), logic.Le(c, logic.IntLit(hi)))
	return c
}

// boolean returns a new constant for a boolean.
func (b *sampler) boolean() *logic.Term {
	c := logic.Const(fmt.Sprintf("%s%d", sampleName, len(b.vars)), logic.Bool)
	b.vars = append(b.vars, c)
	return c
}

// failure returns an error for one leaf of a sample, as a number constant
// decides: nil, a sample error of its own, the sample error of an earlier
// leaf, so that two leaves can hold different errors or the same, or a
// sentinel the formulas mention. Leaves past the number of sample errors
// have only the choices of the last one.
func (b *sampler) failure() *logic.Term {
	own := min(b.errs, maxSampleErrors-1)
	b.errs++
	choices := append([]*logic.Term{logic.NilErr()}, sampleErrors[:own+1]...)
	choices = append(choices, b.sentinels...)
	choice := b.within(0, int64(len(choices)-1))
	chosen := choices[len(choices)-1]
	for i := len(choices) - 2; i >= 0; i-- {
		chosen = logic.Ite(logic.Eq(choice, logic.IntLit(int64(i))), choices[i], chosen)
	}
	return chosen
}

// text returns a sample string: a run of one byte, of some length.
func (b *sampler) text() *logic.Term {
	return logic.Fill(b.within(0, maxSampleLen), b.number(types.Typ[types.Uint8]))
}

// texts returns the sample strings: a run of one byte, and the literals the
// formulas mention whose elements are bytes.
func (b *sampler) texts() []*logic.Term {
	values := []*logic.Term{b.text()}
	for _, literal := range b.literals {
		if literal.Sort == logic.IntSeq && b.v.proves(nil, b.v.elementFacts(literal, types.Typ[types.Uint8]), 0) {
			values = append(values, literal)
		}
	}
	return values
}

// scalarOf returns a sample for a single value of a type, or nil if it has
// none.
func (b *sampler) scalarOf(t types.Type) *logic.Term {
	sort, single := sortOf(t)
	switch {
	case isString(t):
		return b.text()
	case single && sort == logic.Int:
		return b.number(t)
	case single && sort == logic.Bool:
		return b.boolean()
	case single && sort == logic.Err:
		return b.failure()
	}
	return nil
}

// binding says how the leaves of a sampled value are filled in, and under
// which name each is known to the formulas: the constant of a parameter, or
// the region of memory a field lives in.
type binding struct {
	set  func(s *witness, leaf int, term *logic.Term)
	name func(leaf int) string
}

// choose adds a slot. A slot for something the formulas never mention would
// multiply the samples without changing what any of them proves, so it keeps
// its first alternative only.
func (b *sampler) choose(alternatives slot, names ...string) {
	if !slices.ContainsFunc(names, func(name string) bool { return b.mentioned[name] }) {
		alternatives = alternatives[:min(len(alternatives), 1)]
	}
	b.slots = append(b.slots, alternatives)
}

// add creates the slots for a value of type t. A pointer is nil or refers to
// an object of its own, whose fields are sampled in turn. depth counts the
// pointers followed to reach the value; beyond maxSampleDepth of them a
// pointer stays nil, so that samples stay small and a type that refers to
// itself has an end. A value no sample exists for stays symbolic.
func (b *sampler) add(t types.Type, to binding, depth int) {
	scalar := func(choices []*logic.Term) {
		var alternatives slot
		for _, choice := range choices {
			alternatives = append(alternatives, func(s *witness) { to.set(s, 0, choice) })
		}
		b.choose(alternatives, to.name(0))
	}
	object, isPointer := pointee(t)
	sort, single := sortOf(t)
	switch {
	case isPointer:
		// A pointer is nil or points to a struct in an allocation of its
		// own.
		pointTo := func(ref *logic.Term) func(s *witness) {
			return func(s *witness) {
				to.set(s, 0, ref)
				to.set(s, 1, logic.IntLit(0))
			}
		}
		if depth >= maxSampleDepth {
			b.slots = append(b.slots, slot{pointTo(logic.RefLit(0))})
			break
		}
		b.refs++
		ref := logic.RefLit(b.refs)
		b.choose(slot{pointTo(ref), pointTo(logic.RefLit(0))}, to.name(0))
		cells := b.v.cellsOf(object)
		b.add(object, binding{
			set:  func(s *witness, i int, term *logic.Term) { s.storeAt(cells[i], ref, term) },
			name: func(i int) string { return entryRegion + cells[i].key },
		}, depth+1)
	case isSlice(t):
		b.addSlice(t, to)
	case isMap(t):
		b.addMap(t, to, depth)
	case isString(t):
		scalar(b.texts())
	case isIface(t):
		// An interface value is nil or not, and has a home.
		b.addStates(t, to)
	case holdsCodeRef(t):
		// A function value is nil or not, and nothing else is known of
		// it.
		scalar([]*logic.Term{logic.RefLit(0), logic.RefLit(1)})
	case single && sort != logic.Float:
		scalar([]*logic.Term{b.scalarOf(t)})
	case single:
		// A float has no concrete values in the logic.
	default:
		u, isStruct := t.Underlying().(*types.Struct)
		if !isStruct {
			return
		}
		for i := range u.NumFields() {
			lo, _, ok := fieldLeaves(t, i)
			if ok {
				b.add(u.Field(i).Type(), binding{
					set:  func(s *witness, j int, term *logic.Term) { to.set(s, lo+j, term) },
					name: func(j int) string { return to.name(lo + j) },
				}, depth)
			}
		}
		// The states of the struct come after its fields; those of a
		// struct in a field were given slots with the field.
		leaves, _ := layoutOf(t)
		decls := statesOf(u)
		for i := range decls {
			at, choice := len(leaves)-len(decls)+i, b.boolean()
			b.choose(slot{func(s *witness) { to.set(s, at, choice) }}, to.name(at))
		}
	}
}

// addStates creates the slot for an interface value with states: nil, or
// a reference of its own, whose home is its own too, so that a sample can
// meet the fact that parameters have homes of their own. Each state there
// gets a value that Z3 chooses. Every other reference, which an interface
// value without states has, gets one home that exists.
func (b *sampler) addStates(t types.Type, to binding) {
	if b.homes == nil {
		b.refs++
		b.homes = map[int64]*logic.Term{0: logic.RefLit(b.refs)}
		b.slots = append(b.slots, slot{func(s *witness) {
			table := logic.Fill(logic.IntLit(0), b.homes[0])
			for _, ref := range slices.Sorted(maps.Keys(b.homes)) {
				if ref != 0 {
					table = logic.Store(table, logic.RefLit(ref), b.homes[ref])
				}
			}
			s.consts[homes.Name] = table
		}})
	}
	if !b.v.hasStates(t) {
		b.choose(slot{func(s *witness) { to.set(s, 0, logic.RefLit(0)) }, func(s *witness) { to.set(s, 0, logic.RefLit(1)) }}, to.name(0))
		return
	}
	b.refs++
	own := logic.RefLit(b.refs)
	b.homes[b.refs] = own
	var states []func(s *witness)
	for _, state := range b.v.ifaceStatesOf(t) {
		choice, position := b.boolean(), state.position()
		states = append(states, func(s *witness) {
			name := entryRegion + stateRegion
			region, ok := s.consts[name]
			if !ok {
				region = logic.Const(name, logic.SeqOf(logic.BoolSeq))
			}
			s.consts[name] = logic.Store(region, own, logic.Store(logic.Select(region, own), position, choice))
		})
	}
	b.choose(slot{
		func(s *witness) {
			to.set(s, 0, own)
			for _, set := range states {
				set(s)
			}
		},
		func(s *witness) { to.set(s, 0, logic.RefLit(0)) },
	}, to.name(0), entryRegion+stateRegion)
}

// addSlice creates the slots for a slice: one for its length, and one for
// each leaf of its elements, which every element of a sample shares. The
// slice gets an array of its own. For a slice of single values the literals
// the formulas mention are offered as contents too.
func (b *sampler) addSlice(t types.Type, to binding) {
	elem := elemType(t)
	leaves, ok := layoutOf(elem)
	if !ok {
		return
	}
	b.refs++
	ref := logic.RefLit(b.refs)
	cells := b.v.cellsOf(elem)
	// Slices of one element type share their regions, so what a literal
	// fixes is one array in a region.
	array := func(i int) string { return cells[i].key + "@" + ref.String() }
	names := []string{to.name(0), to.name(1), to.name(2), to.name(3)}
	for _, c := range cells {
		names = append(names, entryRegion+c.key)
	}
	sized := func(length *logic.Term, also func(s *witness)) func(s *witness) {
		return func(s *witness) {
			for i, part := range []*logic.Term{ref, logic.IntLit(0), length, length} {
				to.set(s, i, part)
			}
			also(s)
		}
	}
	lengths := slot{sized(b.within(0, maxSampleLen), func(*witness) {})}
	if b.mentioned[names[3]] && b.v.namedInFormulas[names[3]] {
		// A slice whose capacity a formula names, as in cap(A), may have
		// more capacity than length, as one made with make or cut with
		// s[:n] has.
		length, spare := b.within(0, maxSampleLen), b.within(0, maxSampleLen)
		lengths = append(lengths, func(s *witness) {
			for i, part := range []*logic.Term{ref, logic.IntLit(0), length, logic.Add(length, spare)} {
				to.set(s, i, part)
			}
		})
	}
	if b.mentioned[names[0]] && b.v.namedInFormulas[names[0]+" = nil"] {
		// A slice that a formula compares with nil may be nil.
		lengths = append(lengths, func(s *witness) {
			for i := range 4 {
				to.set(s, i, map[bool]*logic.Term{true: logic.RefLit(0), false: logic.IntLit(0)}[i == 0])
			}
		})
	}
	if sort, single := sortOf(elem); single {
		for _, literal := range b.literals {
			if literal.Sort == logic.SeqOf(sort) && b.v.proves(nil, b.v.elementFacts(literal, elem), 0) {
				lengths = append(lengths, sized(logic.Len(literal), func(s *witness) {
					s.store(cells[0].key, logic.SeqOf(literal.Sort), ref, literal)
					s.fixed[array(0)] = true
				}))
			}
		}
	}
	b.choose(lengths, names...)
	for i, lf := range leaves {
		var element *logic.Term
		switch {
		case lf.part == partRef && (b.v.namedInFormulas[entryRegion+cells[i].key+" = nil"] || b.v.namedInFormulas[entryRegion+cells[i+3].key]):
			// A slice inside an element is left open, as every slice inside
			// an element is. When a formula compares it with nil it may also
			// be nil in every element, and when a formula names its
			// capacity it may also be, in every element, a slice of an
			// array of its own with more capacity than length.
			parts := func(s *witness, values ...*logic.Term) {
				for j, c := range cells[i : i+4] {
					if !s.fixed[array(i+j)] {
						row := logic.Fill(logic.IntLit(maxSampleLen), values[j])
						s.store(c.key, logic.SeqOf(row.Sort), ref, row)
					}
				}
			}
			alternatives := slot{func(*witness) {}}
			if b.v.namedInFormulas[entryRegion+cells[i].key+" = nil"] {
				alternatives = append(alternatives, func(s *witness) {
					parts(s, logic.RefLit(0), logic.IntLit(0), logic.IntLit(0), logic.IntLit(0))
				})
			}
			if b.v.namedInFormulas[entryRegion+cells[i+3].key] {
				b.refs++
				inner, length, spare := logic.RefLit(b.refs), b.within(0, maxSampleLen), b.within(0, maxSampleLen)
				alternatives = append(alternatives, func(s *witness) {
					parts(s, inner, logic.IntLit(0), length, logic.Add(length, spare))
				})
			}
			b.choose(alternatives, entryRegion+cells[i].key, entryRegion+cells[i+3].key)
			continue
		case lf.part != partValue && lf.part != partState:
			// A slice or a pointer inside an element has no sample.
			continue
		case lf.sort == logic.Int:
			element = b.number(lf.typ)
		case lf.sort == logic.Bool:
			element = b.boolean()
		case lf.sort == logic.Err:
			element = b.failure()
		case lf.sort == logic.Ref:
			element = logic.RefLit(0)
		case lf.sort.IsSeq():
			element = b.text()
		default:
			continue
		}
		fill := func(s *witness) {
			if !s.fixed[array(i)] {
				// Every position holds the element, so the row serves
				// whatever length the slice has.
				row := logic.Fill(logic.IntLit(maxSampleLen), element)
				s.store(cells[i].key, logic.SeqOf(row.Sort), ref, row)
			}
		}
		b.choose(slot{fill}, entryRegion+cells[i].key)
	}
}

// addMap creates the slot for a map: the nil map, or a map of its own with
// a single key. A value that is a pointer points to an object of its own,
// which counts as one more pointer followed, or is nil; beyond
// maxSampleDepth it is nil.
func (b *sampler) addMap(t types.Type, to binding, depth int) {
	keyType, elem := mapParts(t)
	b.refs++
	ref := logic.RefLit(b.refs)
	region := func(lf leaf) (string, logic.Sort) { return mapOwner(t) + lf.path, logic.SeqOf(logic.SeqOf(lf.sort)) }
	alternatives := slot{func(s *witness) { to.set(s, 0, logic.RefLit(0)) }}
	key := b.scalarOf(keyType)
	leaves, _ := layoutOf(elem)
	_, single := sortOf(elem)
	held := b.scalarOf(elem)
	// A value of several parts has a number of its own for each of its
	// numbers, and everything else in it is zero.
	numbers := make([]*logic.Term, len(leaves))
	if !single {
		for i, lf := range leaves {
			if _, _, isInt := b.v.intRange(lf.typ); isInt && lf.part == partValue && lf.sort == logic.Int {
				numbers[i] = b.number(lf.typ)
			}
		}
	}
	// A pointer in a map points to an object of its own, whose fields are
	// sampled like those of any other, or is nil.
	object, isPointer := pointee(elem)
	variants := 1
	var pointed *logic.Term
	if isPointer && depth < maxSampleDepth {
		b.refs++
		pointed = logic.RefLit(b.refs)
		variants = 2
		cells := b.v.cellsOf(object)
		b.add(object, binding{
			set:  func(s *witness, i int, term *logic.Term) { s.storeAt(cells[i], pointed, term) },
			name: func(i int) string { return entryRegion + cells[i].key },
		}, depth+1)
	}
	if key != nil && (!single || held != nil || isPointer) {
		for variant := range variants {
			alternatives = append(alternatives, func(s *witness) {
				to.set(s, 0, ref)
				hasKey, hasSort := region(hasLeaf)
				s.store(mapOwner(t)+countLeaf.path, logic.SeqOf(logic.Int), ref, logic.IntLit(1))
				s.store(hasKey, hasSort, ref, logic.Store(logic.Fill(logic.IntLit(0), logic.False()), mapKey(key), logic.True()))
				for i, lf := range leaves {
					val := zeroLeaf(lf)
					switch {
					case pointed != nil && variant == 0 && lf.part == partPtr:
						val = pointed
					case pointed != nil:
					case single && held != nil:
						val = held
					case numbers[i] != nil:
						val = numbers[i]
					}
					inMap := lf
					inMap.path = "#val" + lf.path
					valKey, valSort := region(inMap)
					s.store(valKey, valSort, ref, logic.Store(logic.Fill(logic.IntLit(0), zeroLeaf(lf)), mapKey(key), val))
				}
			})
		}
	}
	names := []string{to.name(0), entryRegion + mapOwner(t) + countLeaf.path, entryRegion + mapOwner(t) + hasLeaf.path}
	b.choose(alternatives, names...)
}

// someInput looks for a concrete input that accept takes, and reports
// whether it found one. For each shape of sample, search gives the facts
// that the values of its constants should satisfy, and one or more sets of
// constants to quantify universally in them, tried in turn; Z3 proposes
// values, and the sample with those values is handed to accept. A proposal
// accept refuses is excluded and Z3 asked again, a few times. Z3 only proposes: whether an input is
// taken is decided by accept, by proof, so a model of the logic that no Go
// state has cannot slip through.
//
// The shapes are tried in a fixed order, all of them when there are few
// enough, and otherwise drawn evenly from all of them by a fixed sequence.
func (v *fnVerifier) someInput(terms []*logic.Term, search func(input *witness) (facts []*logic.Term, foralls [][]*logic.Term), accept func(input *witness) bool) bool {
	v.searching++
	defer func() { v.searching-- }()
	b := &sampler{v: v, mentioned: map[string]bool{}}
	seen := map[*logic.Term]bool{}
	var sentinels []*logic.Term
	var harvest func(t *logic.Term)
	harvest = func(t *logic.Term) {
		if seen[t] {
			return
		}
		seen[t] = true
		switch {
		case isSentinelTerm(t) && !b.mentioned[t.Name]:
			b.mentioned[t.Name] = true
			sentinels = append(sentinels, t)
		case t.Op == logic.OpConst:
			b.mentioned[t.Name] = true
		case t.Op == logic.OpPush && len(b.literals) < 8:
			// A string or slice literal is a chain of appended elements.
			b.literals = append(b.literals, t)
			return
		}
		for _, arg := range t.Args {
			harvest(arg)
		}
	}
	// The clauses of a contract and the conditions of a path come after the
	// facts about types and memory that hold anyway, and their literals are
	// the likelier contents, so they are collected first.
	for _, t := range slices.Backward(terms) {
		if !v.typing[t] {
			harvest(t)
		}
	}
	b.sentinels = v.tiedToInputs(terms, sentinels)
	for _, param := range v.fn.params {
		entry := v.entry[param]
		if entry != nil {
			b.add(param.Type(), binding{
				set:  func(s *witness, i int, term *logic.Term) { s.consts[entry[i].Name] = term },
				name: func(i int) string { return entry[i].Name },
			}, 0)
		}
	}
	// A package-level variable that keeps its value is an input that no
	// caller chooses: a sample gives it a value too, which what its
	// declaration gives narrows, among the facts known of every input.
	for _, key := range slices.Sorted(maps.Keys(v.fixedMet)) {
		met := v.fixedMet[key]
		if !slices.ContainsFunc(met.val, func(leaf *logic.Term) bool { return b.mentioned[leaf.Name] }) {
			continue
		}
		b.add(met.typ, binding{
			set:  func(s *witness, i int, term *logic.Term) { s.consts[met.val[i].Name] = term },
			name: func(i int) string { return met.val[i].Name },
		}, 0)
	}
	total := 1
	for _, alternatives := range b.slots {
		total = min(total*max(len(alternatives), 1), maxShapes+1)
	}
	exhaustive := total <= maxShapes
	for n := range min(total, maxShapes) {
		input := &witness{consts: map[string]*logic.Term{}, memo: map[*logic.Term]*logic.Term{}, fixed: map[string]bool{}}
		// Everything a sample contains exists.
		input.consts[v.entryBrk.Name] = logic.RefLit(b.refs + 1)
		rest := uint64(n)
		for i, alternatives := range b.slots {
			if len(alternatives) == 0 {
				continue
			}
			count := uint64(len(alternatives))
			if exhaustive {
				alternatives[rest%count](input)
				rest /= count
				continue
			}
			alternatives[scramble(uint64(n), uint64(i))%count](input)
		}
		facts, foralls := search(input)
		// What is known of every input narrows what Z3 proposes to what
		// accept can take.
		facts = append(slices.Clip(facts), input.fixedOnly().apply(v.knownFacts())...)
		for _, forall := range foralls {
			if v.proposeFor(b, input, append(slices.Clip(b.facts), facts...), forall, accept) {
				return true
			}
		}
	}
	return false
}

// tiedToInputs returns the variables among sentinels that the formulas tie
// to an error of the input: two constants that hold or contain errors are
// tied when one formula mentions both, and ties are followed from one
// constant to the next. A sample may give an input error the value of such
// a variable. One that is tied only to what calls returned, as those that a
// contract of a callee names, would only widen the search: no fact about
// the input can then need the input to be it. Which variables are offered
// decides only where the search looks, never whether a sample is taken.
func (v *fnVerifier) tiedToInputs(terms, sentinels []*logic.Term) []*logic.Term {
	if len(sentinels) == 0 {
		return nil
	}
	holdsError := func(sort logic.Sort) bool {
		for sort.IsSeq() {
			sort = sort.Elem()
		}
		return sort == logic.Err
	}
	parent := map[string]string{}
	var find func(name string) string
	find = func(name string) string {
		if up, ok := parent[name]; ok && up != name {
			root := find(up)
			parent[name] = root
			return root
		}
		parent[name] = name
		return name
	}
	inputs := map[string]bool{}
	for _, t := range terms {
		if v.typing[t] {
			continue
		}
		var names []string
		seen := map[*logic.Term]bool{}
		var walk func(t *logic.Term)
		walk = func(t *logic.Term) {
			if seen[t] {
				return
			}
			seen[t] = true
			if t.Op == logic.OpConst && t != logic.NilErr() && holdsError(t.Sort) {
				names = append(names, t.Name)
				if v.isInput(t) && !isSentinelTerm(t) {
					inputs[t.Name] = true
				}
			}
			for _, arg := range t.Args {
				walk(arg)
			}
		}
		walk(t)
		for _, name := range names {
			parent[find(name)] = find(names[0])
		}
	}
	tied := map[string]bool{}
	for name := range inputs {
		tied[find(name)] = true
	}
	var offered []*logic.Term
	for _, sentinel := range sentinels {
		if tied[find(sentinel.Name)] {
			offered = append(offered, sentinel)
		}
	}
	return offered
}

// proposeFor asks Z3 for values of the constants of a sample that satisfy
// the facts for every value of the constants in forall, and hands the
// sample with them to accept, up to maxRounds times. It reports whether
// accept took one.
func (v *fnVerifier) proposeFor(b *sampler, input *witness, facts, forall []*logic.Term, accept func(input *witness) bool) bool {
	// A proposal decides nothing, so it gets a part of the effort a proof
	// gets.
	opts := v.options(max(v.effort/4, 1), failureCheck)
	opts.Forall = forall
	for range maxRounds {
		result, values := v.solver().Model(facts, opts, b.vars)
		v.noteLimit(result)
		if result == solver.Proved {
			// No values make the facts hold, so none makes accept take
			// the sample.
			return false
		}
		if values == nil {
			values = map[string]*logic.Term{}
		}
		// A constant Z3 gave no value matters to nothing it checked, so
		// any value of its type will do; zero is one for every integer
		// type.
		var picked []*logic.Term
		for _, c := range b.vars {
			if value, ok := values[c.Name]; ok {
				picked = append(picked, logic.Eq(c, value))
				continue
			}
			values[c.Name] = logic.IntLit(0)
			if c.Sort == logic.Bool {
				values[c.Name] = logic.False()
			}
		}
		if offer(b, input, result, values, accept) {
			return true
		}
		if len(picked) == 0 {
			// Nothing to exclude: asking again would give the same.
			return false
		}
		facts = append(facts, logic.Not(logic.And(picked...)))
	}
	return false
}

// offer hands a sample with the values Z3 proposed to accept, and reports
// whether accept took it. Z3's values are a model, which is not trusted:
// that each lies in the range of its type, and so that the sample is an
// input Go has, is checked first. A value out of range after Z3 answered
// sat is a fault of Z3; after another answer the proposal is only passed
// over.
func offer(b *sampler, input *witness, result solver.Result, values map[string]*logic.Term, accept func(input *witness) bool) bool {
	if rangesHold(b.facts, values) {
		return accept(input.bind(values))
	}
	if result == solver.Refuted {
		panic(&solver.Fault{Err: fmt.Errorf("Z3 gave sample values outside their ranges: %v", values), File: "(not saved)"})
	}
	return false
}

// rangesHold reports whether the values of the constants of a sample lie in
// the ranges the sampler set for them. Each range fact is a comparison of a
// constant with a number.
func rangesHold(facts []*logic.Term, values map[string]*logic.Term) bool {
	number := func(t *logic.Term) *big.Int {
		if t.Op == logic.OpConst {
			t = values[t.Name]
		}
		if t == nil || t.Op != logic.OpIntLit {
			panic(fmt.Sprintf("vego: a range fact of a sample is not about numbers: %v", t))
		}
		return t.Value()
	}
	for _, fact := range facts {
		if fact.Op != logic.OpLe {
			panic(fmt.Sprintf("vego: a range fact of a sample is not a comparison: %v", fact))
		}
		if number(fact.Args[0]).Cmp(number(fact.Args[1])) > 0 {
			return false
		}
	}
	return true
}

// scramble returns a number that depends on both arguments in no simple
// way, and is zero for the first sample, which so takes the first
// alternative of every slot.
func scramble(sample, slot uint64) uint64 {
	if sample == 0 {
		return 0
	}
	x := sample*0x9E3779B97F4A7C15 + slot*0xBF58476D1CE4E5B9
	x ^= x >> 30
	x *= 0xBF58476D1CE4E5B9
	x ^= x >> 27
	x *= 0x94D049BB133111EB
	return x ^ x>>31
}

// primedEnsures reports whether an Ensures of a contract speaks of the
// state on return through a primed path.
func primedEnsures(fn *funcInfo) bool {
	found := false
	for _, c := range fn.ensures {
		c.node.Walk(func(n *logic.Node) {
			if n.Primed {
				found = true
			}
		})
	}
	return found
}
