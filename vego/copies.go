package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"slices"
	"strings"

	"golang.org/x/tools/go/ssa"
)

// A value that holds a state, such as a sync.Mutex or a struct with one as
// a field, is never copied or overwritten by verified code. The model would
// copy the state with the struct, as Go copies the fields of a mutex, but
// that is not enough: sync documents that a Mutex must not be copied after
// first use, so no contract may say what Lock does on a copy, and a copy of
// a mutex that another goroutine holds stays locked for ever while its
// state, which is about the calling goroutine, says it is free. And a state
// changes only through the contracts of methods, which an assignment of a
// whole value would get round.
//
// So the places where Go copies or overwrites such a value are refused,
// found from the syntax (copyWalk), and go/ssa confirms that nothing else
// copies one: in debug mode every copy of a value is an SSA value of its
// type, and the only one allowed is the value of a composite literal (see
// ssaCopiesOf). A copy the walk misses ends the function with a message of its
// own, so it cannot pass quietly.

// holdsState returns the type with a declared state, or that owns memory
// through its fields (see footprint.go), that a value of type t holds in
// itself, not behind a pointer, a slice, or a map: t itself, a field of it
// at any depth, or an element of an array in it.
func holdsState(t types.Type) (types.Type, bool) {
	switch u := t.Underlying().(type) {
	case *types.Struct:
		if len(statesOf(u)) > 0 || len(ownedFieldsOf(t)) > 0 {
			return t, true
		}
		for field := range u.Fields() {
			if inner, ok := holdsState(field.Type()); ok {
				return inner, true
			}
		}
	case *types.Array:
		return holdsState(u.Elem())
	}
	return nil, false
}

// holding describes a type that holds a state, for a message, followed by
// a comma when more of the sentence follows.
// Types are named relative to the package, as q says.
func holding(t types.Type, q types.Qualifier) string {
	inner, _ := holdsState(t)
	if types.Identical(inner, t) {
		if len(statesOf(t.Underlying().(*types.Struct))) == 0 {
			// A type with the fields of an owner owns by the owner's
			// declaration, which the message names.
			if known := ownsDeclaredBy(t); known != nil {
				shown, owned := types.TypeString(t, q), strings.Join(known.fields, ", ")
				return fmt.Sprintf("%s, which owns memory (%s owns %s because it has the fields of %s, which declares // @Owns %s; give %s a field of its own, or use %s)",
					shown, shown, owned, known.name.Name(), owned, shown, known.name.Name())
			}
			return fmt.Sprintf("%s, which owns memory", types.TypeString(t, q))
		}
		return fmt.Sprintf("%s, which holds a state", types.TypeString(t, q))
	}
	return fmt.Sprintf("%s, which holds a %s", types.TypeString(t, q), types.TypeString(inner, q))
}

// copyReasonFor is said in every refusal of a copy of a value of type t:
// copyReason when what t holds has a state, and ownerCopyReason when it
// only owns memory.
func copyReasonFor(t types.Type) string {
	inner, _ := holdsState(t)
	if u, ok := inner.Underlying().(*types.Struct); ok && len(statesOf(u)) == 0 {
		return ownerCopyReason
	}
	return copyReason
}

// ownerCopyReason is said in the refusal of a copy of a value that owns
// memory and holds no state.
const ownerCopyReason = "a value that owns memory must not be copied or overwritten, " +
	"since a copy would share what the original owns, which only the methods of each may write"

// copyReason is said in every other refusal.
const copyReason = "a value that holds a state, such as a sync.Mutex, must not be copied or overwritten, " +
	"since its state changes only through its methods and sync documents that a Mutex must not be copied after first use"

// skipCopyWalk turns the syntactic walk off, so that a test can show that
// the confirmation by go/ssa catches every copy on its own.
var skipCopyWalk = false

// checkCopies refuses the first place in a function, its signature
// included, where Go copies or overwrites a value that holds a state.
func (v *fnVerifier) checkCopies(decl *ast.FuncDecl) {
	if !skipCopyWalk {
		if pos, msg := copyWalk(v.info, v.pass.Pkg, decl, v.findConversions()); msg != "" {
			v.unsupported(pos, rCopyValue, msg)
		}
	}
	// A struct whose states trusted methods change is never copied: the
	// states are about what it refers to, which a copy shares (F10 of the
	// design review of S0b of F34). Only go/ssa is asked: every copy of a
	// value is an SSA value of its type.
	if found := v.findSharedCopies()[decl]; len(found) > 0 {
		inner, _ := v.sharesStates(found[0].typ)
		shown := func(t types.Type) string { return types.TypeString(t, types.RelativeTo(v.pass.Pkg)) }
		what := shown(found[0].typ)
		if !types.Identical(inner, found[0].typ) {
			what += ", which holds " + article(shown(inner)) + " " + shown(inner)
		}
		v.unsupported(found[0].pos, rCopyValue, fmt.Sprintf("Go copies a value of type %s, here (%s); the states of %s %s are changed by trusted methods and are about what it refers to, "+
			"which a copy would share, so %s %s is never copied; hold it by pointer", what, v.copySource(decl, found[0]), article(shown(inner)), shown(inner), article(shown(inner)), shown(inner)))
	}
	if found := v.findCopies()[decl]; len(found) > 0 {
		v.unsupported(found[0].pos, rCopyValue, fmt.Sprintf("Go copies a value of type %s, here (%s), and no rule of vego accounts for the copy; %s; "+
			"hold the value by pointer", holding(found[0].typ, types.RelativeTo(v.pass.Pkg)), found[0].what, copyReasonFor(found[0].typ)))
	}
}

// copyWalk returns the first place under decl where Go copies or
// overwrites a value that holds a state, and what to say about it.
func copyWalk(info *types.Info, pkg *types.Package, decl *ast.FuncDecl, conv *conversions) (token.Pos, string) {
	q := types.RelativeTo(pkg)
	var pos token.Pos
	msg := ""
	refuse := func(at token.Pos, t types.Type, format string, args ...any) {
		if msg == "" {
			pos, msg = at, fmt.Sprintf(format, args...)+"; "+copyReasonFor(t)
		}
	}
	signature := func(fields *ast.FieldList, what, of string) {
		if fields == nil {
			return
		}
		for _, field := range fields.List {
			t := info.TypeOf(field.Type)
			if _, ok := holdsState(t); !ok {
				continue
			}
			name := "an unnamed one"
			if len(field.Names) > 0 {
				name = field.Names[0].Name
			}
			refuse(field.Pos(), t, "the %s %s%s has type %s, and passing it copies the value; use a pointer to %s",
				what, name, of, holding(t, q), types.TypeString(t, q))
		}
	}
	signature(decl.Recv, "receiver", "")
	signature(decl.Type.Params, "parameter", "")
	signature(decl.Type.Results, "result", "")
	var stack []ast.Node
	ast.Inspect(decl.Body, func(n ast.Node) bool {
		if n == nil {
			stack = stack[:len(stack)-1]
			return false
		}
		var parent ast.Node
		if len(stack) > 0 {
			parent = stack[len(stack)-1]
		}
		stack = append(stack, n)
		switch n := n.(type) {
		case *ast.FuncLit:
			signature(n.Type.Params, "parameter", " of the function literal")
			signature(n.Type.Results, "result", " of the function literal")
		case *ast.RangeStmt:
			for _, e := range []ast.Expr{n.Key, n.Value} {
				if e == nil {
					continue
				}
				if t := info.TypeOf(e); t != nil {
					if _, ok := holdsState(t); ok {
						refuse(e.Pos(), t, "the range variable %s copies each element, a value of type %s; range over the indices and use &s[i]",
							types.ExprString(e), holding(t, q))
					}
				}
			}
		case *ast.ForStmt:
			if init, ok := n.Init.(*ast.AssignStmt); ok && init.Tok == token.DEFINE {
				for _, lhs := range init.Lhs {
					if t := info.TypeOf(lhs); t != nil {
						if _, ok := holdsState(t); ok {
							refuse(lhs.Pos(), t, "the loop variable %s has type %s, and Go copies it into each iteration; declare it before the loop",
								types.ExprString(lhs), holding(t, q))
						}
					}
				}
			}
		case *ast.AssignStmt:
			for _, lhs := range n.Lhs {
				t := info.TypeOf(lhs)
				if t == nil {
					continue
				}
				if _, ok := holdsState(t); !ok {
					continue
				}
				id, isIdent := ast.Unparen(lhs).(*ast.Ident)
				if n.Tok == token.DEFINE && isIdent && info.Defs[id] != nil {
					continue
				}
				refuse(lhs.Pos(), t, "%s is assigned, which overwrites a value of type %s; create the value where it is declared, "+
					"as in x := T{} or p := &T{}, and change it only through its methods", types.ExprString(lhs), holding(t, q))
			}
		case *ast.CallExpr:
			if id, ok := ast.Unparen(n.Fun).(*ast.Ident); ok && len(n.Args) > 0 {
				if builtin, ok := info.Uses[id].(*types.Builtin); ok && builtin.Name() == "append" {
					if t := info.TypeOf(n.Args[0]); t != nil {
						if s, ok := t.Underlying().(*types.Slice); ok {
							if _, holds := holdsState(s.Elem()); holds {
								refuse(n.Pos(), s.Elem(), "append to a slice of %s, copies every element when the slice grows; "+
									"build the slice with its final length, as in make([]T, n), or hold the elements by pointer", holding(s.Elem(), q))
							}
						}
					}
				}
			}
		case *ast.TypeAssertExpr:
			// x.(T) copies what the interface value holds (F33).
			if n.Type != nil {
				if t := info.TypeOf(n.Type); t != nil {
					if _, ok := holdsState(t); ok {
						refuse(n.Pos(), t, "the type assertion %s copies what %s holds, a value of type %s; hold a pointer to it in the %s instead",
							types.ExprString(n), types.ExprString(n.X), holding(t, q), holderWord(info, n.X))
					}
				}
			}
		case *ast.TypeSwitchStmt:
			var operand ast.Expr
			switch a := n.Assign.(type) {
			case *ast.ExprStmt:
				operand = a.X.(*ast.TypeAssertExpr).X
			case *ast.AssignStmt:
				operand = a.Rhs[0].(*ast.TypeAssertExpr).X
			}
			for _, clause := range n.Body.List {
				for _, e := range clause.(*ast.CaseClause).List {
					if t := info.TypeOf(e); t != nil {
						if _, ok := holdsState(t); ok {
							refuse(e.Pos(), t, "the case %s of the type switch copies what the operand holds, a value of type %s; hold a pointer to it in the %s instead",
								types.ExprString(e), holding(t, q), holderWord(info, operand))
						}
					}
				}
			}
		case *ast.SelectorExpr:
			selection := info.Selections[n]
			if selection == nil || selection.Kind() == types.FieldVal {
				break
			}
			// A method with a value receiver is given a copy of the value,
			// also when it is called through a pointer.
			recv := selection.Obj().Type().(*types.Signature).Recv()
			if recv == nil {
				break
			}
			if _, isPointer := recv.Type().Underlying().(*types.Pointer); !isPointer {
				if _, ok := holdsState(recv.Type()); ok {
					refuse(n.Sel.Pos(), recv.Type(), "%s has a value receiver of type %s, so calling it copies the value; give the method a pointer receiver",
						selection.Obj().Name(), holding(recv.Type(), q))
				}
			}
		}
		e, isExpr := n.(ast.Expr)
		if !isExpr {
			return true
		}
		tv, ok := info.Types[e]
		if !ok || !tv.IsValue() || tv.Type == nil {
			return true
		}
		if _, ok := holdsState(tv.Type); !ok {
			// A conversion to an interface of a pointer whose type has a
			// method with a value receiver copies the value at each call.
			for _, target := range conv.converted[ast.Unparen(e)] {
				if what, ok := valueReceiverOf(tv.Type, target); ok {
					refuse(e.Pos(), what.Type().(*types.Signature).Recv().Type(), "%s is converted to %s, whose method %s has a value receiver of type %s, so each call copies the value; "+
						"give the method a pointer receiver", types.ExprString(e), types.TypeString(target, q), what.Name(), holding(what.Type().(*types.Signature).Recv().Type(), q))
				}
			}
			return true
		}
		if call, isCall := ast.Unparen(e).(*ast.CallExpr); isCall && !tv.IsType() {
			if fun := info.Types[call.Fun]; !fun.IsType() {
				refuse(e.Pos(), tv.Type, "%s returns a value of type %s, and the call copies it; return a pointer", types.ExprString(call.Fun), holding(tv.Type, q))
				return true
			}
		}
		if allowedStateUse(info, e, parent) {
			return true
		}
		if sel, ok := parent.(*ast.SelectorExpr); ok && sel.X == e {
			refuse(e.Pos(), tv.Type, "%s cannot be addressed, so Go copies a value of type %s, to select %s from it; hold the value by pointer, "+
				"as in a map of pointers", types.ExprString(e), holding(tv.Type, q), sel.Sel.Name)
			return true
		}
		refuse(e.Pos(), tv.Type, "%s copies a value of type %s; use a pointer to it", types.ExprString(e), holding(tv.Type, q))
		return true
	})
	return pos, msg
}

// allowedStateUse reports whether an expression whose type holds a state
// stands where Go neither copies nor overwrites it: a composite literal,
// which makes a new value; the operand of &; an addressable operand of a
// field selection or of a method with a pointer receiver, which Go takes
// the address of; and the target of an assignment, which the walk judges
// on its own.
func allowedStateUse(info *types.Info, e ast.Expr, parent ast.Node) bool {
	if _, literal := ast.Unparen(e).(*ast.CompositeLit); literal {
		return true
	}
	switch p := parent.(type) {
	case *ast.ParenExpr:
		return true
	case *ast.UnaryExpr:
		return p.Op == token.AND && p.X == e
	case *ast.SelectorExpr:
		return p.X == e && addressable(info, e)
	case *ast.AssignStmt:
		return slices.Contains(p.Lhs, e)
	}
	return false
}

// addressable reports whether Go can take the address of an expression, so
// that selecting a field of it, or calling a method with a pointer receiver
// on it, does not copy it. A composite literal counts: it is a new value,
// and copying it copies nothing that was used.
func addressable(info *types.Info, e ast.Expr) bool {
	switch e := ast.Unparen(e).(type) {
	case *ast.Ident:
		_, isVar := info.Uses[e].(*types.Var)
		return isVar
	case *ast.StarExpr, *ast.CompositeLit:
		return true
	case *ast.SelectorExpr:
		selection := info.Selections[e]
		if selection == nil || selection.Kind() != types.FieldVal {
			return false
		}
		if selection.Indirect() {
			return true
		}
		if _, isPointer := info.TypeOf(e.X).Underlying().(*types.Pointer); isPointer {
			return true
		}
		return addressable(info, e.X)
	case *ast.IndexExpr:
		switch info.TypeOf(e.X).Underlying().(type) {
		case *types.Slice, *types.Pointer:
			return true
		case *types.Array:
			return addressable(info, e.X)
		}
	}
	return false
}

// valueReceiverOf returns a method of the interface target whose method
// of type t has a value receiver of a type that holds a state.
func valueReceiverOf(t, target types.Type) (*types.Func, bool) {
	iface, ok := target.Underlying().(*types.Interface)
	if !ok {
		return nil, false
	}
	for method := range iface.Methods() {
		found, _, _ := types.LookupFieldOrMethod(t, true, method.Pkg(), method.Name())
		fn, isFunc := found.(*types.Func)
		if !isFunc {
			continue
		}
		recv := fn.Type().(*types.Signature).Recv()
		if recv == nil {
			continue
		}
		if _, isPointer := recv.Type().Underlying().(*types.Pointer); isPointer {
			continue
		}
		if _, holds := holdsState(recv.Type()); holds {
			return fn, true
		}
	}
	return nil, false
}

// ssaCopy is a value of a type that holds a state in go/ssa that is not the
// value of a composite literal: a copy.
type ssaCopy struct {
	pos  token.Pos
	typ  types.Type
	what string
}

// findCopies lists, for each function declaration, the copies go/ssa makes
// of values that hold a state; see ssaCopiesOf.
func (pv *pkgVerifier) findCopies() map[*ast.FuncDecl][]ssaCopy {
	if pv.copies != nil {
		return pv.copies
	}
	pv.copies = map[*ast.FuncDecl][]ssaCopy{}
	if !pv.holdsStates() {
		return pv.copies
	}
	ssaFunctions(pv.ssaProgram(), pv.pass.Files, pv.info, func(fd *ast.FuncDecl, fn *ssa.Function) {
		pv.copies[fd] = ssaCopiesOf(fn, holdsState)
	})
	return pv.copies
}

// copySource names, for a message, the expression where go/ssa found a
// copy (F13 of the review of S0b of F34): the dereference or the expression
// at its position, the range whose iteration copies an element, or what
// ssaCopiesOf said of a parameter, a result, or a receiver.
func (v *fnVerifier) copySource(decl *ast.FuncDecl, c ssaCopy) string {
	if strings.HasPrefix(c.what, "the ") {
		return c.what
	}
	found := ""
	var ranged *ast.RangeStmt
	ast.Inspect(decl, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.RangeStmt:
			if n.Pos() <= c.pos && c.pos < n.Body.Pos() {
				ranged = n
			}
		case ast.Expr:
			if found == "" && n.Pos() == c.pos {
				if t := v.info.TypeOf(n); t != nil && types.Identical(t, c.typ) {
					found = types.ExprString(n)
				}
			}
		}
		return true
	})
	switch {
	case found != "":
		return found
	case ranged != nil:
		return "the range over " + types.ExprString(ranged.X)
	}
	return "a copy that go/ssa found"
}

// findSharedCopies is findCopies for the structs whose states trusted
// methods change (sharesStates).
func (pv *pkgVerifier) findSharedCopies() map[*ast.FuncDecl][]ssaCopy {
	if pv.sharedCopies != nil {
		return pv.sharedCopies
	}
	pv.sharedCopies = map[*ast.FuncDecl][]ssaCopy{}
	if len(pv.stateInterfaces()) == 0 {
		return pv.sharedCopies
	}
	ssaFunctions(pv.ssaProgram(), pv.pass.Files, pv.info, func(fd *ast.FuncDecl, fn *ssa.Function) {
		pv.sharedCopies[fd] = ssaCopiesOf(fn, pv.sharesStates)
	})
	return pv.sharedCopies
}

// sharesStates returns the struct type, t itself, a field of it at any
// depth, or an element of an array in it, held by value and not behind a
// pointer, whose pointer has states that a trusted method changes.
func (pv *pkgVerifier) sharesStates(t types.Type) (types.Type, bool) {
	switch u := t.Underlying().(type) {
	case *types.Struct:
		if pointer := types.NewPointer(t); pv.pointerKeyed(pointer) && !pv.ghostPointer(pointer) {
			return t, true
		}
		for field := range u.Fields() {
			if inner, ok := pv.sharesStates(field.Type()); ok {
				return inner, true
			}
		}
	case *types.Array:
		return pv.sharesStates(u.Elem())
	}
	return nil, false
}

// holdsStates reports whether any struct type of the package or of what it
// is built with has a declared state, so that the package can hold one; the
// confirmation by go/ssa is not built otherwise. A state of an interface
// lies at a home, not in a value, so copying the value copies none.
func (pv *pkgVerifier) holdsStates() bool {
	for path, byType := range shippedStates() {
		seen := map[*types.Package]bool{}
		var reached *types.Package
		var reaches func(pkg *types.Package) bool
		reaches = func(pkg *types.Package) bool {
			if seen[pkg] {
				return false
			}
			seen[pkg] = true
			if pkg.Path() == path {
				reached = pkg
				return true
			}
			return slices.ContainsFunc(pkg.Imports(), reaches)
		}
		if !reaches(pv.pass.Pkg) {
			continue
		}
		for name := range byType {
			if obj, ok := reached.Scope().Lookup(name).(*types.TypeName); ok {
				if _, isStruct := obj.Type().Underlying().(*types.Struct); isStruct {
					return true
				}
			}
		}
	}
	return false
}

// ssaCopiesOf returns the values of a function and of the literals in it
// whose type holds a state and that are not the value of a composite
// literal: a load from the local Alloc that go/ssa makes for the literal,
// which carries the DebugRef of that literal. A parameter of such a type
// counts as a copy too, since the caller copied it.
// Which types hold a state is what holds says.
func ssaCopiesOf(fn *ssa.Function, holds func(types.Type) (types.Type, bool)) []ssaCopy {
	var found []ssaCopy
	add := func(value ssa.Value, at token.Pos) {
		if _, ok := holds(value.Type()); ok {
			found = append(found, ssaCopy{pos: at, typ: value.Type(), what: value.String()})
		}
	}
	for _, param := range fn.Params {
		add(param, fn.Pos())
	}
	// A result is copied to the caller.
	for result := range fn.Signature.Results().Variables() {
		if _, ok := holds(result.Type()); ok {
			found = append(found, ssaCopy{pos: fn.Pos(), typ: result.Type(), what: "the result " + result.Name()})
		}
	}
	for _, block := range fn.Blocks {
		literal := map[ssa.Value]bool{}
		for _, instr := range block.Instrs {
			if ref, ok := instr.(*ssa.DebugRef); ok && !ref.IsAddr {
				if _, isLiteral := ast.Unparen(ref.Expr).(*ast.CompositeLit); isLiteral {
					literal[ref.X] = true
				}
			}
		}
		for _, instr := range block.Instrs {
			// A pointer converted to an interface whose method has a value
			// receiver is copied at each call, in a wrapper go/ssa makes.
			if conversion, ok := instr.(*ssa.MakeInterface); ok {
				if method, ok := valueReceiverOf(conversion.X.Type(), conversion.Type()); ok {
					found = append(found, ssaCopy{pos: nearestPos(block.Instrs, instr), typ: method.Type().(*types.Signature).Recv().Type(),
						what: "the receiver of " + method.Name()})
				}
			}
			value, ok := instr.(ssa.Value)
			if !ok {
				continue
			}
			if load, isLoad := value.(*ssa.UnOp); isLoad && load.Op == token.MUL && literal[value] {
				if alloc, isAlloc := load.X.(*ssa.Alloc); isAlloc && !alloc.Heap && alloc.Comment == "complit" {
					continue
				}
			}
			add(value, nearestPos(block.Instrs, instr))
		}
		// A constant is the zero value, which is no copy of anything used.
	}
	for _, anon := range fn.AnonFuncs {
		found = append(found, ssaCopiesOf(anon, holds)...)
	}
	return found
}

// holderWord names what an operand of an assertion or a type switch is, for
// the remedy of a copy: an error, or another interface value.
func holderWord(info *types.Info, x ast.Expr) string {
	if x != nil && isError(info.TypeOf(x)) {
		return "error"
	}
	return "interface value"
}
