package vego

import (
	"go/ast"
	"go/token"
	"go/types"

	"golang.org/x/tools/go/ssa"
)

// Go converts a value to an interface type in many places without saying
// so: an argument, an assignment, a return, an element of a composite
// literal, a map key, an operand of ==, a switch case. A conversion of a
// concrete value to an interface with methods is where verified code makes
// an interface value, and each method of the value has to be checked there
// against its contract (see madeInterface). A conversion that the verifier
// evaluated as an ordinary expression would make an interface value nobody
// checked.
//
// So the conversions of a package are listed from two sources, and the
// verifier stops with an internal error when it evaluates a listed
// expression anywhere but where the conversion is checked
// (evalConverted), or where newError formats it:
//
//   - The record that go/ssa makes of the package: every conversion to an
//     interface type is a MakeInterface instruction there, implicit or
//     explicit. Built in debug mode, every expression whose value is
//     computed gets a DebugRef to that value, and the expression converted
//     is the nearest DebugRef of the operand before the MakeInterface in the
//     same block that no other MakeInterface took. A constant gets no
//     DebugRef, and a conversion of something without an expression of its
//     own, such as one result of a call with several, has none either; a
//     function with such a conversion that is not a constant cannot be
//     verified (see unplaced).
//   - The contexts in which the specification lets a value be assigned to
//     a variable of another type, walked in the syntax tree
//     (syntacticConversions).
//
// The type checker keeps no record of implicit conversions. A test checks
// that the two lists agree on the corpus, so that a gap in either shows.

// conversions is what the two lists say of a package.
type conversions struct {
	// converted holds every expression that Go converts to an interface
	// type where it stands.
	converted map[ast.Expr]bool
	// unplaced holds, for the function declaration around it, the position
	// of each conversion of a value that is not a constant and has no
	// expression of its own.
	unplaced map[*ast.FuncDecl][]token.Pos
}

// findConversions lists the conversions of the package.
func (pv *pkgVerifier) findConversions() *conversions {
	if pv.conversions != nil {
		return pv.conversions
	}
	found := &conversions{converted: map[ast.Expr]bool{}, unplaced: map[*ast.FuncDecl][]token.Pos{}}
	placed, unplaced := ssaConversions(pv.pass.Fset, pv.pass.Pkg, pv.pass.Files, pv.info)
	for e := range placed {
		found.converted[e] = true
	}
	for _, file := range pv.pass.Files {
		for e := range syntacticConversions(pv.info, file) {
			found.converted[e] = true
		}
	}
	for _, conversion := range unplaced {
		at := conversion.at
		if !at.IsValid() {
			at = conversion.fn.Pos()
		}
		for _, file := range pv.pass.Files {
			for _, decl := range file.Decls {
				if fd, ok := decl.(*ast.FuncDecl); ok && fd.Pos() <= conversion.fn.Pos() && conversion.fn.Pos() < fd.End() {
					found.unplaced[fd] = append(found.unplaced[fd], at)
				}
			}
		}
	}
	pv.conversions = found
	return found
}

// ssaConversions builds the package in go/ssa, with a DebugRef for every
// expression, and returns the expressions that its MakeInterface
// instructions convert, and the positions of the functions or literals
// that hold a conversion of a value that is not a constant and has no
// expression of its own.
func ssaConversions(fset *token.FileSet, pkg *types.Package, files []*ast.File, info *types.Info) (placed map[ast.Expr]bool, unplaced []unplacedConversion) {
	prog := ssa.NewProgram(fset, ssa.GlobalDebug)
	created := map[*types.Package]bool{}
	var create func(imports []*types.Package)
	create = func(imports []*types.Package) {
		for _, imported := range imports {
			if !created[imported] {
				created[imported] = true
				prog.CreatePackage(imported, nil, nil, true)
				create(imported.Imports())
			}
		}
	}
	create(pkg.Imports())
	built := prog.CreatePackage(pkg, files, info, false)
	built.Build()
	placed = map[ast.Expr]bool{}
	isConstant := func(value ssa.Value) bool {
		_, ok := value.(*ssa.Const)
		return ok
	}
	var walk func(fn *ssa.Function)
	walk = func(fn *ssa.Function) {
		for _, block := range fn.Blocks {
			// The expressions of each value, in the order the block
			// computes them, not yet taken by a conversion.
			refs := map[ssa.Value][]*ssa.DebugRef{}
			for _, instr := range block.Instrs {
				switch instr := instr.(type) {
				case *ssa.DebugRef:
					if !instr.IsAddr {
						refs[instr.X] = append(refs[instr.X], instr)
					}
				case *ssa.MakeInterface:
					candidates := refs[instr.X]
					switch {
					case len(candidates) > 0:
						last := candidates[len(candidates)-1]
						refs[instr.X] = candidates[:len(candidates)-1]
						placed[ast.Unparen(last.Expr)] = true
					case isConstant(instr.X):
					default:
						unplaced = append(unplaced, unplacedConversion{fn: fn.Syntax(), at: nearestPos(block.Instrs, instr), what: instr.X.String()})
					}
				}
			}
		}
		for _, anon := range fn.AnonFuncs {
			walk(anon)
		}
	}
	for _, file := range files {
		for _, decl := range file.Decls {
			fd, ok := decl.(*ast.FuncDecl)
			if !ok {
				continue
			}
			obj, _ := info.Defs[fd.Name].(*types.Func)
			if obj == nil {
				continue
			}
			if fn := prog.FuncValue(obj); fn != nil && fn.Synthetic == "" {
				walk(fn)
			}
		}
	}
	return placed, unplaced
}

// unplacedConversion is a conversion that go/ssa makes of a value that is
// not a constant and has no expression of its own: the function or literal
// it is in, the nearest position the instructions up to it give, and what
// is converted.
type unplacedConversion struct {
	fn   ast.Node
	at   token.Pos
	what string
}

// nearestPos returns the position of an instruction, or of the nearest one
// before it in its block that has one; a conversion that Go makes without
// saying so has none of its own.
func nearestPos(instrs []ssa.Instruction, instr ssa.Instruction) token.Pos {
	at := token.NoPos
	for _, other := range instrs {
		if other.Pos().IsValid() {
			at = other.Pos()
		}
		if other == instr {
			break
		}
	}
	return at
}

// syntacticConversions returns the expressions under root that Go converts
// to an interface type where they stand, found by the contexts in which
// the specification lets a value be assigned to something of another type.
// One result of a call with several, an element that a range assigns, and
// a value that a comma-ok form gives have no expression of their own and
// are not listed.
func syntacticConversions(info *types.Info, root ast.Node) map[ast.Expr]bool {
	found := map[ast.Expr]bool{}
	add := func(e ast.Expr, to types.Type) {
		if e == nil || to == nil || !types.IsInterface(to) {
			return
		}
		e = ast.Unparen(e)
		tv := info.Types[e]
		if tv.Type == nil || tv.IsNil() || types.IsInterface(tv.Type) {
			return
		}
		if _, tuple := tv.Type.(*types.Tuple); tuple {
			return
		}
		found[e] = true
	}
	var walk func(root ast.Node, results *types.Tuple)
	walk = func(root ast.Node, results *types.Tuple) {
		ast.Inspect(root, func(n ast.Node) bool {
			switch n := n.(type) {
			case *ast.FuncLit:
				if sig, ok := info.TypeOf(n).(*types.Signature); ok {
					walk(n.Body, sig.Results())
				}
				return false
			case *ast.AssignStmt:
				if (n.Tok == token.ASSIGN || n.Tok == token.DEFINE) && len(n.Lhs) == len(n.Rhs) {
					for i, lhs := range n.Lhs {
						add(n.Rhs[i], info.TypeOf(lhs))
					}
				}
			case *ast.ValueSpec:
				if n.Type != nil && len(n.Names) == len(n.Values) {
					for i, name := range n.Names {
						add(n.Values[i], info.TypeOf(name))
					}
				}
			case *ast.ReturnStmt:
				if results != nil && len(n.Results) == results.Len() {
					for i, result := range n.Results {
						add(result, results.At(i).Type())
					}
				}
			case *ast.CallExpr:
				callConversions(info, n, add)
			case *ast.CompositeLit:
				literalConversions(info, n, add)
			case *ast.IndexExpr:
				if m, ok := info.TypeOf(n.X).Underlying().(*types.Map); ok {
					add(n.Index, m.Key())
				}
			case *ast.SendStmt:
				if ch, ok := info.TypeOf(n.Chan).Underlying().(*types.Chan); ok {
					add(n.Value, ch.Elem())
				}
			case *ast.BinaryExpr:
				if n.Op == token.EQL || n.Op == token.NEQ {
					add(n.X, info.TypeOf(n.Y))
					add(n.Y, info.TypeOf(n.X))
				}
			case *ast.SwitchStmt:
				if n.Tag != nil {
					for _, stmt := range n.Body.List {
						for _, c := range stmt.(*ast.CaseClause).List {
							add(c, info.TypeOf(n.Tag))
							add(n.Tag, info.TypeOf(c))
						}
					}
				}
			}
			return true
		})
	}
	ast.Inspect(root, func(n ast.Node) bool {
		if fd, ok := n.(*ast.FuncDecl); ok {
			if fd.Body != nil {
				if obj, ok := info.Defs[fd.Name].(*types.Func); ok {
					walk(fd.Body, obj.Type().(*types.Signature).Results())
				}
			}
			return false
		}
		return true
	})
	return found
}

// callConversions adds the arguments of a call that Go converts: to the
// types of the parameters, the elements that append adds, what panic and
// delete take, and the operand of a conversion.
func callConversions(info *types.Info, call *ast.CallExpr, add func(e ast.Expr, to types.Type)) {
	tv := info.Types[call.Fun]
	switch {
	case tv.IsType():
		if len(call.Args) == 1 {
			add(call.Args[0], info.TypeOf(call))
		}
		return
	case tv.IsBuiltin():
		name := ""
		if id, ok := ast.Unparen(call.Fun).(*ast.Ident); ok {
			name = id.Name
		}
		switch name {
		case "append":
			if s, ok := info.TypeOf(call).Underlying().(*types.Slice); ok && !call.Ellipsis.IsValid() {
				for _, arg := range call.Args[1:] {
					add(arg, s.Elem())
				}
			}
		case "panic":
			add(call.Args[0], types.Universe.Lookup("any").Type())
		case "delete":
			if m, ok := info.TypeOf(call.Args[0]).Underlying().(*types.Map); ok {
				add(call.Args[1], m.Key())
			}
		}
		return
	}
	sig, ok := info.TypeOf(call.Fun).Underlying().(*types.Signature)
	if !ok {
		return
	}
	params := sig.Params()
	for i, arg := range call.Args {
		switch {
		case sig.Variadic() && i >= params.Len()-1 && call.Ellipsis.IsValid():
		case sig.Variadic() && i >= params.Len()-1:
			add(arg, params.At(params.Len()-1).Type().(*types.Slice).Elem())
		case i < params.Len():
			add(arg, params.At(i).Type())
		}
	}
}

// literalConversions adds the elements, keys, and fields of a composite
// literal that Go converts to their types.
func literalConversions(info *types.Info, lit *ast.CompositeLit, add func(e ast.Expr, to types.Type)) {
	t := info.TypeOf(lit)
	if t == nil {
		return
	}
	if p, ok := t.Underlying().(*types.Pointer); ok {
		t = p.Elem()
	}
	switch u := t.Underlying().(type) {
	case *types.Struct:
		for i, elt := range lit.Elts {
			if kv, ok := elt.(*ast.KeyValueExpr); ok {
				if key, ok := kv.Key.(*ast.Ident); ok {
					if field, ok := info.Uses[key].(*types.Var); ok {
						add(kv.Value, field.Type())
					}
				}
				continue
			}
			if i < u.NumFields() {
				add(elt, u.Field(i).Type())
			}
		}
	case *types.Slice, *types.Array, *types.Map:
		var key, elem types.Type
		switch u := u.(type) {
		case *types.Slice:
			elem = u.Elem()
		case *types.Array:
			elem = u.Elem()
		case *types.Map:
			key, elem = u.Key(), u.Elem()
		}
		for _, elt := range lit.Elts {
			if kv, ok := elt.(*ast.KeyValueExpr); ok {
				if key != nil {
					add(kv.Key, key)
				}
				add(kv.Value, elem)
				continue
			}
			add(elt, elem)
		}
	}
}
