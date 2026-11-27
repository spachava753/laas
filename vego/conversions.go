package vego

import (
	"go/ast"
	"go/token"
	"go/types"
	"slices"

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
// So the conversions of a package are listed by walking the contexts in
// which the specification lets a value be assigned to something of another
// type (syntacticConversions), and the verifier stops with an internal
// error when it evaluates a listed expression anywhere but where the
// conversion is checked (evalConverted), or for another target type.
//
// The type checker keeps no record of implicit conversions. go/ssa does:
// every conversion to an interface type is a MakeInterface instruction,
// and in debug mode every expression whose value is computed gets a
// DebugRef to its value. But one value can carry several expressions, as x
// does in p, t = x, x, and nothing says which of them a MakeInterface
// converts. So go/ssa confirms the walk and does not add to it: each
// MakeInterface of a value that is not a constant must have, among the
// DebugRefs of its operand before it in its block, an expression that the
// walk lists. A function where one does not, or where one converts a value
// without any expression, such as one result of a call with several,
// cannot be verified (see unplaced). A test checks both directions on the
// corpus: what go/ssa converts has a listed expression, and every listed
// expression that is not a constant is a candidate of a conversion go/ssa
// makes.

// conversions is what the walk and go/ssa say of a package.
type conversions struct {
	// converted holds every expression that Go converts to an interface
	// type where it stands, with the type it is converted to; a switch tag
	// may be converted to several.
	converted map[ast.Expr][]types.Type
	// unplaced holds, for the function declaration around it, the position
	// of each conversion that go/ssa makes and that no expression the walk
	// lists accounts for. inInit holds the positions of those in the
	// initialisers of package-level variables, outside every function
	// declaration; a position is not valid when go/ssa gives none.
	unplaced map[*ast.FuncDecl][]token.Pos
	inInit   []token.Pos
}

// findConversions lists the conversions of the package.
func (pv *pkgVerifier) findConversions() *conversions {
	if pv.conversions != nil {
		return pv.conversions
	}
	found := &conversions{converted: map[ast.Expr][]types.Type{}, unplaced: map[*ast.FuncDecl][]token.Pos{}}
	for _, file := range pv.pass.Files {
		for e, targets := range syntacticConversions(pv.info, file) {
			found.converted[e] = append(found.converted[e], targets...)
		}
	}
	for _, conversion := range conversionsIn(pv.ssaProgram(), pv.pass.Pkg, pv.pass.Files, pv.info) {
		if conversion.constant || slices.ContainsFunc(conversion.candidates, func(e ast.Expr) bool { return found.converted[e] != nil }) {
			continue
		}
		at := conversion.at
		if !at.IsValid() && conversion.fn != nil {
			at = conversion.fn.Pos()
		}
		inDecl := false
		for _, file := range pv.pass.Files {
			for _, decl := range file.Decls {
				if fd, ok := decl.(*ast.FuncDecl); ok && conversion.fn != nil && fd.Pos() <= conversion.fn.Pos() && conversion.fn.Pos() < fd.End() {
					found.unplaced[fd] = append(found.unplaced[fd], at)
					inDecl = true
				}
			}
		}
		if !inDecl {
			found.inInit = append(found.inInit, at)
		}
	}
	pv.conversions = found
	return found
}

// ssaProgram returns the package built in go/ssa, built once.
func (pv *pkgVerifier) ssaProgram() *ssa.Program {
	if pv.ssaProg == nil {
		// From the type information as the compiler gave it: a copy in
		// which calls of recursive closures resolve to functions of their
		// own (closures.go) is not one go/ssa can build.
		pv.ssaProg = buildSSA(pv.pass.Fset, pv.pass.Pkg, pv.pass.Files, pv.pass.TypesInfo)
	}
	return pv.ssaProg
}

// ssaConversion is a MakeInterface instruction of go/ssa: the function or
// literal it is in, the nearest position the instructions up to it give,
// what it converts, and the expressions whose DebugRef names its operand
// before it in its block. A constant has no DebugRef. fn is nil in the
// function go/ssa makes of the initialisers of package-level variables.
type ssaConversion struct {
	fn         ast.Node
	at         token.Pos
	what       string
	constant   bool
	candidates []ast.Expr
}

// buildSSA builds a package in go/ssa, with a DebugRef for every
// expression.
func buildSSA(fset *token.FileSet, pkg *types.Package, files []*ast.File, info *types.Info) *ssa.Program {
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
	prog.CreatePackage(pkg, files, info, false).Build()
	return prog
}

// ssaFunctions calls visit for every function declaration of the files
// with the function go/ssa built for it.
func ssaFunctions(prog *ssa.Program, files []*ast.File, info *types.Info, visit func(*ast.FuncDecl, *ssa.Function)) {
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
				visit(fd, fn)
			}
		}
	}
}

// conversionsIn returns the conversions to interface types of a package
// built in go/ssa: in its function declarations and in the initialisers of
// its package-level variables, which go/ssa puts in the init function it
// makes.
func conversionsIn(prog *ssa.Program, pkg *types.Package, files []*ast.File, info *types.Info) []ssaConversion {
	var found []ssaConversion
	var walk func(fn *ssa.Function)
	walk = func(fn *ssa.Function) {
		for _, block := range fn.Blocks {
			refs := map[ssa.Value][]ast.Expr{}
			for _, instr := range block.Instrs {
				switch instr := instr.(type) {
				case *ssa.DebugRef:
					if !instr.IsAddr {
						refs[instr.X] = append(refs[instr.X], ast.Unparen(instr.Expr))
					}
				case *ssa.MakeInterface:
					_, constant := instr.X.(*ssa.Const)
					found = append(found, ssaConversion{fn: fn.Syntax(), at: nearestPos(block.Instrs, instr), what: instr.X.String(),
						constant: constant, candidates: slices.Clone(refs[instr.X])})
				}
			}
		}
		for _, anon := range fn.AnonFuncs {
			walk(anon)
		}
	}
	ssaFunctions(prog, files, info, func(_ *ast.FuncDecl, fn *ssa.Function) { walk(fn) })
	if init := prog.Package(pkg).Func("init"); init != nil {
		walk(init)
	}
	return found
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
// to an interface type where they stand, with the types they are converted
// to, found by the contexts in which
// the specification lets a value be assigned to something of another type.
// One result of a call with several, an element that a range assigns, and
// a value that a comma-ok form gives have no expression of their own and
// are not listed.
func syntacticConversions(info *types.Info, root ast.Node) map[ast.Expr][]types.Type {
	found := map[ast.Expr][]types.Type{}
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
		found[e] = append(found[e], to)
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
		// The initialisers of package-level variables, which
		// checkValueInitialisers checks as verified code.
		if gen, ok := n.(*ast.GenDecl); ok && gen.Tok == token.VAR {
			walk(gen, nil)
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
