package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"os"
	"path/filepath"
	"strings"
	"unicode"
	"unicode/utf8"
)

// Package-level variables.
//
// A package-level variable is changed when code of the build assigns it,
// takes its address, or names it in a directive or in assembly; see
// findChanges. A variable that nothing changes holds, from the end of its
// initialisation on, the value it was initialised with.
//
// What a variable refers to is a separate matter: table[0] = 5 assigns no
// variable. Every use of a variable that does more than read a value out of
// it is noted as well, as an escape, since from there on something else may
// hold a reference to what the variable refers to.

// findChanges walks every file of the package, code that is not verified
// included, and records what changes a package-level variable or lets a
// reference to what it refers to out of it, for the variables of this
// package and of others. A change of a variable of another package is
// published, so that a proof that relies on it can meet it; see
// reportSentinelWrites. Uses are read from what the type checker records,
// so a variable named in an initialiser, an init function, a function
// literal, a defer or go statement, or generic code counts like any other.
func (pv *pkgVerifier) findChanges() {
	pv.reassigned = map[*types.Var]bool{}
	pv.ownChanges = map[*types.Var]string{}
	pv.changeOf = map[*types.Var]string{}
	pv.escapes = map[*types.Var]string{}
	at := func(pos token.Pos) string {
		position := pv.pass.Fset.Position(pos)
		return fmt.Sprintf("%s:%d", filepath.Base(position.Filename), position.Line)
	}
	changed := func(variable *types.Var, what string, pos token.Pos) {
		pv.reassigned[variable] = true
		if pv.changeOf[variable] == "" {
			pv.changeOf[variable] = what + " at " + at(pos)
		}
		if variable.Pkg() == pv.pass.Pkg && pv.ownChanges[variable] == "" {
			pv.ownChanges[variable] = what + " at " + at(pos)
		}
		// A proof in another package may rest on the value of a variable
		// of another package.
		if _, published := pv.foreignSentinel(variable); published {
			pv.writes = append(pv.writes, sentinelWrite{
				Key: errorKey(variable), Name: variable.Pkg().Name() + "." + variable.Name(), Package: pv.pass.Pkg.Path(),
				At: at(pos), pos: pos,
			})
		}
	}
	escaped := func(variable *types.Var, pos token.Pos) {
		if pv.escapes[variable] == "" {
			pv.escapes[variable] = at(pos)
		}
	}
	for _, file := range pv.pass.Files {
		pv.linknames(file, changed)
	}
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
			variable, ok := pv.info.Uses[id].(*types.Var)
			if !ok || variable.Pkg() == nil || variable.Parent() != variable.Pkg().Scope() {
				return true
			}
			switch use := pv.useOf(stack); {
			case use.change != "":
				changed(variable, use.change, use.pos)
				escaped(variable, use.pos)
			case use.escape:
				escaped(variable, use.pos)
			}
			return true
		})
	}
	pv.assemblyReferences(changed)
}

// use is what one use of a package-level variable does with it: change says
// how it changes the variable, if it does, and escape is set when it lets a
// reference to what the variable refers to out of it. pos is where.
type use struct {
	change string
	escape bool
	pos    token.Pos
}

// useOf decides what the use of a variable at the end of stack does. It
// follows the expression around the name outwards. As long as the path
// stays inside the value of the variable (fields of a struct, elements of
// an array), assigning to it or taking its address changes the variable;
// once it passes through a pointer, a slice, or a map it is in memory the
// variable refers to, and assigning there writes that memory. Only a path
// of fields and elements that ends where a value without references is
// read, the argument of len or cap, or what a range clause ranges over is
// a read; anything else is an escape. That is a list of what is allowed, so
// a form the walk does not know is an escape.
func (pv *pkgVerifier) useOf(stack []ast.Node) use {
	i := len(stack) - 1
	var cur ast.Expr = stack[i].(*ast.Ident)
	// A variable of another package is selected from its package name.
	if i > 0 {
		if sel, ok := stack[i-1].(*ast.SelectorExpr); ok && sel.Sel == cur {
			cur, i = sel, i-1
		}
	}
	inValue := true
	escape := use{escape: true, pos: cur.Pos()}
	for i--; i >= 0; i-- {
		switch parent := stack[i].(type) {
		case *ast.ParenExpr:
			cur = parent
			continue
		case *ast.SelectorExpr:
			if parent.X != cur {
				return escape
			}
			selection := pv.info.Selections[parent]
			if selection == nil {
				return escape
			}
			if selection.Kind() != types.FieldVal {
				// A method with a pointer receiver selected on a value
				// takes its address, for a call, a method value, defer,
				// and go alike, and through embedded fields as well.
				signature, _ := selection.Obj().Type().(*types.Signature)
				_, pointerRecv := signature.Recv().Type().Underlying().(*types.Pointer)
				_, onPointer := pv.info.TypeOf(cur).Underlying().(*types.Pointer)
				if inValue && pointerRecv && !onPointer && !selection.Indirect() {
					return use{change: "has its address taken", escape: true, pos: parent.Sel.Pos()}
				}
				return escape
			}
			if _, onPointer := pv.info.TypeOf(cur).Underlying().(*types.Pointer); onPointer || selection.Indirect() {
				inValue = false
			}
			cur = parent
			continue
		case *ast.IndexExpr:
			if parent.X != cur {
				return pv.readOf(cur, inValue, escape)
			}
			switch pv.info.TypeOf(cur).Underlying().(type) {
			case *types.Array:
			case *types.Basic:
				// A byte of a string is a value.
			default:
				inValue = false
			}
			cur = parent
			continue
		case *ast.StarExpr:
			inValue = false
			cur = parent
			continue
		case *ast.SliceExpr:
			if parent.X != cur {
				return pv.readOf(cur, inValue, escape)
			}
			switch pv.info.TypeOf(cur).Underlying().(type) {
			case *types.Basic:
				cur = parent
				continue
			case *types.Array:
				if inValue {
					return use{change: "has its address taken", escape: true, pos: parent.Pos()}
				}
			}
			return escape
		case *ast.UnaryExpr:
			if parent.Op == token.AND {
				if inValue {
					return use{change: "has its address taken", escape: true, pos: parent.Pos()}
				}
				return escape
			}
			return pv.readOf(cur, inValue, escape)
		case *ast.AssignStmt:
			for _, lhs := range parent.Lhs {
				if lhs == cur {
					if inValue {
						return use{change: "is assigned", escape: true, pos: cur.Pos()}
					}
					return escape
				}
			}
			return pv.readOf(cur, inValue, escape)
		case *ast.IncDecStmt:
			if inValue {
				return use{change: "is assigned", escape: true, pos: cur.Pos()}
			}
			return escape
		case *ast.RangeStmt:
			if parent.Key == cur || parent.Value == cur {
				if inValue {
					return use{change: "is assigned", escape: true, pos: cur.Pos()}
				}
				return escape
			}
			if parent.X == cur && pv.rangeCopies(pv.info.TypeOf(cur)) {
				return use{pos: cur.Pos()}
			}
			return escape
		case *ast.CallExpr:
			if id, ok := ast.Unparen(parent.Fun).(*ast.Ident); ok && len(parent.Args) == 1 && parent.Args[0] == cur {
				if builtin, ok := pv.info.Uses[id].(*types.Builtin); ok && (builtin.Name() == "len" || builtin.Name() == "cap") {
					return use{pos: cur.Pos()}
				}
			}
			return pv.readOf(cur, inValue, escape)
		default:
			return pv.readOf(cur, inValue, escape)
		}
	}
	return escape
}

// readOf decides a use that ends at cur: a read of a value without
// references is a read, and anything else an escape. The index of a map
// that gives two results, as in v, ok := m[k], has the type of a tuple,
// which is read when both of its parts are.
func (pv *pkgVerifier) readOf(cur ast.Expr, inValue bool, escape use) use {
	t := pv.info.TypeOf(cur)
	if tuple, ok := t.(*types.Tuple); ok {
		for part := range tuple.Variables() {
			if !flat(part.Type(), map[types.Type]bool{}) {
				return escape
			}
		}
		return use{pos: cur.Pos()}
	}
	if flat(t, map[types.Type]bool{}) {
		return use{pos: cur.Pos()}
	}
	return escape
}

// rangeCopies reports whether each iteration of a range over a value of
// the type copies out only values without references: the keys and
// values of a map, the elements of a slice or an array, the bytes and
// runes of a string, or the numbers up to an integer. Ranging over a
// function calls it.
func (pv *pkgVerifier) rangeCopies(t types.Type) bool {
	switch u := t.Underlying().(type) {
	case *types.Basic:
		return true
	case *types.Slice:
		return flat(u.Elem(), map[types.Type]bool{})
	case *types.Array:
		return flat(u.Elem(), map[types.Type]bool{})
	case *types.Pointer:
		array, ok := u.Elem().Underlying().(*types.Array)
		return ok && flat(array.Elem(), map[types.Type]bool{})
	case *types.Map:
		return flat(u.Key(), map[types.Type]bool{}) && flat(u.Elem(), map[types.Type]bool{})
	}
	return false
}

// flat reports whether a value of the type holds no reference at any
// depth, so that reading it copies everything it is: a basic type other
// than unsafe.Pointer, or an array or struct of such types.
func flat(t types.Type, seen map[types.Type]bool) bool {
	if t == nil {
		return false
	}
	if seen[t] {
		return true
	}
	seen[t] = true
	switch u := t.Underlying().(type) {
	case *types.Basic:
		return u.Kind() != types.UnsafePointer && u.Kind() != types.UntypedNil
	case *types.Array:
		return flat(u.Elem(), seen)
	case *types.Struct:
		for field := range u.Fields() {
			if !flat(field.Type(), seen) {
				return false
			}
		}
		return true
	}
	return false
}

// linknames records the variables that the go:linkname directives of a
// file name. The local name of a directive is changed, since the directive
// lets the linker give it the storage of another symbol, or another package
// that storage. The target of a directive with two names is published as
// changed whatever it names, so that the direction of the directive is not
// read at all: a variable of one package that is the storage of a variable
// of another is changed in both.
func (pv *pkgVerifier) linknames(file *ast.File, changed func(*types.Var, string, token.Pos)) {
	for _, group := range file.Comments {
		for _, c := range group.List {
			fields := strings.Fields(c.Text)
			if len(fields) < 2 || fields[0] != "//go:linkname" {
				continue
			}
			const what = "is named by a go:linkname directive"
			if variable, ok := pv.pass.Pkg.Scope().Lookup(fields[1]).(*types.Var); ok {
				changed(variable, what, c.Pos())
			}
			if len(fields) < 3 {
				continue
			}
			pv.changedByKey(fields[2], what, c.Pos(), changed)
		}
	}
}

// changedByKey records a change of the variable a full name such as
// example.com/a.N names: one of this package or of the build is changed,
// and a name that cannot be looked up here is published as written, since
// a package that can look it up may rely on it.
func (pv *pkgVerifier) changedByKey(key, what string, pos token.Pos, changed func(*types.Var, string, token.Pos)) {
	if variable := pv.lookupKey(key); variable != nil {
		if variable.Parent() == variable.Pkg().Scope() {
			changed(variable, what, pos)
		}
		return
	}
	dot := strings.LastIndex(key, ".")
	if dot <= 0 || pv.lookupPackage(key[:dot]) != nil {
		return
	}
	position := pv.pass.Fset.Position(pos)
	pv.writes = append(pv.writes, sentinelWrite{
		Key: key, Name: filepath.Base(key[:dot]) + key[dot:], Package: pv.pass.Pkg.Path(),
		At: fmt.Sprintf("%s:%d", filepath.Base(position.Filename), position.Line), pos: pos,
	})
}

// assemblyReferences records the package-level variables that the other
// files of the package, assembly and headers alike, refer to. In assembly
// a symbol is spelled with a middle dot for the dot before the name and a
// division slash for each slash of the path, as in example·com∕x·N, and a
// name that starts with the dot is of the package itself. Any reference
// counts as a change, read or write, since which it is cannot be told.
func (pv *pkgVerifier) assemblyReferences(changed func(*types.Var, string, token.Pos)) {
	for _, name := range pv.pass.OtherFiles {
		text, err := os.ReadFile(name)
		if err != nil {
			continue
		}
		file := pv.pass.Fset.AddFile(name, -1, len(text))
		file.SetLinesForContent(text)
		const what = "is referred to in assembly"
		symbol := func(r rune) bool {
			return unicode.IsLetter(r) || unicode.IsDigit(r) || r == '_' || r == '·' || r == '∕' || r == '.' || r == '/'
		}
		for start := 0; start < len(text); {
			end := start
			for end < len(text) {
				r, size := utf8.DecodeRune(text[end:])
				if !symbol(r) {
					break
				}
				end += size
			}
			if end == start {
				start++
				continue
			}
			token := string(text[start:end])
			pos := file.Pos(start)
			start = end
			if !strings.Contains(token, "·") {
				continue
			}
			key := strings.NewReplacer("·", ".", "∕", "/").Replace(token)
			if strings.HasPrefix(key, ".") {
				if variable, ok := pv.pass.Pkg.Scope().Lookup(key[1:]).(*types.Var); ok {
					changed(variable, what, pos)
				}
				continue
			}
			pv.changedByKey(key, what, pos, changed)
		}
	}
}
