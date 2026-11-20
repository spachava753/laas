package vego

import (
	"errors"
	"fmt"
	"go/ast"
	"go/constant"
	"go/token"
	"go/types"
	"maps"
	"math/big"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"unicode"
	"unicode/utf8"

	"github.com/spachava753/laas/vego/internal/logic"
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
		_, sentinel := pv.foreignSentinel(variable)
		if _, fixed := pv.foreignFixed(variable); sentinel || fixed {
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
		// A proof in another package may rest on what a variable of
		// another package refers to being only read.
		if fact := pv.publishedFixed(variable); fact != nil && fact.ReadOnly[variable.Name()] {
			pv.writes = append(pv.writes, sentinelWrite{
				Key: errorKey(variable) + contentsKey, Name: variable.Pkg().Name() + "." + variable.Name(), Package: pv.pass.Pkg.Path(),
				At: at(pos), pos: pos,
			})
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
		case *ast.BinaryExpr:
			// A comparison with nil reads the value and lets nothing out.
			other := parent.X
			if other == cur {
				other = parent.Y
			}
			if (parent.Op == token.EQL || parent.Op == token.NEQ) && pv.info.Types[other].IsNil() {
				return use{pos: cur.Pos()}
			}
			return pv.readOf(cur, inValue, escape)
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

// fixedFact lists, by name, the package-level variables of a package that
// are not of type error and that nothing in the package changes, with what
// their initialisers give, and says of every other such variable what
// changes it. Error variables have sentinelsFact. It is a fact about the
// package so that it reaches every package built with this one.
type fixedFact struct {
	Vars    map[string]knownValue
	Changed map[string]string
	// ReadOnly holds those of Vars whose contents are only read; see
	// readOnly.
	ReadOnly map[string]bool
}

func (*fixedFact) AFact() {}

func (f *fixedFact) String() string { return fmt.Sprintf("fixed(%d)", len(f.Vars)) }

// knownKind says what the initialiser of a fixed variable gives.
type knownKind int

const (
	// knownNothing: a value of the type, of which nothing more is known.
	knownNothing knownKind = iota
	// knownZero: the zero value of the type; there is no initialiser.
	knownZero
	// knownConstant: the constant Text, of kind Constant.
	knownConstant
	// knownStruct: a struct whose fields Parts gives, one per field of
	// the struct type, blank fields included.
	knownStruct
	// knownMade: a slice, a map, or a pointer the initialiser made, so not
	// nil, at a new allocation. A slice has the length Len and capacity
	// Cap where they are not negative. Sized is set when the allocation
	// has a size, so that it is apart from every other one.
	knownMade
	// knownAlias: the value of the variable with key Alias.
	knownAlias
)

// knownValue is what is known of a value from the initialiser of a fixed
// variable, read from source.
type knownValue struct {
	Kind     knownKind
	Text     string
	Constant constant.Kind
	Parts    []knownValue
	Len, Cap int64
	Sized    bool
	Alias    string
	// Elems is what a made slice, map, or pointer holds when it was made:
	// the elements of a slice at the positions Indices gives, the values
	// of a map under the keys Keys gives, or the struct a pointer points
	// to. Contents is set when that is all it holds, as for a literal.
	Elems    []knownValue
	Indices  []int64
	Keys     []knownValue
	Contents bool
}

// findFixed records the package-level variables of the package that are
// not errors and that nothing changes, with what each initialiser gives,
// and publishes them. It runs after findChanges and findSentinels.
func (pv *pkgVerifier) findFixed() {
	pv.fixed = map[*types.Var]knownValue{}
	pv.readOnly = map[*types.Var]bool{}
	embeds := pv.embedded()
	fact := &fixedFact{Vars: map[string]knownValue{}, Changed: map[string]string{}, ReadOnly: map[string]bool{}}
	initialised := false
	for _, file := range pv.pass.Files {
		for _, decl := range file.Decls {
			gen, ok := decl.(*ast.GenDecl)
			if !ok || gen.Tok != token.VAR {
				continue
			}
			for _, spec := range gen.Specs {
				spec := spec.(*ast.ValueSpec)
				for i, name := range spec.Names {
					variable, _ := pv.info.Defs[name].(*types.Var)
					if variable == nil || isError(variable.Type()) {
						continue
					}
					if pv.reassigned[variable] {
						fact.Changed[variable.Name()] = pv.ownChanges[variable]
						continue
					}
					known := knownValue{Kind: knownZero}
					switch {
					case embeds[spec]:
						// The value is the content of files, which the
						// directive names and the source does not hold.
						known = knownValue{}
					case len(spec.Values) == len(spec.Names):
						known = pv.knownOf(spec.Values[i], variable.Type(), true)
						initialised = true
					case len(spec.Values) > 0:
						known = knownValue{}
						initialised = true
					}
					pv.fixed[variable] = known
					fact.Vars[variable.Name()] = known
					if known.Kind == knownMade && pv.escapes[variable] == "" {
						pv.readOnly[variable] = true
						fact.ReadOnly[variable.Name()] = true
					}
				}
			}
		}
	}
	if len(fact.Vars) > 0 || len(fact.Changed) > 0 {
		pv.pass.ExportPackageFact(fact)
	}
	// Code that Go's order of initialisation does not see may run a
	// function of the package before a variable has its value.
	if initialised {
		pv.hidden = pv.hiddenInitCode()
	}
}

// maxKnownElems bounds the elements, or keys, of a literal whose contents
// are recorded, so that what a package publishes stays small: generated
// tables of thousands of entries are read as tables of unknown contents.
const maxKnownElems = 1024

// knownOf reads what an initialiser of a variable of type t gives, or with
// top unset what a part of it gives. The contents of what it makes are
// recorded only for the initialiser itself, and not for what is made
// inside it, which no read of the
// variable reaches without passing through memory that is not only read.
func (pv *pkgVerifier) knownOf(e ast.Expr, t types.Type, top bool) knownValue {
	e = ast.Unparen(e)
	if tv := pv.info.Types[e]; tv.Value != nil {
		return knownConstantOf(tv.Value)
	}
	sized := func(elem types.Type) bool { return pv.pass.TypesSizes.Sizeof(elem) > 0 }
	switch e := e.(type) {
	case *ast.CompositeLit:
		switch u := t.Underlying().(type) {
		case *types.Struct:
			parts := make([]knownValue, u.NumFields())
			for i := range parts {
				parts[i] = knownValue{Kind: knownZero}
			}
			for i, elt := range e.Elts {
				index, value := i, elt
				if kv, ok := elt.(*ast.KeyValueExpr); ok {
					value = kv.Value
					key, _ := kv.Key.(*ast.Ident)
					index = -1
					for j := range u.NumFields() {
						if key != nil && u.Field(j).Name() == key.Name {
							index = j
						}
					}
				}
				if index < 0 || index >= len(parts) {
					return knownValue{}
				}
				parts[index] = pv.knownOf(value, u.Field(index).Type(), false)
			}
			return knownValue{Kind: knownStruct, Parts: parts}
		case *types.Slice:
			made := knownValue{Kind: knownMade, Contents: top && len(e.Elts) <= maxKnownElems}
			length, next := int64(0), int64(0)
			for _, elt := range e.Elts {
				value := elt
				if kv, ok := elt.(*ast.KeyValueExpr); ok {
					index, exact := constant.Int64Val(constant.ToInt(pv.info.Types[kv.Key].Value))
					if !exact {
						return knownValue{}
					}
					next, value = index, kv.Value
				}
				if made.Contents {
					made.Elems = append(made.Elems, pv.knownOf(value, u.Elem(), false))
					made.Indices = append(made.Indices, next)
				}
				next++
				length = max(length, next)
			}
			made.Len, made.Cap, made.Sized = length, length, length > 0 && sized(u.Elem())
			return made
		case *types.Map:
			made := knownValue{Kind: knownMade, Len: -1, Cap: -1, Sized: true, Contents: top && len(e.Elts) <= maxKnownElems}
			for _, elt := range e.Elts {
				kv, ok := elt.(*ast.KeyValueExpr)
				if !ok || !made.Contents {
					break
				}
				made.Keys = append(made.Keys, pv.knownOf(kv.Key, u.Key(), false))
				made.Elems = append(made.Elems, pv.knownOf(kv.Value, u.Elem(), false))
			}
			return made
		}
	case *ast.UnaryExpr:
		if _, ok := ast.Unparen(e.X).(*ast.CompositeLit); ok && e.Op == token.AND {
			if object, ok := pointee(t); ok {
				made := knownValue{Kind: knownMade, Len: -1, Cap: -1, Sized: sized(object), Contents: top}
				if top {
					made.Elems = []knownValue{pv.knownOf(e.X, object, false)}
				}
				return made
			}
		}
	case *ast.CallExpr:
		size := func(i int) int64 {
			if i >= len(e.Args) {
				return -1
			}
			if value := pv.info.Types[e.Args[i]].Value; value != nil {
				if n, exact := constant.Int64Val(constant.ToInt(value)); exact {
					return n
				}
			}
			return -1
		}
		id, _ := ast.Unparen(e.Fun).(*ast.Ident)
		builtin, _ := pv.info.Uses[id].(*types.Builtin)
		switch {
		case builtin != nil && builtin.Name() == "make":
			switch u := t.Underlying().(type) {
			case *types.Slice:
				length, capacity := size(1), size(1)
				if len(e.Args) > 2 {
					capacity = size(2)
				}
				return knownValue{Kind: knownMade, Len: length, Cap: capacity, Sized: capacity > 0 && sized(u.Elem())}
			case *types.Map:
				return knownValue{Kind: knownMade, Len: -1, Cap: -1, Sized: true}
			}
		case builtin != nil && builtin.Name() == "new":
			if object, ok := pointee(t); ok {
				return knownValue{Kind: knownMade, Len: -1, Cap: -1, Sized: sized(object)}
			}
		case pv.info.Types[e.Fun].IsType() && len(e.Args) == 1:
			// []byte of a constant string is a new array of its bytes, and
			// []rune one of the code points that ranging over the string
			// gives, with U+FFFD for each byte that is not valid UTF-8, as
			// the conversion does. The runtime rounds the capacity up.
			value := pv.info.Types[e.Args[0]].Value
			if u, ok := t.Underlying().(*types.Slice); ok && value != nil && value.Kind() == constant.String {
				var elems []int64
				switch basic, _ := u.Elem().Underlying().(*types.Basic); {
				case basic != nil && basic.Kind() == types.Byte:
					for _, b := range []byte(constant.StringVal(value)) {
						elems = append(elems, int64(b))
					}
				case basic != nil && basic.Kind() == types.Rune:
					for _, r := range constant.StringVal(value) {
						elems = append(elems, int64(r))
					}
				default:
					return knownValue{}
				}
				made := knownValue{Kind: knownMade, Len: int64(len(elems)), Cap: -1, Sized: len(elems) > 0 && sized(u.Elem()),
					Contents: top && len(elems) <= maxKnownElems}
				for i, elem := range elems {
					if made.Contents {
						made.Elems = append(made.Elems, knownConstantOf(constant.MakeInt64(elem)))
						made.Indices = append(made.Indices, int64(i))
					}
				}
				return made
			}
		}
	case *ast.Ident, *ast.SelectorExpr:
		if variable := pv.namedVariable(e); variable != nil && variable.Pkg() != nil && variable.Parent() == variable.Pkg().Scope() {
			return knownValue{Kind: knownAlias, Alias: errorKey(variable)}
		}
	}
	return knownValue{}
}

// knownConstantOf records a constant.
func knownConstantOf(value constant.Value) knownValue {
	text := value.ExactString()
	switch value.Kind() {
	case constant.String:
		text = constant.StringVal(value)
	case constant.Int:
		text = constant.ToInt(value).ExactString()
	}
	return knownValue{Kind: knownConstant, Text: text, Constant: value.Kind()}
}

// publishedFixed returns what the package of a variable of another package
// published about its fixed variables, or nil.
func (pv *pkgVerifier) publishedFixed(variable *types.Var) *fixedFact {
	pkg := variable.Pkg()
	if pkg == nil || pkg == pv.pass.Pkg || variable.Parent() != pkg.Scope() || isError(variable.Type()) {
		return nil
	}
	if pv.fixedOf == nil {
		pv.fixedOf = map[*types.Package]*fixedFact{}
	}
	fact, done := pv.fixedOf[pkg]
	if !done {
		fact = new(fixedFact)
		if !pv.pass.ImportPackageFact(pkg, fact) {
			fact = nil
		}
		pv.fixedOf[pkg] = fact
	}
	return fact
}

// foreignFixed returns what the package of a variable of another package
// published about it as a fixed variable, if anything.
func (pv *pkgVerifier) foreignFixed(variable *types.Var) (knownValue, bool) {
	fact := pv.publishedFixed(variable)
	if fact == nil {
		return knownValue{}, false
	}
	known, ok := fact.Vars[variable.Name()]
	return known, ok
}

// changedNotYet ends the messages about variables that a later part
// supports.
const changedNotYet = "package-level variables that are changed are not supported yet"

// usableFixed reports what is known of a package-level variable that is
// not an error and that a function reads, or why it cannot be read.
func (pv *pkgVerifier) usableFixed(variable *types.Var) (knownValue, string) {
	spelled := pv.spelling(variable)
	t := variable.Type()
	if _, ok := layoutOf(t); !ok {
		return knownValue{}, fmt.Sprintf("%s has type %s, which is not supported%s", spelled, t, unsupportedHint(t))
	}
	if !pv.dataType(t, map[types.Type]bool{}) {
		return knownValue{}, fmt.Sprintf("%s has type %s, which can hold a function value, an interface value, an error, a channel, or an unsafe.Pointer; "+
			"package-level variables of such types are not supported yet", spelled, t)
	}
	var known knownValue
	switch {
	case variable.Pkg() == pv.pass.Pkg && pv.reassigned[variable]:
		return knownValue{}, fmt.Sprintf("%s %s; %s", spelled, pv.ownChanges[variable], changedNotYet)
	case variable.Pkg() == pv.pass.Pkg:
		known = pv.fixed[variable]
		if pv.hidden != "" && known.Kind != knownZero {
			return knownValue{}, fmt.Sprintf("%s is not known to have its value yet when this runs: %s while the variables of the package are "+
				"initialised, which may run this function first", spelled, pv.hidden)
		}
	case pv.reassigned[variable]:
		return knownValue{}, fmt.Sprintf("%s is changed in this package; %s", spelled, changedNotYet)
	default:
		var published bool
		known, published = pv.foreignFixed(variable)
		if !published {
			if fact := pv.publishedFixed(variable); fact != nil && fact.Changed[variable.Name()] != "" {
				return knownValue{}, fmt.Sprintf("%s %s in package %s; %s", spelled, fact.Changed[variable.Name()], variable.Pkg().Path(), changedNotYet)
			}
			return knownValue{}, fmt.Sprintf("%s is a variable of package %s that is not known to keep its value", spelled, variable.Pkg().Path())
		}
	}
	if write, changed := pv.writtenInBuild()[errorKey(variable)]; changed {
		return knownValue{}, fmt.Sprintf("%s is changed at %s in package %s, which this package is built with; %s", spelled, write.At, write.Package, changedNotYet)
	}
	return known, ""
}

// dataType reports whether a value of the type, and the memory it refers
// to at any depth, can hold no code: no function value, interface value,
// error, channel, or unsafe.Pointer. The unexported fields of a struct type
// of another package count too: verified code cannot read them, but it can
// hand the value to a trusted function that runs the code they hold, as a
// *log.Logger holds the writer its initialiser gave it.
func (pv *pkgVerifier) dataType(t types.Type, seen map[types.Type]bool) bool {
	if seen[t] {
		return true
	}
	seen[t] = true
	switch u := t.Underlying().(type) {
	case *types.Basic:
		return u.Kind() != types.UnsafePointer
	case *types.Pointer:
		return pv.dataType(u.Elem(), seen)
	case *types.Slice:
		return pv.dataType(u.Elem(), seen)
	case *types.Array:
		return pv.dataType(u.Elem(), seen)
	case *types.Map:
		return pv.dataType(u.Key(), seen) && pv.dataType(u.Elem(), seen)
	case *types.Struct:
		for field := range u.Fields() {
			if !pv.dataType(field.Type(), seen) {
				return false
			}
		}
		return true
	}
	return false
}

// fixedName begins the names of the constants that stand for the leaves of
// fixed variables, as it does those of sentinels.
const fixedName = sentinelName

// isFixedTerm reports whether a term is a constant that stands for the
// value of a package-level variable that keeps its value, or for what such
// a variable refers to: the same in every function and every package.
func isFixedTerm(t *logic.Term) bool {
	return t.Op == logic.OpConst && strings.HasPrefix(t.Name, fixedName)
}

// packageVariable reads a package-level variable in a body: an error
// variable as a sentinel, and any other as a fixed variable.
func (v *fnVerifier) packageVariable(variable *types.Var, pos token.Pos, st *state) value {
	if isError(variable.Type()) {
		sentinel, why := v.sentinelTerm(st, variable)
		if why != "" {
			v.unsupported(pos, why)
		}
		return value{sentinel}
	}
	val, why := v.fixedValue(st, variable)
	if why != "" {
		v.unsupported(pos, why)
	}
	return val
}

// fixedValue returns the value of a fixed variable that is not an error,
// noting in sink, which may be nil, what is known of it, or why it cannot
// be read.
func (v *fnVerifier) fixedValue(sink *state, variable *types.Var) (value, string) {
	known, why := v.usableFixed(variable)
	if why != "" {
		return nil, why
	}
	keys := []string{errorKey(variable)}
	// A variable that holds the value of another fixed variable is that
	// value; one that held the value of a variable that changes holds
	// what it was, of which nothing is known.
	final := variable
	for seen := map[*types.Var]bool{variable: true}; known.Kind == knownAlias; {
		target := v.lookupKey(known.Alias)
		if target == nil || seen[target] || isError(target.Type()) || !types.Identical(target.Type().Underlying(), variable.Type().Underlying()) {
			known = knownValue{}
			break
		}
		seen[target] = true
		next, why := v.usableFixed(target)
		if why != "" {
			known = knownValue{}
			break
		}
		final, known = target, next
		keys = append(keys, errorKey(target))
	}
	// A proof rests on the values of these variables, which are not
	// errors.
	for _, key := range keys {
		v.reliedKeys[key] = true
		v.reliedValues[key] = true
	}
	leaves := mustLayout(variable.Type())
	val := make(value, len(leaves))
	for i, lf := range leaves {
		val[i] = logic.Const(fixedName+errorKey(final)+lf.path, lf.sort)
	}
	if v.fixedMet == nil {
		v.fixedMet = map[string]fixedMet{}
	}
	for i, lf := range leaves {
		if lf.part == partRef || lf.part == partPtr || (lf.sort == logic.Ref && isMap(lf.typ)) {
			v.fixedRefs[val[i].Name] = v.spelling(variable)
		}
	}
	v.fixedMet[errorKey(final)] = fixedMet{val: val, typ: variable.Type()}
	readOnly := v.readOnlyHere(final)
	if !readOnly && known.Contents {
		v.noteLostContents(final)
	}
	if readOnly {
		v.reliedKeys[errorKey(final)+contentsKey] = true
		v.reliedValues[errorKey(final)+contentsKey] = true
		v.readOnlyRefs[val[0].Name] = errorKey(final)
	}
	if sink == nil || sink.noted["fixed "+errorKey(final)] {
		return val, ""
	}
	sink.noted["fixed "+errorKey(final)] = true
	v.declared(sink, v.wellFormed(val, variable.Type(), v.entryBrk))
	v.noteKnown(sink, val, variable.Type(), known)
	if readOnly && known.Contents {
		v.noteContents(sink, errorKey(final), val[0], variable.Type(), known)
	}
	return val, ""
}

// noteLostContents records that what a variable read in the function
// refers to is not known to stay as its initialiser made it, with the use
// that lets a reference to it out, for the message of an obligation that
// fails; see check.
func (v *fnVerifier) noteLostContents(variable *types.Var) {
	where := ""
	if at := v.escapes[variable]; at != "" {
		where = "the use at " + at
	} else if write, ok := v.writtenInBuild()[errorKey(variable)+contentsKey]; ok {
		where = fmt.Sprintf("the use at %s in package %s", write.At, write.Package)
	}
	if where == "" {
		return
	}
	note := fmt.Sprintf("the contents of %s are not known to stay as initialised: %s lets a reference to them out", v.spelling(variable), where)
	if !slices.Contains(v.lostContents, note) {
		v.lostContents = append(v.lostContents, note)
	}
}

// contentsKey ends the key under which a proof relies on what a variable
// refers to being only read, and under which a package publishes a use
// that lets a reference to it out.
const contentsKey = "[]"

// readOnlyHere reports whether what a fixed variable refers to is only
// read, as this package sees it: its initialiser made that memory, so the
// variable held the only reference to it, and every use in the build is a
// read of a value out of it, so it still does. Nothing writes that memory
// then, and no other reference in the program reaches it.
func (pv *pkgVerifier) readOnlyHere(variable *types.Var) bool {
	switch {
	case variable.Pkg() == pv.pass.Pkg:
		return pv.readOnly[variable]
	case pv.escapes[variable] != "":
		return false
	}
	fact := pv.publishedFixed(variable)
	if fact == nil || !fact.ReadOnly[variable.Name()] {
		return false
	}
	_, escaped := pv.writtenInBuild()[errorKey(variable)+contentsKey]
	return !escaped
}

// readOnlyRegion is the constant that stands for a region at the reference
// of a variable whose contents are only read, whatever memory holds.
func readOnlyRegion(variable, key string, sort logic.Sort) *logic.Term {
	return logic.Const(fixedName+variable+" in "+key, sort)
}

// noteContents states what the initialiser of a variable whose contents
// are only read put into them: the elements of a slice, the keys and
// values of a map, or the fields of the struct a pointer points to.
func (v *fnVerifier) noteContents(sink *state, variable string, ref *logic.Term, t types.Type, known knownValue) {
	row := func(key string, sort logic.Sort) *logic.Term {
		return logic.Select(readOnlyRegion(variable, key, logic.SeqOf(logic.SeqOf(sort))), ref)
	}
	at := func(object types.Type, start *logic.Term) value {
		cells := v.cellsOf(object)
		val := make(value, len(cells))
		for i, c := range cells {
			val[i] = logic.Select(row(c.key, c.sort), logic.Add(start, logic.IntLit(c.off)))
		}
		return val
	}
	switch u := t.Underlying().(type) {
	case *types.Slice:
		for j, elem := range known.Elems {
			v.noteKnown(sink, at(u.Elem(), logic.IntLit(known.Indices[j]*v.span(u.Elem()))), u.Elem(), elem)
		}
	case *types.Pointer:
		v.noteKnown(sink, at(u.Elem(), logic.IntLit(0)), u.Elem(), known.Elems[0])
	case *types.Map:
		keyType, elem := mapParts(t)
		keyLeaf := mustLayout(keyType)[0]
		var keys []*logic.Term
		for j, k := range known.Keys {
			if k.Kind != knownConstant {
				return
			}
			term := v.knownConstantTerm(sink, k, logic.Const(fmt.Sprintf("%s%s key %d", fixedName, variable, j), keyLeaf.sort))
			if term == nil {
				return
			}
			keys = append(keys, mapKey(term))
		}
		owner := mapOwner(t)
		has := row(owner+hasLeaf.path, hasLeaf.sort)
		leaves := mustLayout(elem)
		for j, key := range keys {
			v.declared(sink, logic.Select(has, key))
			held := make(value, len(leaves))
			for i, lf := range leaves {
				held[i] = logic.Select(row(owner+"#val"+lf.path, lf.sort), key)
			}
			v.noteKnown(sink, held, elem, known.Elems[j])
		}
		count := logic.Select(readOnlyRegion(variable, owner+countLeaf.path, logic.SeqOf(countLeaf.sort)), ref)
		v.declared(sink, logic.Eq(count, logic.IntLit(int64(len(keys)))))
		k := v.bound("k")
		others := make([]*logic.Term, len(keys))
		for j, key := range keys {
			others[j] = logic.Eq(k, key)
		}
		v.declared(sink, logic.Forall(k, logic.Implies(logic.Select(has, k), logic.Or(others...))))
	}
}

// declared notes a fact that the declaration of a fixed variable gives.
// It speaks of inputs alone, so it is part of the background of the
// function too, from which checkDeclaredRequires proves.
func (v *fnVerifier) declared(sink *state, fact *logic.Term) {
	v.fact(sink, fact)
}

// noteKnown notes what an initialiser gives of a value of type t.
func (v *fnVerifier) noteKnown(sink *state, val value, t types.Type, known knownValue) {
	switch known.Kind {
	case knownZero:
		for i, zero := range zeroValue(t) {
			v.declared(sink, v.same(val[i], zero))
		}
	case knownConstant:
		if term := v.knownConstantTerm(sink, known, val[0]); term != nil {
			v.declared(sink, v.same(val[0], term))
		}
	case knownStruct:
		u := t.Underlying().(*types.Struct)
		for i, part := range known.Parts {
			if lo, hi, ok := fieldLeaves(t, i); ok && i < u.NumFields() {
				v.noteKnown(sink, val[lo:hi], u.Field(i).Type(), part)
			}
		}
	case knownMade:
		ref := val[0]
		v.declared(sink, logic.Lt(logic.IntLit(0), ref))
		switch t.Underlying().(type) {
		case *types.Slice:
			v.declared(sink, logic.Eq(val[1], logic.IntLit(0)))
			if known.Len >= 0 {
				v.declared(sink, logic.Eq(val[2], logic.IntLit(known.Len)))
			}
			if known.Cap >= 0 {
				v.declared(sink, logic.Eq(val[3], logic.IntLit(known.Cap)))
			}
		case *types.Pointer:
			v.declared(sink, logic.Eq(val[1], logic.IntLit(0)))
		}
		if known.Sized {
			for _, other := range v.madeFixed {
				if other.Name != ref.Name {
					v.declared(sink, logic.Not(logic.Eq(ref, other)))
				}
			}
			if !slices.ContainsFunc(v.madeFixed, func(other *logic.Term) bool { return other.Name == ref.Name }) {
				v.madeFixed = append(v.madeFixed, ref)
			}
		}
	}
}

// knownConstantTerm returns the term for a constant an initialiser gives,
// or nil for one that a term of the sort cannot hold.
func (v *fnVerifier) knownConstantTerm(sink *state, known knownValue, leaf *logic.Term) *logic.Term {
	switch sort := leaf.Sort; {
	case sort == logic.Int && known.Constant == constant.Int:
		if number, ok := new(big.Int).SetString(known.Text, 10); ok {
			return logic.BigLit(number)
		}
	case sort == logic.Bool && known.Constant == constant.Bool:
		return logic.BoolLit(known.Text == "true")
	case sort == logic.Float:
		return logic.Const("float "+known.Text, logic.Float)
	case sort == logic.IntSeq && known.Constant == constant.String:
		if len(known.Text) <= maxLiteral {
			return logic.Bytes(known.Text)
		}
		long := logic.Const(leaf.Name+" text", logic.IntSeq)
		v.declared(sink, logic.Eq(logic.Len(long), logic.IntLit(int64(len(known.Text)))))
		return long
	}
	return nil
}

// locateVariable follows a path of an annotation that starts at a
// package-level variable that is not an error.
func (e *specEnv) locateVariable(variable *types.Var, steps []logic.Step, when logic.When) (reached, error) {
	spelled := e.v.spelling(variable)
	if when == logic.Old {
		return reached{}, fmt.Errorf("old(%s): %s is not a parameter", spelled, spelled)
	}
	val, why := e.v.fixedValue(e.sink, variable)
	if why != "" {
		return reached{}, errors.New(why)
	}
	hops, final, err := plan(variable.Type(), steps, e.writtenIn())
	if err != nil {
		return reached{}, fmt.Errorf("%s%v", spelled, err)
	}
	mem := e.now
	if when == logic.Primed {
		switch {
		case e.fn == nil:
			return reached{}, fmt.Errorf("%s' is only allowed in Ensures; inside a body %s already denotes the current value", spelled, spelled)
		case e.post == nil:
			return reached{}, fmt.Errorf("%s' describes the state on return and is only allowed in Ensures", spelled)
		case !reachesMemory(hops, final):
			return reached{}, fmt.Errorf("%s is a package-level variable that nothing changes, so it holds the same value on return; drop the prime", spelled)
		}
		mem = e.post
	}
	cur, ground := e.v.follow(e.sink, mem, val, hops)
	found := reached{val: cur, typ: final, mem: mem, hops: len(hops)}
	if ground {
		found.sink = e.sink
	}
	return found, nil
}

// callMemoryFree reports whether a call can be moved across a write to
// memory without changing what its contract says: it modifies nothing,
// its signature refers to no memory, and its contract names no
// package-level variable whose value refers to memory. Every call whose
// purity a unit records is judged here.
func (v *fnVerifier) callMemoryFree(fn *funcInfo, sig *types.Signature) bool {
	if len(fn.modifies) > 0 || !signatureMemoryFree(sig) {
		return false
	}
	return !slices.ContainsFunc(v.contractVariables(fn), func(variable *types.Var) bool { return !memoryFree(variable.Type()) })
}

// contractVariables returns the package-level variables a contract names:
// those an imported contract recorded, or those a contract in source names
// where it is written. A trusted contract names error variables only.
func (pv *pkgVerifier) contractVariables(fn *funcInfo) []*types.Var {
	spelled := fn.spelling()
	if pv.namedByContract == nil {
		pv.namedByContract = map[*funcInfo][]*types.Var{}
	}
	if found, done := pv.namedByContract[spelled]; done {
		return found
	}
	keys := map[string]string{}
	switch {
	case spelled.imported != nil:
		keys = spelled.imported.Errors
	case spelled.trust == nil && spelled.decl != nil:
		keys = pv.contractFactOf(spelled, spelled.decl.Pos()).Errors
	case spelled.trust == nil && spelled.obj != nil:
		keys = pv.contractFactOf(spelled, spelled.obj.Pos()).Errors
	}
	var found []*types.Var
	for _, spelling := range slices.Sorted(maps.Keys(keys)) {
		if variable := pv.lookupKey(keys[spelling]); variable != nil {
			found = append(found, variable)
		}
	}
	pv.namedByContract[spelled] = found
	return found
}

// packageRoot returns the package-level variable that an assignment target
// other than a variable itself is reached from, through fields, elements,
// and pointers, or nil, and whether the way passes through a pointer, a
// slice, or a map.
func (v *fnVerifier) packageRoot(e ast.Expr) (*types.Var, bool) {
	inMemory := false
	through := func(x ast.Expr) {
		switch v.info.TypeOf(x).Underlying().(type) {
		case *types.Pointer, *types.Slice, *types.Map:
			inMemory = true
		}
	}
	for first := true; ; first = false {
		switch x := ast.Unparen(e).(type) {
		case *ast.Ident:
			if variable := packageVariableOf(v.info.Uses[x], ""); variable != nil && !first {
				return variable, inMemory
			}
			return nil, false
		case *ast.SelectorExpr:
			if id, ok := x.X.(*ast.Ident); ok && v.isPackageName(id) {
				if variable := packageVariableOf(v.info.Uses[x.Sel], ""); variable != nil && !first {
					return variable, inMemory
				}
				return nil, false
			}
			through(x.X)
			e = x.X
		case *ast.IndexExpr:
			through(x.X)
			e = x.X
		case *ast.StarExpr:
			inMemory = true
			e = x.X
		default:
			return nil, false
		}
	}
}

// checkDeclaredRequires reports each top-level conjunct of a Requires
// clause that reads package-level variables and nothing else, unless what
// their declarations give shows it. No caller can choose the value of such
// a variable, and a caller in another package may not even be able to
// name it, so such a clause would be a claim about the initialiser that
// nothing checks.
func (v *fnVerifier) checkDeclaredRequires(st *state) {
	for _, c := range v.fn.requires {
		if c.node == nil {
			continue
		}
		for _, conjunct := range c.node.Conjuncts() {
			scratch := st.clone()
			env := &specEnv{v: v, sink: scratch, fn: v.fn, args: v.entry, now: memory{}}
			t := v.formula(c, conjunct, env)
			onlyVariables, named := true, false
			seen := map[*logic.Term]bool{}
			var walk func(t *logic.Term)
			walk = func(t *logic.Term) {
				if seen[t] {
					return
				}
				seen[t] = true
				switch {
				case isFixedTerm(t):
					named = true
				case t.Op == logic.OpConst && t != logic.NilErr() && !strings.HasPrefix(t.Name, "float "):
					onlyVariables = false
				}
				for _, arg := range t.Args {
					walk(arg)
				}
			}
			walk(t)
			if !onlyVariables || !named || v.proves(v.knownFacts(), t, 0) {
				continue
			}
			v.report(c.pos, "the Requires clause %s reads only package-level variables, and their declarations do not show that it holds; "+
				"test the value in the body instead", conjunct)
		}
	}
}

// refuseWriteThrough stops the verification of a function that assigns a
// part of a package-level variable, or memory one refers to.
func (v *fnVerifier) refuseWriteThrough(e ast.Expr) {
	v.refuseWriteThroughAs(e, types.ExprString(e))
}

// refuseWriteThroughAs is refuseWriteThrough for a write that text spells.
func (v *fnVerifier) refuseWriteThroughAs(e ast.Expr, text string) {
	switch root, inMemory := v.packageRoot(e); {
	case root != nil && inMemory:
		v.unsupported(e.Pos(), fmt.Sprintf("%s writes memory that the package-level variable %s refers to, which a Modifies clause cannot name yet",
			text, v.spelling(root)))
	case root != nil:
		v.unsupported(e.Pos(), fmt.Sprintf("%s is part of the package-level variable %s, which a verified function cannot assign yet", text, v.spelling(root)))
	}
}

// embedded returns the declarations of variables that a go:embed
// directive gives their values. A directive belongs to the first
// declaration of a variable after it, as the compiler reads it: blank lines
// and other comments may stand between them, so the doc comment of the
// declaration is not where to look.
func (pv *pkgVerifier) embedded() map[*ast.ValueSpec]bool {
	embeds := map[*ast.ValueSpec]bool{}
	for _, file := range pv.pass.Files {
		var specs []*ast.ValueSpec
		for _, decl := range file.Decls {
			if gen, ok := decl.(*ast.GenDecl); ok && gen.Tok == token.VAR {
				for _, spec := range gen.Specs {
					specs = append(specs, spec.(*ast.ValueSpec))
				}
			}
		}
		for _, group := range file.Comments {
			for _, c := range group.List {
				if !strings.HasPrefix(c.Text, "//go:embed") {
					continue
				}
				if i := slices.IndexFunc(specs, func(spec *ast.ValueSpec) bool { return spec.Pos() > c.Pos() }); i >= 0 {
					embeds[specs[i]] = true
				}
			}
		}
	}
	return embeds
}

// fixedMet is a fixed variable that a function read: its leaves and its
// type, for the samples of the check of a contract that may always fail.
type fixedMet struct {
	val value
	typ types.Type
}

// modifiesVariable returns the package-level variable that the path of a
// Modifies entry starts from, as the function's file spells it, or nil.
func (v *fnVerifier) modifiesVariable(fn *funcInfo, m *modTarget) *types.Var {
	spelled := fn.spelling()
	var obj types.Object
	switch {
	case spelled.decl != nil && spelled.obj.Pkg() == v.pass.Pkg:
		if scope := v.pass.Pkg.Scope().Innermost(spelled.decl.Pos()); scope != nil {
			_, obj = scope.LookupParent(m.name, spelled.decl.Pos())
		}
	case spelled.obj != nil && spelled.obj.Pkg() != nil:
		obj = spelled.obj.Pkg().Scope().Lookup(m.name)
	}
	field := ""
	if len(m.steps) > 0 {
		field = m.steps[0].field
	}
	if variable := packageVariableOf(obj, ""); variable != nil {
		return variable
	}
	if _, isPackage := obj.(*types.PkgName); isPackage {
		return packageVariableOf(obj, field)
	}
	return nil
}
