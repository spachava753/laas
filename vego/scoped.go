package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"slices"
	"strings"
	"sync"

	"gopkg.in/yaml.v3"
)

// Two declarations of the shipped files say how verified code may use a
// type of the standard library beyond what the entries of its functions
// say (F28):
//
//   - scoped: a value of an interface type that must not be used after the
//     call that received it returns, as an http.ResponseWriter after
//     ServeHTTP. Verified code never keeps one: ownorigins.go marks every
//     value that is one, holds one, or was converted from one, and refuses
//     to store it into memory, capture it in a literal that may outlive the
//     call, hand it to a parameter that is kept, or return it.
//   - hidden: fields of a struct that code that is not verified writes
//     behind calls whose entries do not list them, as the server writes
//     Request.Trailer when a write to the response drains the body.
//     Verified code cannot name such a field, in code or in a formula, and
//     the separation of part 1 does not count it, or what it refers to, as
//     reached by a value that holds it.
//
// Both are matched by the underlying type, as owns and states are, so a
// type defined from a declared one, or identical to it, is covered.

// scopedDecl is a scoped declaration.
type scopedDecl struct {
	pkg, typ string
	reason   string
	line     int
}

// hiddenDecl is a hidden declaration: the fields of a struct type.
type hiddenDecl struct {
	pkg, typ string
	fields   []string
	reason   string
	line     int
}

// addScoped reads the scoped section of a shipped file: a mapping from an
// interface type to a reason.
func (f *trustFile) addScoped(node *yaml.Node) {
	if !f.shipped {
		f.problem(node.Line, "scoped can be declared only in the shipped files")
		return
	}
	if node.Kind != yaml.MappingNode {
		f.problem(node.Line, "scoped must map types to a reason")
		return
	}
	for i := 0; i+1 < len(node.Content); i += 2 {
		typeName, body := node.Content[i], node.Content[i+1]
		pkg, typ, ok := splitTypeName(typeName.Value)
		if !ok || body.Kind != yaml.MappingNode {
			f.problem(typeName.Line, "scoped: %q must be a type named by its package, mapped to a reason", typeName.Value)
			continue
		}
		decl := scopedDecl{pkg: pkg, typ: typ, line: typeName.Line}
		for k := 0; k+1 < len(body.Content); k += 2 {
			switch field, value := body.Content[k], body.Content[k+1]; field.Value {
			case "reason":
				decl.reason = strings.TrimSpace(value.Value)
			default:
				f.problem(field.Line, "unknown field %q in scoped of %s; expected reason", field.Value, typeName.Value)
			}
		}
		if decl.reason == "" {
			f.problem(typeName.Line, "scoped of %s needs a reason", typeName.Value)
			continue
		}
		f.scoped[stateKey(pkg, typ)] = decl
	}
}

// addFields reads a section of a shipped file that maps struct types to
// fields and a reason: hidden, or notWrittenBy.
func (f *trustFile) addFields(section string, into map[string]hiddenDecl, node *yaml.Node) {
	if !f.shipped {
		f.problem(node.Line, "%s can be declared only in the shipped files", section)
		return
	}
	if node.Kind != yaml.MappingNode {
		f.problem(node.Line, "%s must map types to their fields and a reason", section)
		return
	}
	for i := 0; i+1 < len(node.Content); i += 2 {
		typeName, body := node.Content[i], node.Content[i+1]
		pkg, typ, ok := splitTypeName(typeName.Value)
		if !ok || body.Kind != yaml.MappingNode {
			f.problem(typeName.Line, "%s: %q must be a type named by its package, mapped to its fields and a reason", section, typeName.Value)
			continue
		}
		decl := hiddenDecl{pkg: pkg, typ: typ, line: typeName.Line}
		for k := 0; k+1 < len(body.Content); k += 2 {
			switch field, value := body.Content[k], body.Content[k+1]; field.Value {
			case "fields":
				for _, name := range value.Content {
					decl.fields = append(decl.fields, name.Value)
				}
			case "reason":
				decl.reason = strings.TrimSpace(value.Value)
			default:
				f.problem(field.Line, "unknown field %q in %s of %s; expected fields and reason", field.Value, section, typeName.Value)
			}
		}
		if len(decl.fields) == 0 || decl.reason == "" {
			f.problem(typeName.Line, "%s of %s needs its fields and a reason", section, typeName.Value)
			continue
		}
		into[stateKey(pkg, typ)] = decl
	}
}

// packageOf finds the package with a path among what pkg imports, at any
// depth, or nil.
func packageOf(pkg *types.Package, path string) *types.Package {
	seen := map[*types.Package]bool{}
	var walk func(p *types.Package) *types.Package
	walk = func(p *types.Package) *types.Package {
		if p == nil || seen[p] {
			return nil
		}
		seen[p] = true
		if p.Path() == path {
			return p
		}
		for _, imported := range p.Imports() {
			if found := walk(imported); found != nil {
				return found
			}
		}
		return nil
	}
	return walk(pkg)
}

// scopedCache remembers, per type, the declaration scopedOf found.
var scopedCache sync.Map

// scopedOf returns the scoped declaration of an interface type: one whose
// underlying interface is that of a declared type, or that has every
// method of a declared type as the same declaration, as an interface that
// embeds it does. A declared type is found among the packages its methods
// and their signatures mention, since an identical interface names the
// same types.
func scopedOf(t types.Type) *scopedDecl {
	if t == nil {
		return nil
	}
	u, isIface := types.Unalias(t).Underlying().(*types.Interface)
	if !isIface || u.NumMethods() == 0 {
		return nil
	}
	if found, ok := scopedCache.Load(t); ok {
		return found.(*scopedDecl)
	}
	var result *scopedDecl
	for _, file := range shippedContracts() {
		for _, decl := range file.scoped {
			for method := range u.Methods() {
				home := packageOf(method.Pkg(), decl.pkg)
				if home == nil {
					sig := method.Type().(*types.Signature)
					for _, tuple := range []*types.Tuple{sig.Params(), sig.Results()} {
						for v := range tuple.Variables() {
							if named, ok := types.Unalias(v.Type()).(*types.Named); ok && home == nil {
								home = packageOf(named.Obj().Pkg(), decl.pkg)
							}
						}
					}
				}
				if home == nil {
					continue
				}
				if obj, ok := home.Scope().Lookup(decl.typ).(*types.TypeName); ok && (types.Identical(u, obj.Type().Underlying()) || embeds(u, obj.Type())) {
					d := decl
					result = &d
				}
				break
			}
		}
	}
	scopedCache.Store(t, result)
	return result
}

// embeds reports whether an interface has every method of a declared one
// as the same declaration, as through embedding at any depth: a value of it
// is a value of the declared type too (F8 of the review of step 1).
func embeds(u *types.Interface, declared types.Type) bool {
	want, ok := declared.Underlying().(*types.Interface)
	if !ok || want.NumMethods() == 0 {
		return false
	}
	for method := range want.Methods() {
		if !slices.Contains(slices.Collect(u.Methods()), method) {
			return false
		}
	}
	return true
}

// holdsScoped returns the scoped declaration of a value that a value of
// type t is or holds, through fields, elements, map keys and values, and
// what pointers point to; it stops at interfaces other than a scoped one
// and at function values, which may hold one only as verified code
// converted or captured it, which the kinds of ownorigins.go follow.
func holdsScoped(t types.Type) *scopedDecl {
	seen := map[types.Type]bool{}
	var walk func(t types.Type) *scopedDecl
	walk = func(t types.Type) *scopedDecl {
		if t == nil || seen[t] {
			return nil
		}
		seen[t] = true
		if d := scopedOf(t); d != nil {
			return d
		}
		switch u := types.Unalias(t).Underlying().(type) {
		case *types.Pointer:
			return walk(u.Elem())
		case *types.Slice:
			return walk(u.Elem())
		case *types.Array:
			return walk(u.Elem())
		case *types.Map:
			if d := walk(u.Key()); d != nil {
				return d
			}
			return walk(u.Elem())
		case *types.Struct:
			for field := range u.Fields() {
				if d := walk(field.Type()); d != nil {
					return d
				}
			}
		}
		return nil
	}
	return walk(t)
}

// hiddenOf returns the hidden declaration of a struct type that covers its
// field at index, or nil. It is matched as ownsDeclared matches owns.
func hiddenOf(t types.Type, index int) *hiddenDecl {
	return fieldDeclOf(t, index, func(f *trustFile) map[string]hiddenDecl { return f.hidden })
}

// notWrittenOf returns the notWrittenBy declaration of a struct type that
// covers its field at index, or nil: verified code reads the field and does
// not store into it, and what the value in it holds writes nothing else of
// what the struct reaches without going through an interface value but its
// hidden fields.
func progressOf(t types.Type, index int) *hiddenDecl {
	return fieldDeclOf(t, index, func(f *trustFile) map[string]hiddenDecl { return f.progresses })
}

// notWrittenOf finds the notWrittenBy declaration of a field of a struct
// type, or nil.
func notWrittenOf(t types.Type, index int) *hiddenDecl {
	return fieldDeclOf(t, index, func(f *trustFile) map[string]hiddenDecl { return f.notWritten })
}

// fieldDeclOf finds a declaration of a field of a struct type in a section
// of the shipped files.
func fieldDeclOf(t types.Type, index int, section func(*trustFile) map[string]hiddenDecl) *hiddenDecl {
	u, isStruct := types.Unalias(t).Underlying().(*types.Struct)
	if !isStruct || index < 0 || index >= u.NumFields() {
		return nil
	}
	var home *types.Package
	for field := range u.Fields() {
		if field.Pkg() != nil {
			home = field.Pkg()
			break
		}
	}
	if home == nil {
		return nil
	}
	plain := untagged(u)
	for _, file := range shippedContracts() {
		for _, decl := range section(file) {
			if decl.pkg != home.Path() || !slices.Contains(decl.fields, u.Field(index).Name()) {
				continue
			}
			obj, ok := home.Scope().Lookup(decl.typ).(*types.TypeName)
			if ok && types.Identical(plain, untagged(obj.Type().Underlying())) {
				d := decl
				return &d
			}
		}
	}
	return nil
}

// hiddenReason says why a hidden field cannot be named, for a message.
func hiddenReason(d *hiddenDecl, field string) string {
	return fmt.Sprintf("%s of %s.%s cannot be read or written by verified code: code that is not verified writes it behind calls whose entries do not list it, "+
		"as the hidden declaration of %s.%s in the shipped files says", field, d.pkg, d.typ, d.pkg, d.typ)
}

// checkHidden refuses every selector of a body that reaches a hidden field,
// read, assigned, or with its address taken, promoted ones included, and
// every key of a composite literal that names one.
func (v *fnVerifier) checkHidden(body ast.Node) {
	if body == nil {
		return
	}
	ast.Inspect(body, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.SelectorExpr:
			selection := v.info.Selections[n]
			if selection == nil || selection.Kind() != types.FieldVal {
				return true
			}
			t := selection.Recv()
			for _, index := range selection.Index() {
				object := t
				if target, ok := pointee(t); ok {
					object = target
				}
				u, isStruct := object.Underlying().(*types.Struct)
				if !isStruct {
					break
				}
				if d := hiddenOf(object, index); d != nil {
					v.unsupported(n.Sel.Pos(), hiddenReason(d, u.Field(index).Name()))
				}
				t = u.Field(index).Type()
			}
		case *ast.CompositeLit:
			t := v.info.TypeOf(n)
			if t == nil {
				return true
			}
			u, isStruct := t.Underlying().(*types.Struct)
			if !isStruct {
				return true
			}
			for i, element := range n.Elts {
				index := i
				if pair, keyed := element.(*ast.KeyValueExpr); keyed {
					if id, ok := pair.Key.(*ast.Ident); ok {
						index = slices.IndexFunc(slices.Collect(u.Fields()), func(f *types.Var) bool { return f.Name() == id.Name })
					}
				}
				if d := hiddenOf(t, index); d != nil {
					v.unsupported(element.Pos(), hiddenReason(d, u.Field(index).Name()))
				}
			}
		}
		return true
	})
}

// hiddenOffsets returns the byte offsets, in a struct type, of the hidden
// fields it holds at any depth through fields held by value.
func (pv *pkgVerifier) hiddenOffsets(t types.Type) []int64 {
	var offsets []int64
	var walk func(t types.Type, base int64)
	walk = func(t types.Type, base int64) {
		st, ok := t.Underlying().(*types.Struct)
		if !ok {
			return
		}
		fields := slices.Collect(st.Fields())
		for i, offset := range pv.pass.TypesSizes.Offsetsof(fields) {
			if hiddenOf(t, i) != nil {
				offsets = append(offsets, base+offset)
				continue
			}
			walk(fields[i].Type(), base+offset)
		}
	}
	walk(t, 0)
	return offsets
}

// newAtStore reports whether an expression is new memory converted where it
// is stored: the address of a composite literal, or a composite literal,
// possibly converted explicitly, whose footprint as an interface value is
// what it makes.
func (v *fnVerifier) newAtStore(e ast.Expr) bool {
	e = ast.Unparen(e)
	if call, ok := e.(*ast.CallExpr); ok && len(call.Args) == 1 {
		if tv := v.info.Types[call.Fun]; tv.IsType() {
			e = ast.Unparen(call.Args[0])
		}
	}
	if u, ok := e.(*ast.UnaryExpr); ok && u.Op == token.AND {
		_, isLit := ast.Unparen(u.X).(*ast.CompositeLit)
		return isLit
	}
	_, isLit := e.(*ast.CompositeLit)
	return isLit
}

// holdsNotWritten returns the declaration of a struct held by value in a
// value of type t, at any depth through fields and arrays, that has a field
// a notWrittenBy declaration covers, or nil.
func holdsNotWritten(t types.Type) *hiddenDecl {
	seen := map[types.Type]bool{}
	var walk func(t types.Type) *hiddenDecl
	walk = func(t types.Type) *hiddenDecl {
		if t == nil || seen[t] {
			return nil
		}
		seen[t] = true
		switch u := types.Unalias(t).Underlying().(type) {
		case *types.Array:
			return walk(u.Elem())
		case *types.Struct:
			for i := range u.NumFields() {
				if d := notWrittenOf(t, i); d != nil {
					return d
				}
				if d := walk(u.Field(i).Type()); d != nil {
					return d
				}
			}
		}
		return nil
	}
	return walk(t)
}

// notWrittenReason says why verified code may not store into a field that
// a notWrittenBy declaration covers, or a whole struct that has one into
// memory, for a message.
func notWrittenReason(d *hiddenDecl) string {
	return fmt.Sprintf("what the field %s of a %s.%s holds writes nothing else the %s reaches, as the notWrittenBy declaration of %s.%s in the shipped files says "+
		"of values from code that is not verified, and verified code does not store into it",
		d.fields[0], d.pkg, d.typ, d.typ, d.pkg, d.typ)
}

// checkNotWritten refuses, in a body, a store into a field that a
// notWrittenBy declaration covers, unless what is stored is new memory
// converted where it is stored, whose footprint is what it makes; a
// composite literal that sets such a field the same way; and a store of a
// whole struct that has one into memory, as *resp = r2, which a copy into a
// local is not (F28).
func (v *fnVerifier) checkNotWritten(body ast.Node) {
	if body == nil {
		return
	}
	fieldOf := func(sel *ast.SelectorExpr, decl func(types.Type, int) *hiddenDecl) *hiddenDecl {
		selection := v.info.Selections[sel]
		if selection == nil || selection.Kind() != types.FieldVal {
			return nil
		}
		t := selection.Recv()
		index := selection.Index()
		for _, i := range index[:len(index)-1] {
			object := t
			if target, ok := pointee(t); ok {
				object = target
			}
			t = object.Underlying().(*types.Struct).Field(i).Type()
		}
		object := t
		if target, ok := pointee(t); ok {
			object = target
		}
		return decl(object, index[len(index)-1])
	}
	field := func(sel *ast.SelectorExpr) *hiddenDecl { return fieldOf(sel, notWrittenOf) }
	local := func(e ast.Expr) bool {
		id, ok := ast.Unparen(e).(*ast.Ident)
		if !ok {
			return false
		}
		if id.Name == "_" {
			return true
		}
		// A local variable is memory the function made, also when its
		// address is taken, which no footprint holds.
		variable, ok := v.info.ObjectOf(id).(*types.Var)
		return ok && variable.Parent() != v.pass.Pkg.Scope()
	}
	ast.Inspect(body, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.AssignStmt:
			for i, lhs := range n.Lhs {
				var rhs ast.Expr
				if len(n.Rhs) == len(n.Lhs) {
					rhs = n.Rhs[i]
				}
				if sel, ok := ast.Unparen(lhs).(*ast.SelectorExpr); ok {
					if d := fieldOf(sel, progressOf); d != nil {
						v.unsupported(lhs.Pos(), fmt.Sprintf("%s is stored into, and the progresses declaration of %s.%s in the shipped files says that what it holds is "+
							"a reader that the server made, whose Read makes progress; keep the request's own body", types.ExprString(lhs), d.pkg, d.typ))
					}
					if d := field(sel); d != nil && (rhs == nil || !v.newAtStore(rhs)) {
						v.unsupported(lhs.Pos(), fmt.Sprintf("%s is stored into, and %s; store a value made here, as in %s = &myBody{...}, whose methods write only what it makes",
							types.ExprString(lhs), notWrittenReason(d), types.ExprString(lhs)))
					}
				}
				if d := holdsNotWritten(v.info.TypeOf(lhs)); d != nil && !local(lhs) {
					v.unsupported(lhs.Pos(), fmt.Sprintf("a %s.%s is stored into memory at %s, and %s; copy it into a local variable instead",
						d.pkg, d.typ, types.ExprString(lhs), notWrittenReason(d)))
				}
			}
		case *ast.CallExpr:
			if isBuiltin(v.info, n, "append") && len(n.Args) > 1 {
				if d := holdsNotWritten(elemType(v.info.TypeOf(n.Args[0]))); d != nil {
					v.unsupported(n.Pos(), fmt.Sprintf("a %s.%s is appended to %s, which may store it into memory that exists, and %s; keep the values in a slice made here",
						d.pkg, d.typ, types.ExprString(n.Args[0]), notWrittenReason(d)))
				}
			}
		case *ast.CompositeLit:
			t := v.info.TypeOf(n)
			if t == nil {
				return true
			}
			u, isStruct := t.Underlying().(*types.Struct)
			if !isStruct {
				return true
			}
			for i, element := range n.Elts {
				index, value := i, element
				if pair, keyed := element.(*ast.KeyValueExpr); keyed {
					value = pair.Value
					if id, ok := pair.Key.(*ast.Ident); ok {
						index = slices.IndexFunc(slices.Collect(u.Fields()), func(f *types.Var) bool { return f.Name() == id.Name })
					}
				}
				if d := progressOf(t, index); d != nil && !v.isNil(value) {
					v.unsupported(element.Pos(), fmt.Sprintf("the field %s of the %s.%s made at %s is set, and the progresses declaration of %s.%s in the shipped files says "+
						"that what it holds is a reader that the server made, whose Read makes progress; a request verified code makes has no body",
						u.Field(index).Name(), d.pkg, d.typ, v.placeOf(n.Pos()), d.pkg, d.typ))
				}
				if d := notWrittenOf(t, index); d != nil && !v.newAtStore(value) && !v.isNil(value) {
					v.unsupported(element.Pos(), fmt.Sprintf("the field %s of the %s.%s made at %s is set, and %s; set it to a value made here, as &myBody{...}, whose methods write only what it makes",
						u.Field(index).Name(), d.pkg, d.typ, v.placeOf(n.Pos()), notWrittenReason(d)))
				}
			}
		}
		return true
	})
}
