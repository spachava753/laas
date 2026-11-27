package vego

import (
	"fmt"
	"go/types"
	"slices"
	"strings"
)

// canonSig writes a signature so that two identical signatures are written
// the same: aliases are removed, basic types are written by kind, named
// types by package path, name, and type arguments, and a type parameter
// anywhere makes it "*", which meets every signature.
func canonSig(sig *types.Signature) string {
	var b strings.Builder
	wild := false
	var write func(t types.Type, seen map[types.Type]bool)
	tuple := func(tu *types.Tuple, seen map[types.Type]bool) {
		b.WriteString("(")
		for i := range tu.Len() {
			if i > 0 {
				b.WriteString(",")
			}
			write(tu.At(i).Type(), seen)
		}
		b.WriteString(")")
	}
	write = func(t types.Type, seen map[types.Type]bool) {
		t = types.Unalias(t)
		switch u := t.(type) {
		case *types.TypeParam:
			wild = true
		case *types.Basic:
			fmt.Fprintf(&b, "b%d", u.Kind())
		case *types.Named:
			path := ""
			if u.Obj().Pkg() != nil {
				path = u.Obj().Pkg().Path()
			}
			fmt.Fprintf(&b, "%s.%s", path, u.Obj().Name())
			if u.TypeParams().Len() > 0 && u.TypeArgs().Len() == 0 {
				wild = true
			}
			if u.TypeArgs().Len() > 0 {
				b.WriteString("[")
				for i := range u.TypeArgs().Len() {
					if i > 0 {
						b.WriteString(",")
					}
					write(u.TypeArgs().At(i), seen)
				}
				b.WriteString("]")
			}
		case *types.Pointer:
			b.WriteString("*")
			write(u.Elem(), seen)
		case *types.Slice:
			b.WriteString("[]")
			write(u.Elem(), seen)
		case *types.Array:
			fmt.Fprintf(&b, "[%d]", u.Len())
			write(u.Elem(), seen)
		case *types.Map:
			b.WriteString("map[")
			write(u.Key(), seen)
			b.WriteString("]")
			write(u.Elem(), seen)
		case *types.Chan:
			fmt.Fprintf(&b, "chan%d ", u.Dir())
			write(u.Elem(), seen)
		case *types.Signature:
			b.WriteString("func")
			if u.TypeParams().Len() > 0 {
				wild = true
			}
			tuple(u.Params(), seen)
			tuple(u.Results(), seen)
			if u.Variadic() {
				b.WriteString("...")
			}
		case *types.Struct:
			b.WriteString("struct{")
			for i := range u.NumFields() {
				f := u.Field(i)
				pkg := ""
				if !f.Exported() && f.Pkg() != nil {
					pkg = f.Pkg().Path() + "."
				}
				fmt.Fprintf(&b, "%s%s %t ", pkg, f.Name(), f.Embedded())
				write(f.Type(), seen)
				fmt.Fprintf(&b, " %q;", u.Tag(i))
			}
			b.WriteString("}")
		case *types.Interface:
			if !u.IsMethodSet() {
				// A constraint: identity of type sets is not written.
				wild = true
				return
			}
			b.WriteString("interface{")
			var ms []string
			for m := range u.Methods() {
				ms = append(ms, m.Id())
			}
			slices.Sort(ms)
			for _, id := range ms {
				for m := range u.Methods() {
					if m.Id() == id {
						b.WriteString(id)
						write(m.Type(), seen)
						b.WriteString(";")
					}
				}
			}
			b.WriteString("}")
		default:
			wild = true
		}
	}
	write(withoutRecv(sig), map[types.Type]bool{})
	if wild {
		return "*"
	}
	return b.String()
}
