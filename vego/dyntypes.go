package vego

import (
	"fmt"
	"go/ast"
	"go/constant"
	"go/token"
	"go/types"
	"math/big"
	"slices"
	"strconv"
	"strings"
	"unicode/utf8"

	"github.com/spachava753/laas/vego/internal/logic"
)

// Dynamic types (F33, see Dynamic types and typed errors in ROADMAP.md).
//
// An error is a Go error value, up to Go's == where == is identity of what
// it holds: two errors are equal in the logic when they are the same error,
// and for a dynamic type on which == is identity (identityEq) two errors
// that hold equal values of it are the same error. For any other dynamic
// type an error stands for one conversion, which its copies share.
//
// What an error holds is read at its reference, ErrRef(e), from tables
// that nothing writes, as the home of an interface value is read:
//
//   - dyntype at the reference is the tag of the dynamic type, a number
//     made from a name that two types share exactly when types.Identical
//     holds of them (canonicalName);
//   - "held T.path" at the reference is one leaf of the value of type T
//     that the error holds, meaningful when the tag is T's.
//
// Invariants (TI and HV of the roadmap): the tag of a non-nil error is the
// tag of its dynamic type, or unknown; no fact gives a known tag but at a
// conversion. The held value of an error read under its tag is the value
// converted, which never changes, since Go copies it into the interface.
// The leaves of a pointer are read as Go has them: a nil pointer has
// position zero, whatever position the logic gave it (goLeaves).

// dynTypes is the table of the tags of dynamic types, read at a reference.
var dynTypes = logic.Const("dyntype", logic.IntSeq)

// isDynTable reports whether a term is one of the tables of what errors
// hold: dyntype, a held table, or a table of canonical errors, or the table
// of the keys of the states of pointers inside an allocation. They are
// one function for the whole program, never written, which the facts of
// conversions constrain, so the always-fails check takes them as part of
// every input, as it takes a fixed variable.
func isDynTable(t *logic.Term) bool {
	return t.Op == logic.OpConst && (t == dynTypes || t.Name == dynTypes.Name || strings.HasPrefix(t.Name, "held ") || strings.HasPrefix(t.Name, "mkerr ") || strings.HasPrefix(t.Name, "implements ") || t.Name == eqPanics.Name ||
		t.Name == pkeys.Name)
}

// dynTag returns the tag of the dynamic type of what is read at a
// reference.
func dynTag(ref *logic.Term) *logic.Term {
	return logic.Select(dynTypes, ref)
}

// errorTag returns the tag of the dynamic type of an error.
func errorTag(err *logic.Term) *logic.Term {
	return dynTag(logic.ErrRef(err))
}

// canonicalName returns a name of a type that two types share exactly when
// types.Identical holds of them, and false for a type that has no such
// name here: one declared inside a function, one that holds such a type, a
// type parameter, and an untyped type. A defined type is named by the path
// of its package and its name, with its type arguments; an alias is the
// type it stands for; byte is uint8 and rune int32; the rest is written
// out, with the package of each unexported field or method name and the
// tag of each field, which types.Identical compares. Paths and tags are
// quoted, so no two types share a name.
func canonicalName(t types.Type) (string, bool) {
	var b strings.Builder
	ok := writeCanonical(&b, t, map[types.Type]bool{})
	return b.String(), ok
}

// writeCanonical writes the canonical name of a type to b and reports
// whether it has one. Each kind of type is written by a case of its own:
// a defined type by its package and name, with type arguments; a basic
// type by the name of its kind; pointers, slices, arrays, maps, channels,
// and signatures from their parts; a struct by its fields, each with its
// name qualified by its package when unexported, its type, and its tag;
// and an interface by its methods sorted by their unique names. A type
// declared inside a function, a generic type without arguments, an
// untyped or invalid type, and a constraint have no name.
func writeCanonical(b *strings.Builder, t types.Type, seen map[types.Type]bool) bool {
	t = types.Unalias(t)
	qualified := func(pkg *types.Package, name string, exported bool) {
		if !exported && pkg != nil {
			b.WriteString(strconv.Quote(pkg.Path()))
			b.WriteByte('.')
		}
		b.WriteString(name)
	}
	tuple := func(vars *types.Tuple, variadic bool) bool {
		b.WriteByte('(')
		for i := range vars.Len() {
			if i > 0 {
				b.WriteByte(',')
			}
			if variadic && i == vars.Len()-1 {
				b.WriteString("...")
			}
			if !writeCanonical(b, vars.At(i).Type(), seen) {
				return false
			}
		}
		b.WriteByte(')')
		return true
	}
	switch t := t.(type) {
	case *types.Named:
		obj := t.Obj()
		if obj.Pkg() == nil {
			// error and comparable.
			b.WriteString(obj.Name())
			return true
		}
		if obj.Pkg().Scope().Lookup(obj.Name()) != obj {
			// Declared inside a function: two such declarations may have
			// one name.
			return false
		}
		b.WriteString(strconv.Quote(obj.Pkg().Path()))
		b.WriteByte('.')
		b.WriteString(obj.Name())
		if args := t.TypeArgs(); args != nil {
			b.WriteByte('[')
			for i := range args.Len() {
				if i > 0 {
					b.WriteByte(',')
				}
				if !writeCanonical(b, args.At(i), seen) {
					return false
				}
			}
			b.WriteByte(']')
		} else if t.TypeParams() != nil {
			return false
		}
		return true
	case *types.Basic:
		if t.Info()&types.IsUntyped != 0 || t.Kind() == types.Invalid {
			return false
		}
		// The name of the kind, so that byte is uint8.
		b.WriteString(types.Typ[t.Kind()].Name())
		return true
	case *types.Pointer:
		b.WriteByte('*')
		return writeCanonical(b, t.Elem(), seen)
	case *types.Slice:
		b.WriteString("[]")
		return writeCanonical(b, t.Elem(), seen)
	case *types.Array:
		fmt.Fprintf(b, "[%d]", t.Len())
		return writeCanonical(b, t.Elem(), seen)
	case *types.Map:
		b.WriteString("map[")
		if !writeCanonical(b, t.Key(), seen) {
			return false
		}
		b.WriteByte(']')
		return writeCanonical(b, t.Elem(), seen)
	case *types.Chan:
		fmt.Fprintf(b, "chan%d ", t.Dir())
		return writeCanonical(b, t.Elem(), seen)
	case *types.Signature:
		if t.TypeParams() != nil || t.RecvTypeParams() != nil {
			return false
		}
		b.WriteString("func")
		if !tuple(t.Params(), t.Variadic()) {
			return false
		}
		return tuple(t.Results(), false)
	case *types.Struct:
		b.WriteString("struct{")
		for i := range t.NumFields() {
			field := t.Field(i)
			if field.Embedded() {
				b.WriteByte('!')
			}
			qualified(field.Pkg(), field.Name(), field.Exported())
			b.WriteByte(' ')
			if !writeCanonical(b, field.Type(), seen) {
				return false
			}
			b.WriteByte(' ')
			b.WriteString(strconv.Quote(t.Tag(i)))
			b.WriteByte(';')
		}
		b.WriteByte('}')
		return true
	case *types.Interface:
		if !t.IsMethodSet() {
			return false
		}
		// The methods of an interface, embedded ones included, sorted by
		// their unique names.
		methods := make([]*types.Func, t.NumMethods())
		for i := range methods {
			methods[i] = t.Method(i)
		}
		slices.SortFunc(methods, func(a, b *types.Func) int { return strings.Compare(a.Id(), b.Id()) })
		b.WriteString("interface{")
		for _, method := range methods {
			qualified(method.Pkg(), method.Name(), method.Exported())
			sig := method.Type().(*types.Signature)
			if !tuple(sig.Params(), sig.Variadic()) || !tuple(sig.Results(), false) {
				return false
			}
			b.WriteByte(';')
		}
		b.WriteByte('}')
		return true
	}
	return false
}

// typeTag returns the tag of a dynamic type: the number whose digits in
// base 256 are the bytes of its canonical name, which holds no zero byte,
// so that two names give two numbers. It is not zero, which no dynamic
// type has: zero is the tag nil has in the intended model.
func typeTag(t types.Type) (*logic.Term, bool) {
	name, ok := canonicalName(t)
	if !ok {
		return nil, false
	}
	return logic.BigLit(new(big.Int).SetBytes([]byte(name))), true
}

// The types of the errors errors.New and fmt.Errorf return, as their
// packages declare them: what TestErrorsAsModelled checks of the running
// toolchain, and what noteMadeTag states of a made error.
var madeErrorTypes = []string{`*"errors".errorString`, `*"fmt".wrapError`, `*"fmt".wrapErrors`}

// heldTable returns the table of one leaf of the values of a dynamic type,
// read at a reference.
func heldTable(name string, index int, lf leaf) *logic.Term {
	return logic.Const(fmt.Sprintf("held %s %d%s", name, index, lf.path), logic.SeqOf(lf.sort))
}

// goLeaves returns the leaves of a value as Go has them: the position of
// a nil pointer is zero, so that two nil pointers of one type are one
// value, as Go's == says (F2 of the design review). The allocation of a
// pointer is read twice there, so one that is not a name or a number is
// named first, which keeps a chain of conversions from doubling.
func (v *fnVerifier) goLeaves(st *state, layout []leaf, val value) value {
	out := slices.Clone(val)
	for i, lf := range layout {
		if lf.part == partAt && i > 0 && layout[i-1].part == partPtr {
			ptr := out[i-1]
			if ptr.Op != logic.OpConst && ptr.Op != logic.OpIntLit {
				named := v.fresh("pointer", logic.Ref)
				st.assume(logic.Eq(named, ptr))
				ptr = named
				out[i-1] = named
			}
			out[i] = logic.Ite(logic.Eq(ptr, logic.RefLit(0)), logic.IntLit(0), val[i])
		}
	}
	return out
}

// identityEq reports whether Go's == on two values of a type cannot panic
// and holds exactly when the values are the same: integers, strings,
// booleans, pointers to values that do not have size zero, and arrays and
// structs of these. Floats are left out (NaN differs from itself, 0 equals
// -0), and so are pointers to values of size zero, which Go may or may not
// give one address (F1 of the design review). Interfaces, slices, maps,
// and functions are not comparable or may panic. It is the one rule for
// where a comparison of errors in code is equality in the logic: an opaque
// error variable is comparable by it, and so is an error a conversion made.
func (pv *pkgVerifier) identityEq(t types.Type) bool {
	return identityEqIn(pv.pass.TypesSizes, t, map[types.Type]bool{})
}

func identityEqIn(sizes types.Sizes, t types.Type, seen map[types.Type]bool) bool {
	if seen[t] {
		return true
	}
	seen[t] = true
	switch u := t.Underlying().(type) {
	case *types.Basic:
		return u.Info()&(types.IsInteger|types.IsString|types.IsBoolean) != 0 && u.Info()&types.IsUntyped == 0
	case *types.Pointer:
		return sizes.Sizeof(u.Elem()) != 0
	case *types.Array:
		return identityEqIn(sizes, u.Elem(), seen)
	case *types.Struct:
		for field := range u.Fields() {
			if !identityEqIn(sizes, field.Type(), seen) {
				return false
			}
		}
		return true
	}
	return false
}

// capturesValue reports whether the leaves of a layout are the whole value
// as == compares it: no field is hidden, and no state is part of it.
func capturesValue(layout []leaf) bool {
	return !slices.ContainsFunc(layout, func(lf leaf) bool { return lf.part == partHidden || lf.part == partState })
}

// typedError returns the error that converting a value of a concrete type
// gives, and states what it holds; see canonicalError and noteHeld.
func (v *fnVerifier) typedError(e ast.Expr, from types.Type, val value, st *state, guard []*logic.Term) *logic.Term {
	layout, _ := layoutOf(from)
	if _, ok := layoutOf(from); ok && holdsArrayValue(from) {
		v.unsupported(e.Pos(), rConvToError, fmt.Sprintf("converting %s %s to an error is not supported: %s", article(v.shown(from)), v.shown(from), heldReason(from)))
	}
	if why := heldReason(from); why != "" {
		v.unsupported(e.Pos(), rConvToError, fmt.Sprintf("converting a %s to an error is not supported: %s", from, why))
	}
	v.checkedMethods(e, from, val, st, guard)
	leaves := v.goLeaves(st, layout, val)
	err := v.canonicalError(from, leaves)
	if err == nil {
		err = v.fresh("typed error", logic.Err)
	}
	v.noteHeld(st, err, from, leaves)
	return err
}

// canonicalError returns the error that holds a value of a type as a term
// of the value, for a type on which == is identity whose value is one
// integer or a pointer, so that two conversions of equal values are one
// error with no fact needed; nil for any other type, whose conversions are
// errors of their own. leaves are the value's as goLeaves gives them.
func (v *fnVerifier) canonicalError(t types.Type, leaves value) *logic.Term {
	layout, ok := layoutOf(t)
	name, named := canonicalName(t)
	if !ok || !named || !v.identityEq(t) || !capturesValue(layout) {
		return nil
	}
	switch {
	case len(layout) == 1 && layout[0].sort == logic.Int:
		return logic.Select(logic.Const("mkerr "+name, logic.SeqOf(logic.Err)), leaves[0])
	case len(layout) == 2 && layout[0].part == partPtr:
		return logic.Select(logic.Select(logic.Const("mkerr "+name, logic.SeqOf(logic.SeqOf(logic.Err))), leaves[0]), leaves[1])
	}
	return nil
}

// noteHeld states that an error holds a value of a type: it is not nil,
// its tag is the type's, and its held leaves are the value's. The function
// then meets an error a conversion made: every made error met so far, and
// every one met later (noteError), holds a type of package errors or fmt,
// so that such errors are told apart from errors of the project's types. A
// function that meets none states nothing. A type with no canonical name,
// one declared in a function, has no known tag, and nothing can tell it
// apart from another.
func (v *fnVerifier) noteHeld(st *state, err *logic.Term, t types.Type, leaves value) {
	v.typedMet = true
	for _, made := range v.distinct {
		v.noteMadeTag(st, made)
	}
	v.fact(st, logic.Not(logic.IsNil(err)))
	name, named := canonicalName(t)
	if !named {
		return
	}
	layout, _ := layoutOf(t)
	tag, _ := typeTag(t)
	ref := logic.ErrRef(err)
	v.fact(st, logic.Eq(dynTag(ref), tag))
	for i, lf := range layout {
		v.fact(st, eqLeaf(logic.Select(heldTable(name, i, lf), ref), leaves[i]))
	}
	v.meetType(st, t)
}

// meetType records a type of the values errors hold that the function
// meets, when == on it is identity; see sameTyped and holdsIdentityEq.
func (v *fnVerifier) meetType(sink *state, t types.Type) {
	v.noteTagged(sink, t)
	if layout, ok := layoutOf(t); ok && v.identityEq(t) && capturesValue(layout) &&
		!slices.ContainsFunc(v.typedTypes, func(known types.Type) bool { return types.Identical(known, t) }) {
		v.typedTypes = append(v.typedTypes, t)
	}
	// What errors.Is reports of an error that holds a value of the type,
	// for every application of is met so far.
	for _, pair := range v.isPairs {
		v.typedTrees(sink, pair[0], pair[1])
	}
	for _, pair := range v.asPairs {
		v.asFacts(sink, pair, map[string]bool{})
	}
}

// eqLeaf says that two leaves of one sort are equal: a string by its
// bytes, through the number Key gives a sequence, anything else by =.
func eqLeaf(a, b *logic.Term) *logic.Term {
	if a.Sort.IsSeq() {
		return logic.Eq(logic.Key(a), logic.Key(b))
	}
	if a.Sort == logic.Bool {
		return logic.Iff(a, b)
	}
	return logic.Eq(a, b)
}

// noteMadeTag states once in a state that a made error holds one of the
// types of package errors and fmt that errors.New and fmt.Errorf return:
// the one its call gives, when that is known (madeTypes), and otherwise
// one of the three.
func (v *fnVerifier) noteMadeTag(st *state, made *logic.Term) {
	if st == nil || !v.typedMet {
		return
	}
	if note := "made tag " + made.Name; !st.noted[note] {
		st.noted[note] = true
		var options []*logic.Term
		for _, name := range madeErrorTypes {
			if known := v.madeTypes[made.Name]; known == "" || known == name {
				options = append(options, logic.Eq(errorTag(made), logic.BigLit(new(big.Int).SetBytes([]byte(name)))))
			}
		}
		v.fact(st, logic.Or(options...))
	}
}

// madeErrorType returns the canonical name of the type of the error a call
// of errors.New or fmt.Errorf makes, or "" when it is not known: errors.New
// and fmt.Errorf with no %w that takes an operand give an
// *errors.errorString, fmt.Errorf with one a *fmt.wrapError, whatever the
// operand is, and with more a *fmt.wrapErrors (fmt's errorf, which
// TestErrorfTypes checks against the running toolchain).
func (v *fnVerifier) madeErrorType(call *ast.CallExpr, errorf bool) string {
	if !errorf {
		return madeErrorTypes[0]
	}
	if call.Ellipsis.IsValid() {
		return ""
	}
	value := v.info.Types[call.Args[0]].Value
	if value == nil || value.Kind() != constant.String {
		return ""
	}
	count, ok := wrapVerbs(constant.StringVal(value), len(call.Args)-1)
	switch {
	case !ok:
		return ""
	case count == 0:
		return madeErrorTypes[0]
	case count == 1:
		return madeErrorTypes[1]
	}
	return madeErrorTypes[2]
}

// wrapVerbs counts the %w verbs of a format that take one of n operands,
// by the rules formatWraps reads, and reports false for a format it does
// not read.
func wrapVerbs(text string, n int) (int, bool) {
	operand, count := 0, 0
	for i := 0; i < len(text); {
		if text[i] != '%' {
			i++
			continue
		}
		i++
		for i < len(text) && (text[i] == '#' || text[i] == '0' || text[i] == '+' || text[i] == '-' || text[i] == ' ') {
			i++
		}
		digits := func() bool {
			start := i
			for i < len(text) && '0' <= text[i] && text[i] <= '9' {
				i++
			}
			return i-start <= maxFormatDigits
		}
		if i < len(text) && (text[i] == '[' || text[i] == '*') || !digits() {
			return 0, false
		}
		if i < len(text) && text[i] == '.' {
			i++
			if i < len(text) && (text[i] == '[' || text[i] == '*') || !digits() {
				return 0, false
			}
		}
		if i >= len(text) {
			break
		}
		verb, size := utf8.DecodeRuneInString(text[i:])
		i += size
		switch verb {
		case '%':
			continue
		case '[':
			return 0, false
		case 'w':
			if operand < n {
				count++
			}
		}
		operand++
	}
	return count, true
}

// sameTyped states, for two errors that code compares, that they are one
// error when they hold equal values of a type met in a conversion on which
// == is identity: Go's == on them.
func (v *fnVerifier) sameTyped(st *state, a, b *logic.Term) {
	if a == b {
		return
	}
	for _, t := range v.typedTypes {
		name, _ := canonicalName(t)
		tag, _ := typeTag(t)
		layout, _ := layoutOf(t)
		ra, rb := logic.ErrRef(a), logic.ErrRef(b)
		same := []*logic.Term{
			logic.Not(logic.IsNil(a)), logic.Not(logic.IsNil(b)),
			logic.Eq(dynTag(ra), tag), logic.Eq(dynTag(rb), tag),
		}
		for i, lf := range layout {
			same = append(same, eqLeaf(logic.Select(heldTable(name, i, lf), ra), logic.Select(heldTable(name, i, lf), rb)))
		}
		v.fact(st, logic.Implies(logic.And(same...), logic.Eq(a, b)))
	}
}

// checkedMethods refuses a conversion to error of a value whose methods
// may do what verified code cannot account for. An error can reach code
// that is not verified, which may run any method of what it holds at any
// time: a trusted function that runs an error, fmt, or a caller that type-
// asserts it. So every method of the type's method set must have a usable
// contract that modifies nothing, asks nothing, names no variable of a
// group with an invariant, makes no call through a value, and is declared
// on the type itself; the type has no invariant; nothing the type reaches
// through exported fields has methods, which reflection reaches; and
// nothing it holds, in any field at any depth, can carry code nobody
// checked: an interface other than error, or a function type without a
// contract (F13 of the review of S1; an interface whose methods all have
// contracts is refused too since the runs step, as a trusted function
// may assert what it holds to another interface), and no method returns
// such a value. A value receiver
// reached through the converted pointer is read when the method runs, so
// the pointer is proved not nil here, where it is fixed. (S1 of F33;
// values.BoxedImplicitly and typederrors.ThroughAny are what this keeps
// out.)
func (v *fnVerifier) checkedMethods(e ast.Expr, from types.Type, val value, st *state, guard []*logic.Term) {
	shown := func(t types.Type) string { return types.TypeString(t, types.RelativeTo(v.pass.Pkg)) }
	code := "code that is not verified may run any method of an error at any time"
	refuse := func(why, remedy string) {
		v.unsupported(e.Pos(), rConvToError, fmt.Sprintf("converting a %s to an error is not supported: %s; %s, so %s", shown(from), why, code, remedy))
	}
	if set, _ := v.invariantsOf(from); set != nil {
		refuse(fmt.Sprintf("%s has an invariant, which a method run at any time could not assume", shown(from)),
			"a type converted to error must have no invariant")
	}
	if held, path := uncheckedHeld(v.pkgVerifier, from, "", map[types.Type]bool{}); held != nil {
		why := fmt.Sprintf("it holds%s a value of type %s, which can carry code that nothing checks", path, shown(held))
		if types.IsInterface(held) && v.pkgVerifier.fullyContracted(held) {
			// A value converted to the interface was checked against its
			// methods only, and code given the error may assert it to
			// another interface: a trusted function whose entry lists
			// that interface under asserts over an error (asserts.go).
			why = fmt.Sprintf("it holds%s a value of type %s, which was checked only against the methods of %s where it was made, and code given the error may find other methods on it by a type assertion",
				path, shown(held), shown(held))
		}
		refuse(why, "a type converted to error may hold an error or a function type with a contract, and no other code")
	}
	_, fromPointer := from.Underlying().(*types.Pointer)
	methods := types.NewMethodSet(from)
	for selection := range methods.Methods() {
		method := selection.Obj().(*types.Func)
		name := methodOf(method.Type().(*types.Signature).Recv().Type(), method, v.pass.Pkg)
		if len(selection.Index()) > 1 {
			refuse(fmt.Sprintf("its method %s is promoted from an embedded field", method.Name()),
				fmt.Sprintf("declare %s on %s itself", method.Name(), shown(from)))
		}
		fn := v.contractOf(method)
		if fn == nil {
			refuse(fmt.Sprintf("%s has no contract", name), "each method of a type converted to error must have a contract that modifies nothing and has no Requires")
		}
		view := v.viewOf(fn)
		switch {
		case view.cut || len(view.problems) > 0:
			refuse(fmt.Sprintf("the contract of %s cannot be used", name), "fix the contract")
		case len(fn.modifies) > 0:
			refuse(fmt.Sprintf("%s modifies memory", name), "each method of a type converted to error must modify nothing")
		case len(fn.requires) > 0:
			refuse(fmt.Sprintf("%s has a Requires clause, which a call made at any time may not meet", name), "each method of a type converted to error must have no Requires")
		case v.pkgVerifier.mayCallValues(method):
			refuse(fmt.Sprintf("%s may call through a function value or an interface value", name), "each method of a type converted to error must call no code through a value")
		case len(v.pkgVerifier.groupsTouched(fn)) > 0:
			refuse(fmt.Sprintf("%s names a variable of a group with an invariant, which a call made at any time could not assume", name),
				"each method of a type converted to error must name no such variable")
		}
		// What a method returns is what code given the error can assert
		// next, as what the value holds is.
		for result := range method.Type().(*types.Signature).Results().Variables() {
			if held, path := uncheckedHeld(v.pkgVerifier, result.Type(), "", map[types.Type]bool{}); held != nil {
				refuse(fmt.Sprintf("%s returns%s a value of type %s, which can carry code that nothing checked against all that code given the error may call on it",
					name, path, shown(held)),
					"the methods of a type converted to error may return an error or a function type with a contract, and no other code")
			}
		}
		if _, recvPointer := method.Type().(*types.Signature).Recv().Type().(*types.Pointer); fromPointer && !recvPointer {
			done := v.at(e.Pos())
			v.check(st, guard, logic.Ne(val[0], logic.RefLit(0)), e.Pos(),
				"%s has a value receiver, and the pointer converted to error may be nil, so the method would panic when it runs; convert a pointer that is not nil, or the value it points to", name)
			done()
		}
	}
	if reached := methodsReached(from, map[types.Type]bool{}, true); reached != nil {
		refuse(fmt.Sprintf("it holds through an exported field a value of type %s, which has methods", shown(reached)),
			"nothing a type converted to error holds through an exported field may have methods")
	}
}

// uncheckedHeld returns a type that a value of type t holds, in any field
// at any depth, exported or not, through pointers, slices, arrays, maps,
// and channels, that can carry code nothing checks where verified code
// makes it: an interface other than error, since a value converted to one
// is checked against its methods only and code given the error may assert
// it to another; or a function type without a contract; nil when there is
// none. path says where.
func uncheckedHeld(pv *pkgVerifier, t types.Type, path string, seen map[types.Type]bool) (types.Type, string) {
	if seen[t] {
		return nil, ""
	}
	seen[t] = true
	if held, replaced := heldAs(t); replaced {
		return uncheckedHeld(pv, held, path, seen)
	}
	switch u := t.Underlying().(type) {
	case *types.Interface:
		if isError(t) {
			return nil, ""
		}
		return t, path
	case *types.Signature:
		if pv.valueContract(t) != nil {
			return nil, ""
		}
		return t, path
	case *types.Basic:
		if u.Kind() == types.UnsafePointer {
			return t, path
		}
	case *types.Pointer:
		return uncheckedHeld(pv, u.Elem(), path, seen)
	case *types.Slice:
		return uncheckedHeld(pv, u.Elem(), path, seen)
	case *types.Array:
		return uncheckedHeld(pv, u.Elem(), path, seen)
	case *types.Chan:
		return uncheckedHeld(pv, u.Elem(), path, seen)
	case *types.Map:
		if found, where := uncheckedHeld(pv, u.Key(), path, seen); found != nil {
			return found, where
		}
		return uncheckedHeld(pv, u.Elem(), path, seen)
	case *types.Struct:
		for field := range u.Fields() {
			if found, where := uncheckedHeld(pv, field.Type(), path+" in field "+field.Name(), seen); found != nil {
				return found, where
			}
		}
	}
	return nil, ""
}

// methodsReached returns a type with methods that reflection reaches from a
// value of type t through exported fields, pointers, slices, and maps, or
// nil. The type itself is not counted when top is set.
func methodsReached(t types.Type, seen map[types.Type]bool, top bool) types.Type {
	if seen[t] {
		return nil
	}
	seen[t] = true
	if !top && (types.NewMethodSet(t).Len() > 0 || types.NewMethodSet(types.NewPointer(t)).Len() > 0) {
		if _, isPointer := t.Underlying().(*types.Pointer); !isPointer {
			return t
		}
	}
	switch u := t.Underlying().(type) {
	case *types.Pointer:
		return methodsReached(u.Elem(), seen, top)
	case *types.Slice:
		return methodsReached(u.Elem(), seen, false)
	case *types.Array:
		return methodsReached(u.Elem(), seen, false)
	case *types.Map:
		if found := methodsReached(u.Key(), seen, false); found != nil {
			return found
		}
		return methodsReached(u.Elem(), seen, false)
	case *types.Struct:
		for field := range u.Fields() {
			if field.Exported() {
				if found := methodsReached(field.Type(), seen, false); found != nil {
					return found
				}
			}
		}
	}
	return nil
}

// noteTypedVariable states of an error variable whose initialiser converts
// a constant of a defined type to error that it is the error that holds
// the constant, the term code builds for the conversion (F12 of the design
// review), wherever the variable is read: in code and in formulas alike.
func (v *fnVerifier) noteTypedVariable(sink *state, variable *logic.Term, info sentinelInfo) {
	if sink == nil || info.TypedKey == "" {
		return
	}
	named, ok := v.objectByKey(info.TypedKey).(*types.TypeName)
	if !ok {
		return
	}
	number, ok := new(big.Int).SetString(info.TypedValue, 10)
	if !ok {
		return
	}
	leaves := value{logic.BigLit(number)}
	canonical := v.canonicalError(named.Type(), leaves)
	if canonical == nil {
		return
	}
	if note := "typed variable " + variable.Name; sink.noted[note] {
		return
	}
	sink.noted["typed variable "+variable.Name] = true
	v.fact(sink, logic.Eq(variable, canonical))
	v.noteHeld(sink, canonical, named.Type(), leaves)
}

// assertion evaluates x.(T) for an error x (S3 of F33) or another
// interface value (S1 of F34). For a concrete T it is what x holds as a T,
// read from the tables (heldRead), when x is not nil and its tag is T's:
// the one-result form proves that and reports where it may not hold, since
// Go panics there; the two-result form gives the held value or the zero
// value of T, and whether it holds one. x.(error) of an error is x itself,
// which is not nil. An interface T is asserted to by assertIface (S2 of
// F34).
func (v *fnVerifier) assertion(e *ast.TypeAssertExpr, st *state, guard []*logic.Term, commaOk bool) []value {
	from, target := v.info.TypeOf(e.X), v.info.TypeOf(e.Type)
	operand := "an error"
	if !isError(from) {
		operand = "an interface value"
	}
	shown := func(t types.Type) string { return types.TypeString(t, types.RelativeTo(v.pass.Pkg)) }
	if isError(target) && isError(from) {
		x := v.expr(e.X, st, guard)
		holds := logic.Not(logic.IsNil(x))
		if commaOk {
			return []value{{x}, {holds}}
		}
		v.checkAssertion(st, guard, holds, e, types.ExprString(e), "x is nil")
		return []value{{x}}
	}
	if types.IsInterface(target) {
		return v.assertIface(e, st, guard, commaOk)
	}
	tag, named := typeTag(target)
	if !named {
		v.unsupported(e.Pos(), rDynLocalType, fmt.Sprintf("asserting %s to %s is not supported: it is declared inside a function, and nothing tells it apart from another type there", operand, shown(target)))
	}
	layout, _ := layoutOf(target)
	if why := heldReason(target); why != "" {
		v.unsupported(e.Pos(), rDynAssert, fmt.Sprintf("asserting %s to %s is not supported: %s", operand, shown(target), why))
	}
	if why := reflectHeld(v.pass.Pkg, target, "", map[types.Type]bool{}); why != "" {
		v.unsupported(e.Pos(), rDynAssert, fmt.Sprintf("asserting %s to %s is not supported: %s", operand, shown(target), why))
	}
	if why := v.contractedReason(target); why != "" && !(commaOk && v.discarded[e]) {
		v.unsupported(e.Pos(), rDynAssert, fmt.Sprintf("asserting %s to %s is not supported: %s", operand, shown(target), why))
	}
	x := v.expr(e.X, st, guard)
	if !isError(from) {
		// The reference is read twice.
		x = v.named(st, "asserted", x)
		v.meetDynamic(st)
		v.meetHeldType(st, target)
	}
	v.meetAssertion(st, target)
	ref, isNil := refOf(x)
	holds := logic.And(logic.Not(isNil), logic.Eq(dynTag(ref), tag))
	held := v.heldRead(st, x, target)
	v.keyHeldPointer(st, x, from, target, held, holds)
	v.noteAssertedFile(st, x, from, target, held, holds)
	if !commaOk {
		v.checkAssertion(st, guard, holds, e, types.ExprString(e), fmt.Sprintf("%s may not hold %s %s", types.ExprString(e.X), article(shown(target)), shown(target)))
		return []value{held}
	}
	zero := zeroValue(target)
	got := make(value, len(layout))
	for i := range layout {
		got[i] = logic.Ite(holds, held[i], zero[i])
	}
	return []value{got, {holds}}
}

// keyHeldPointer states, of an interface value that holds a pointer whose
// type has states, that the key of its states is the pointer's (F11 of the
// design review of F34): true by A3 for a conversion made here, and by the
// definition of the state for a value from elsewhere. Without it, a static
// call on the pointer taken out would forget the pointer's states and not
// the interface value's.
//
// It holds of every value whose static type has states. Of a value of
// another type, an any, it holds where the value shares the reference of
// one with states, which a conversion between interfaces records
// (keyedByHeld); a conversion to an interface without states has states
// of its own, which nothing can read, so the fact is not stated of it.
// Without the fact a proof only knows less: what the key of the pointer
// is to the value's is not known.
func (v *fnVerifier) keyHeldPointer(st *state, x *logic.Term, from, t types.Type, held value, holds *logic.Term) {
	if x.Sort == logic.Err || !v.pointerKeyed(t) {
		return
	}
	v.notePointerKey(st, held)
	if !v.hasStates(from) {
		holds = logic.And(holds, logic.Select(keyedByHeld, x))
	}
	v.fact(st, logic.Implies(holds, logic.Eq(skey(x), pkey(held))))
}

// reflectHeld says where a value of type t holds, through pointers and
// fields at any depth, a reflect.Value or an unsafe.Pointer, which an error
// of the standard library can hold of memory it was handed: built without
// GOEXPERIMENT=jsonv2, json.Marshal returns for a NaN a
// *json.UnsupportedValueError whose Value refers to the float in the
// memory of what it was given, which reflection could set. Taking such a
// value out of an error or an interface value is refused, so verified code
// never holds one it can reach; "" when there is none. Only fields that
// the package here can name are walked.
func reflectHeld(here *types.Package, t types.Type, path string, seen map[types.Type]bool) string {
	if seen[t] {
		return ""
	}
	seen[t] = true
	if named, ok := types.Unalias(t).(*types.Named); ok && named.Obj().Pkg() != nil && named.Obj().Pkg().Path() == "reflect" && named.Obj().Name() == "Value" {
		return "it holds" + path + " a reflect.Value, through which reflection could set the memory it refers to"
	}
	switch u := t.Underlying().(type) {
	case *types.Basic:
		if u.Kind() == types.UnsafePointer {
			return "it holds" + path + " an unsafe.Pointer, through which the memory it refers to could be set"
		}
	case *types.Pointer:
		return reflectHeld(here, u.Elem(), path, seen)
	case *types.Array:
		return reflectHeld(here, u.Elem(), path, seen)
	case *types.Slice:
		return reflectHeld(here, u.Elem(), path, seen)
	case *types.Map:
		if why := reflectHeld(here, u.Key(), path, seen); why != "" {
			return why
		}
		return reflectHeld(here, u.Elem(), path, seen)
	case *types.Struct:
		for field := range u.Fields() {
			// A field the package cannot name, of a struct of another
			// package, verified code never reads, as the unexported
			// insides of an *os.File (S1 of F34).
			if !field.Exported() && field.Pkg() != here {
				continue
			}
			if why := reflectHeld(here, field.Type(), path+" in field "+field.Name(), seen); why != "" {
				return why
			}
		}
	}
	return ""
}

// contractedHeld says where a value of type t holds, at any depth through
// fields, pointers, slices, arrays, and maps, a function value of a type with
// a contract or an interface value with a method that has one, in words
// that follow "it holds"; "" when there is none. Taking a value of such a
// type out of an interface value is refused (R1 of F34): what an interface
// value holds may have been made by code that is not verified, under no
// claim that it meets the contract, as a trusted function that returns an
// error vouches for nothing it holds. The holdsContractedValue rule of
// trusted results counts no error, and a value taken out would be called
// under the contract (S0 of F34, typederrorspos/contracted.go). Only a
// value taken out is refused: the forms _, ok := x.(T), errors.AsType
// whose value is discarded, and a case whose clause does not use its
// variable give nothing to verified code (F7 of the review of S0).
func contractedHeld(pv *pkgVerifier, t types.Type, path string, seen map[types.Type]bool) string {
	if seen[t] {
		return ""
	}
	seen[t] = true
	if held, replaced := heldAs(t); replaced {
		return contractedHeld(pv, held, path, seen)
	}
	shown := types.TypeString(t, types.RelativeTo(pv.pass.Pkg))
	switch u := t.Underlying().(type) {
	case *types.Signature:
		if pv.valueContract(t) != nil {
			return fmt.Sprintf("%s a function value of type %s, which has a contract", path, shown)
		}
	case *types.Interface:
		if isIface(t) {
			for method := range u.Methods() {
				if pv.methodContract(method) != nil {
					return fmt.Sprintf("%s a value of type %s, whose method %s has a contract", path, shown, method.Name())
				}
			}
		}
	case *types.Pointer:
		return contractedHeld(pv, u.Elem(), path, seen)
	case *types.Slice:
		return contractedHeld(pv, u.Elem(), path, seen)
	case *types.Array:
		return contractedHeld(pv, u.Elem(), path, seen)
	case *types.Map:
		if found := contractedHeld(pv, u.Key(), path, seen); found != "" {
			return found
		}
		return contractedHeld(pv, u.Elem(), path, seen)
	case *types.Struct:
		for field := range u.Fields() {
			if found := contractedHeld(pv, field.Type(), path+" in field "+field.Name(), seen); found != "" {
				return found
			}
		}
	}
	return ""
}

// contractedReason says why a value of type t cannot be taken out of an
// interface value because of what it holds (contractedHeld), or "".
func (v *fnVerifier) contractedReason(t types.Type) string {
	found := contractedHeld(v.pkgVerifier, t, "", map[types.Type]bool{})
	if found == "" {
		return ""
	}
	holds := "it holds" + found
	if _, isSignature := t.Underlying().(*types.Signature); isSignature {
		// The type itself is the function type with a contract.
		holds = "it is" + found
	}
	return holds + ", and nothing claims that a value taken out of an interface value meets that contract: " +
		"code that is not verified may have made it"
}

// usesObject reports whether a node uses an object.
func usesObject(n ast.Node, info *types.Info, obj types.Object) bool {
	used := false
	ast.Inspect(n, func(m ast.Node) bool {
		if id, ok := m.(*ast.Ident); ok && info.Uses[id] == obj {
			used = true
		}
		return !used
	})
	return used
}

// meetAssertion records that the function asks what an error holds: the
// made errors it meets hold types of package errors and fmt, which tells
// them apart from the type asked for.
func (v *fnVerifier) meetAssertion(st *state, t types.Type) {
	v.typedMet = true
	for _, made := range v.distinct {
		v.noteMadeTag(st, made)
	}
	v.meetType(st, t)
}

// checkAssertion proves that a one-result assertion does not panic.
func (v *fnVerifier) checkAssertion(st *state, guard []*logic.Term, holds *logic.Term, e *ast.TypeAssertExpr, text, why string) {
	done := v.at(e.Pos())
	defer done()
	example := "holds(err, T)"
	if !isError(v.info.TypeOf(e.X)) {
		example = "holds(x, T)"
	}
	v.check(st, guard, holds, e.Pos(), "the type assertion %s may panic: %s; use the form v, ok := %s, or show that it holds one, as a contract does with %s",
		text, why, text, example)
}

// typeSwitch executes a type switch on an error (S3 of F33) or another
// interface value (S1 and S2 of F34). The operand is evaluated once; each
// case is a path, taken when one of its types matches and no case before
// it did: a concrete type when the operand holds one, nil when it is nil,
// error on an error when it is not, and an interface when it holds a value
// that implements it (ifaceCase). In a clause with one concrete type the
// variable is what the operand holds as that type, and in a clause with
// one interface type that uses it, the value of the assertion to it
// (ifaceCaseVar); in any other clause it is the operand itself, as Go has
// it.
func (v *fnVerifier) typeSwitch(s *ast.TypeSwitchStmt, st *state, c ctrl, k func(*state)) {
	if s.Init != nil {
		init := s.Init
		v.stmt(init, st, c, func(next *state) {
			without := *s
			without.Init = nil
			v.typeSwitch(&without, next, c, k)
		})
		return
	}
	var assert *ast.TypeAssertExpr
	switch a := s.Assign.(type) {
	case *ast.ExprStmt:
		assert = a.X.(*ast.TypeAssertExpr)
	case *ast.AssignStmt:
		assert = a.Rhs[0].(*ast.TypeAssertExpr)
	}
	from := v.info.TypeOf(assert.X)
	onError := isError(from)
	shown := func(t types.Type) string { return types.TypeString(t, types.RelativeTo(v.pass.Pkg)) }
	var x *logic.Term
	v.evaluate(st, func() { x = v.expr(assert.X, st, nil) })
	if !onError {
		// The reference is read in every case.
		x = v.named(st, "switched", x)
		v.meetDynamic(st)
	}
	ref, isNil := refOf(x)
	inner := ctrl{brk: k, cont: c.cont}
	var failed []*logic.Term
	var fallback *ast.CaseClause
	fallbackEnd := token.NoPos
	for i, clause := range s.Body.List {
		clause := clause.(*ast.CaseClause)
		implicit, _ := v.info.Implicits[clause].(*types.Var)
		if clause.List == nil {
			fallback, fallbackEnd = clause, clauseEnd(s.Body, i)
			continue
		}
		var alternatives []*logic.Term
		var single, singleIface types.Type
		var singleExpr ast.Expr
		for _, e := range clause.List {
			t := v.info.TypeOf(e)
			switch {
			case v.isNil(e):
				alternatives = append(alternatives, isNil)
			case isError(t) && onError:
				alternatives = append(alternatives, logic.Not(isNil))
			case types.IsInterface(t):
				alternatives = append(alternatives, v.ifaceCase(e, x, from, t, st))
				if len(clause.List) == 1 {
					singleIface, singleExpr = t, e
				}
			default:
				tag, named := typeTag(t)
				if !named {
					v.unsupported(e.Pos(), rDynLocalType, fmt.Sprintf("a case of %s in a type switch is not supported: it is declared inside a function, and nothing tells it apart from another type there", shown(t)))
				}
				if why := heldReason(t); why != "" {
					v.unsupported(e.Pos(), rDynSwitch, fmt.Sprintf("a case of %s in a type switch is not supported: %s", shown(t), why))
				}
				if why := reflectHeld(v.pass.Pkg, t, "", map[types.Type]bool{}); why != "" {
					v.unsupported(e.Pos(), rDynSwitch, fmt.Sprintf("a case of %s in a type switch is not supported: %s", shown(t), why))
				}
				if why := v.contractedReason(t); why != "" && len(clause.List) == 1 && implicit != nil && usesObject(clause, v.info, implicit) {
					v.unsupported(e.Pos(), rDynSwitch, fmt.Sprintf("a case of %s in a type switch is not supported: %s", shown(t), why))
				}
				if !onError {
					v.meetHeldType(st, t)
				}
				v.meetAssertion(st, t)
				alternatives = append(alternatives, logic.And(logic.Not(isNil), logic.Eq(dynTag(ref), tag)))
				if len(clause.List) == 1 {
					single = t
				}
			}
		}
		matched := logic.Or(alternatives...)
		v.branch(clause.Pos())
		taken := st.clone()
		taken.decide(logic.And(append(slices.Clip(failed), matched)...))
		if implicit != nil {
			switch {
			case singleIface != nil && usesObject(clause, v.info, implicit):
				v.bind(taken, implicit, v.ifaceCaseVar(singleExpr, assert.X, x, from, singleIface, matched, taken))
			case singleIface != nil && isError(singleIface):
				// The clause does not use it.
				v.bind(taken, implicit, value{logic.NilErr()})
			case singleIface != nil:
				v.bind(taken, implicit, value{logic.RefLit(0)})
			case single != nil:
				held := v.heldRead(taken, x, single)
				v.keyHeldPointer(taken, x, from, single, held, matched)
				v.bind(taken, implicit, held)
			default:
				v.bind(taken, implicit, value{x})
			}
		}
		v.seq(clause.Body, clause.Colon, clauseEnd(s.Body, i), taken, inner, k)
		failed = append(failed, logic.Not(matched))
	}
	st.decide(logic.And(failed...))
	if fallback == nil {
		k(st)
		return
	}
	if implicit, ok := v.info.Implicits[fallback].(*types.Var); ok {
		v.bind(st, implicit, value{x})
	}
	v.seq(fallback.Body, fallback.Colon, fallbackEnd, st, inner, k)
}

// switchVars returns, for the guard of a type switch, x := e.(type), the
// variables of its clauses, and the operand e; nil for any other node.
// go/cfg puts the guard once before the clauses, and the variables have no
// node of their own, so the analyses over the graph give them their facts
// there (F7 of the design review).
func (pv *pkgVerifier) switchVars(n ast.Node) ([]*types.Var, ast.Expr) {
	if pv.typeSwitches == nil {
		pv.typeSwitches = map[ast.Node]*ast.TypeSwitchStmt{}
		for _, file := range pv.pass.Files {
			ast.Inspect(file, func(m ast.Node) bool {
				if s, ok := m.(*ast.TypeSwitchStmt); ok && s.Assign != nil {
					pv.typeSwitches[s.Assign] = s
				}
				return true
			})
		}
	}
	s := pv.typeSwitches[n]
	if s == nil {
		return nil, nil
	}
	assign, ok := s.Assign.(*ast.AssignStmt)
	if !ok {
		return nil, nil
	}
	var vars []*types.Var
	for _, clause := range s.Body.List {
		if implicit, ok := pv.info.Implicits[clause].(*types.Var); ok {
			vars = append(vars, implicit)
		}
	}
	return vars, assign.Rhs[0].(*ast.TypeAssertExpr).X
}

// typedOriginWhy says why the errors a conversion of a value of a concrete
// type makes have no known origin, or "" when they have one (S4 of F33):
// the third known origin, typed, beside made and vouched. It is decided
// from the declarations alone, before anything is verified (F5 of the
// design review): == on the type is identity; no method that errors.Is,
// errors.As, or fmt would run but Error, which has a contract; and what
// the type holds is plain, since fmt prints it for verbs that do not call
// Error. What every method may do is checked at each conversion
// (checkedMethods), which is refused where it fails, so an error of this
// origin runs, through any method, nothing that writes or asks.
func (pv *pkgVerifier) typedOriginWhy(t types.Type) string {
	shown := types.TypeString(t, types.RelativeTo(pv.pass.Pkg))
	if _, named := canonicalName(t); !named {
		return fmt.Sprintf("%s is declared inside a function", shown)
	}
	layout, ok := layoutOf(t)
	if !ok || !pv.identityEq(t) || !capturesValue(layout) {
		return fmt.Sprintf("== on values of %s is not identity", shown)
	}
	methods := types.NewMethodSet(t)
	for _, name := range []string{"Unwrap", "Is", "As", "Format", "GoString"} {
		if methods.Lookup(nil, name) != nil {
			return fmt.Sprintf("%s has a method %s, which errors.Is, errors.As, or fmt would run", shown, name)
		}
	}
	selection := methods.Lookup(nil, "Error")
	if selection == nil {
		return fmt.Sprintf("%s has no method Error", shown)
	}
	if pv.contractOf(selection.Obj().(*types.Func)) == nil {
		return fmt.Sprintf("its method Error has no contract")
	}
	base := t
	if object, isPointer := pointee(t); isPointer {
		base = object
	}
	if why := plainReason(base.Underlying(), map[types.Type]bool{}); why != "" {
		return fmt.Sprintf("fmt prints what %s holds for verbs that do not call Error, where %s", shown, why)
	}
	return ""
}

// concreteErrorType returns the type of an expression, or of one result of
// a call, when it is a concrete type that implements error, which Go
// converts where an error is wanted; nil otherwise.
func (pv *pkgVerifier) concreteErrorType(e ast.Expr, index int) types.Type {
	t := pv.info.TypeOf(e)
	if tuple, ok := t.(*types.Tuple); ok {
		if index < 0 || index >= tuple.Len() {
			return nil
		}
		t = tuple.At(index).Type()
	}
	if t == nil || types.IsInterface(t) || pv.info.Types[e].IsNil() || !types.Implements(t, errorType) {
		return nil
	}
	return t
}

// typedTrees states what errors.Is reports of an error that holds a value
// of a type met in the function on which == is identity and that has no Is
// and no Unwrap method: errors.Is compares the error with the target, as
// isComparable && err == target, and finds nothing below it, so is(e, t) is
// e = t (S4 of F33).
func (v *fnVerifier) typedTrees(sink *state, err, target *logic.Term) {
	if sink == nil || hasBound(err) || hasBound(target) {
		return
	}
	for _, t := range v.typedTypes {
		methods := types.NewMethodSet(t)
		if methods.Lookup(nil, "Is") != nil || methods.Lookup(nil, "Unwrap") != nil {
			continue
		}
		tag, _ := typeTag(t)
		fact := logic.Implies(logic.And(logic.Not(logic.IsNil(err)), logic.Eq(errorTag(err), tag)), logic.Iff(logic.Is(err, target), logic.Eq(err, target)))
		if note := "typed tree " + fact.String(); !sink.noted[note] {
			sink.noted[note] = true
			v.fact(sink, fact)
		}
	}
}

// Interface values other than errors (part 2, F34).
//
// The reference of an interface value is the value itself, where that of
// an error is ErrRef(e): both read the same tables, dyntype for the tag and
// the held tables for the leaves. A conversion of a concrete value records
// what it holds; the facts are stated once the function meets dynamic
// types, by an assertion, a type switch, or a formula that asks what an
// interface value holds, for every conversion made so far and every later
// one, so that a function that never asks states nothing (the pattern of
// noteMadeTag). Stating a fact about the reference of a conversion made on
// another path is harmless: that reference is unconstrained there.

// ifaceConversion is a conversion to an interface other than error: of a
// value of type t, or, when err is set, of an error, which the interface
// value holds as it is.
type ifaceConversion struct {
	ref *logic.Term
	t   types.Type
	val value
	err *logic.Term
	// when, for an error, is when the interface value holds it, if not
	// whenever the error is not nil: an assertion of the error to an
	// interface holds it only when it implements the interface.
	when *logic.Term
}

// holds returns when an interface value made from an error holds it.
func (c ifaceConversion) holds() *logic.Term {
	if c.when != nil {
		return c.when
	}
	return logic.Not(logic.IsNil(c.err))
}

// recordConversion records a conversion, and states its facts at once
// when the function has met dynamic types.
func (v *fnVerifier) recordConversion(st *state, c ifaceConversion) {
	v.ifaceConversions = append(v.ifaceConversions, c)
	if c.t != nil {
		v.noteTagged(st, c.t)
	}
	if dynMetIn(st) {
		v.stateConversion(st, c)
	}
}

// dynMetIn reports whether the path of a state has met dynamic types. It
// is a note of the state, not of the function, since paths are followed
// one after another: a path that split off before another met them has
// not, and gets the facts where it meets them itself.
func dynMetIn(st *state) bool {
	return st != nil && st.noted["dynamic types met"]
}

// meetDynamic records that the path of a state asks what an interface
// value holds, and states there what every conversion so far holds.
func (v *fnVerifier) meetDynamic(st *state) {
	if st == nil || dynMetIn(st) {
		return
	}
	st.noted["dynamic types met"] = true
	for _, c := range v.ifaceConversions {
		v.stateConversion(st, c)
	}
	for _, f := range v.keyedFacts {
		v.fact(st, f)
	}
	for _, t := range v.metTypes {
		v.heldTypeFacts(st, t)
	}
}

// keyedFact states a fact of keyedByHeld at once when the path has met
// dynamic types, and otherwise where it meets them, so that a function
// that meets none asks what it asked before them.
func (v *fnVerifier) keyedFact(st *state, f *logic.Term) {
	v.keyedFacts = append(v.keyedFacts, f)
	if dynMetIn(st) {
		v.fact(st, f)
	}
}

// stateConversion states what a conversion holds: the tag and the leaves
// of the value, nil pointers at position zero (TI and HV); or, for an
// error, its tag and, for every type met, its leaves.
func (v *fnVerifier) stateConversion(st *state, c ifaceConversion) {
	if c.err != nil {
		v.fact(st, logic.Implies(c.holds(), logic.Eq(dynTag(c.ref), errorTag(c.err))))
		for _, t := range v.metTypes {
			if name, _ := canonicalName(t); st.noted["held type "+name] {
				v.sameHeld(st, c, t)
			}
		}
		if metIfaceIn(st, types.Universe.Lookup("error").Type()) {
			v.errorImplements(st, c)
		}
		return
	}
	name, named := canonicalName(c.t)
	layout, ok := layoutOf(c.t)
	if !named || !ok {
		return
	}
	tag, _ := typeTag(c.t)
	leaves := v.goLeaves(st, layout, c.val)
	v.fact(st, logic.Eq(dynTag(c.ref), tag))
	for i, lf := range layout {
		v.fact(st, eqLeaf(logic.Select(heldTable(name, i, lf), c.ref), leaves[i]))
	}
	v.meetHeldType(st, c.t)
}

// sameHeld states that an interface value made from an error holds what
// the error holds as a value of type t.
func (v *fnVerifier) sameHeld(st *state, c ifaceConversion, t types.Type) {
	name, _ := canonicalName(t)
	layout, _ := layoutOf(t)
	ref := logic.ErrRef(c.err)
	for i, lf := range layout {
		table := heldTable(name, i, lf)
		v.fact(st, logic.Implies(c.holds(), eqLeaf(logic.Select(table, c.ref), logic.Select(table, ref))))
	}
}

// meetHeldType records a type whose values an interface value is asked
// to hold, and states for every error converted to an interface that the
// interface value holds what the error holds as a value of it.
func (v *fnVerifier) meetHeldType(st *state, t types.Type) {
	if _, named := canonicalName(t); !named {
		return
	}
	if _, ok := layoutOf(t); !ok {
		return
	}
	if !slices.ContainsFunc(v.metTypes, func(known types.Type) bool { return types.Identical(known, t) }) {
		v.metTypes = append(v.metTypes, t)
	}
	v.noteTagged(st, t)
	if dynMetIn(st) {
		v.heldTypeFacts(st, t)
	}
}

// heldTypeFacts states, once in a state, that every interface value made
// from an error holds what the error holds as a value of t.
func (v *fnVerifier) heldTypeFacts(st *state, t types.Type) {
	name, _ := canonicalName(t)
	if note := "held type " + name; !st.noted[note] {
		st.noted[note] = true
		for _, c := range v.ifaceConversions {
			if c.err != nil {
				v.sameHeld(st, c, t)
			}
		}
		for _, p := range v.eqPairs {
			v.eqTypeFact(st, p, t)
		}
	}
}

// refOf returns the reference at which the tables are read for what an
// interface value or an error holds, and whether it is nil.
func refOf(x *logic.Term) (ref, isNil *logic.Term) {
	if x.Sort == logic.Err {
		return logic.ErrRef(x), logic.IsNil(x)
	}
	return x, logic.Eq(x, logic.RefLit(0))
}
