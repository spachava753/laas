package vego

import (
	"fmt"
	"go/ast"
	"go/types"
	"math/big"
	"reflect"
	"slices"
	"strconv"
	"strings"
	"unicode"

	"golang.org/x/tools/go/types/typeutil"

	"github.com/spachava753/laas/vego/internal/logic"
	"github.com/spachava753/laas/vego/internal/solver"
)

// JSON (F29). A shipped entry with encodes, json.Marshal and
// json.MarshalIndent, names its parameter of type any whose value it
// encodes as package encoding/json does. Its claim: the function encodes
// the value as encoding/json does; it runs no method of what the value
// holds but those of the three leaves of the standard library that
// encoding/json runs (jsonLeafMethods), and runs them only while the call
// lasts, on the calling goroutine; it keeps nothing of the value; and what
// it allocates is within the bound that vego proves at each call. In place
// of runs, the static type of what each call hands it is walked
// (jsonPlainReason), and the bound is generated for that type
// (jsonGroups) and proved where the call stands (checkEncodedAlloc).
//
// The claim must hold of every build of encoding/json that a program can
// be built with: Go 1.26 and Go 1.27, each with and without the jsonv2
// experiment, which replaces the package's code by encoding/json/v2.

// jsonMethods are the methods that some build of encoding/json calls on
// what it encodes or decodes, found through the value's or its pointer's
// method set. A type that has one is not walked into: no method of the
// project runs under the claim (F29, D4).
var jsonMethods = []string{"MarshalJSON", "MarshalJSONTo", "AppendText", "MarshalText", "UnmarshalJSON", "UnmarshalJSONFrom", "UnmarshalText"}

// jsonLeaf names a type of the standard library that encoding/json
// encodes by its own methods or by a rule of its own, and that vego
// counts as a leaf, or "" for any other type. Only the types themselves
// are leaves: a struct that embeds time.Time promotes its MarshalJSON and
// is refused by the method check.
func jsonLeaf(t types.Type) string {
	named, ok := types.Unalias(t).(*types.Named)
	if !ok || named.Obj().Pkg() == nil {
		return ""
	}
	switch path, name := named.Obj().Pkg().Path(), named.Obj().Name(); {
	case path == "time" && name == "Time":
		return "time"
	case path == "encoding/json" && name == "RawMessage", path == "encoding/json/jsontext" && name == "Value":
		// json.RawMessage is an alias of jsontext.Value in the builds
		// with jsonv2.
		return "raw"
	case path == "encoding/json" && name == "Number":
		return "number"
	}
	return ""
}

// jsonTag is what the json key of a struct tag says.
type jsonTag struct {
	name              string
	skip              bool
	quoted            bool
	omitzero          bool
	present, hasValue bool
}

// jsonTagOptions are the options of a json tag that every build reads
// the same way (F29, D7).
var jsonTagOptions = map[string]bool{"omitempty": true, "omitzero": true, "string": true}

// parseJSONTag reads the json key of a struct tag, or says why it is
// refused: an option other than omitempty, omitzero, and string, which the
// builds read differently, and a name that v1 would not take, or that
// holds a quote or a backslash, which the builds read differently (F7).
func parseJSONTag(tag string) (jsonTag, string) {
	value, ok := reflect.StructTag(tag).Lookup("json")
	if !ok {
		return jsonTag{}, ""
	}
	t := jsonTag{present: true, hasValue: value != ""}
	if value == "-" {
		t.skip = true
		return t, ""
	}
	name, opts, _ := strings.Cut(value, ",")
	if name != "" && !validJSONName(name) {
		return t, fmt.Sprintf("its json tag names it %q, which the builds of encoding/json read differently; use letters, digits, and the punctuation !#$%%&()*+-./:;<=>?@[]^_{|}~ and space", name)
	}
	t.name = name
	if opts != "" {
		for opt := range strings.SplitSeq(opts, ",") {
			switch {
			case opt == "":
			case !jsonTagOptions[opt]:
				return t, fmt.Sprintf("its json tag has the option %q, which the builds of encoding/json treat differently; only omitempty, omitzero, and string are supported", opt)
			case opt == "string":
				t.quoted = true
			case opt == "omitzero":
				t.omitzero = true
			}
		}
	}
	return t, ""
}

// validJSONName is v1's isValidTag, with ', ", and \ refused too.
func validJSONName(s string) bool {
	if s == "" {
		return false
	}
	for _, c := range s {
		switch {
		case strings.ContainsRune("!#$%&()*+-./:;<=>?@[]^_{|}~ ", c):
		case !unicode.IsLetter(c) && !unicode.IsDigit(c):
			return false
		}
	}
	return true
}

// jsonKeyWeight is what the key of a field takes in the output, with its
// quotes, its colon, and the comma after it: encoding/json escapes <, >,
// and & to six bytes each.
func jsonKeyWeight(name string) int64 {
	n := int64(0)
	for i := range len(name) {
		switch name[i] {
		case '<', '>', '&':
			n += 6
		default:
			n++
		}
	}
	return n + 4
}

// A jsonStep is one step of a chain of the walk: a quantifier over the
// elements of a slice or the keys of a map, whose length multiplies what
// lies under it, or a guard that a pointer is not nil.
type jsonStep struct {
	binder string // "i1 in [0, |v.Tags|)", or "k1 in v.M"
	length string // "|v.Tags|"
	guard  string // "v.P != nil"
}

// A jsonGroup is the part of the output that lies under one chain of
// steps: a constant and lengths, each with its weight, for each element of
// each container on the chain.
type jsonGroup struct {
	steps []jsonStep
	konst int64
	terms []jsonTerm
}

// A jsonTerm is a length with its weight, as 6 * |v.Text|.
type jsonTerm struct {
	coef int64
	path string
}

// jsonWeightTable holds what each part of the output takes, in bytes, at
// most, in every build of encoding/json; TestJSONWeights holds each of
// them against the builds and shows that each made one smaller fails.
type jsonWeightTable struct {
	// Bool is false; Null is null, for a nil slice, map, or pointer, which
	// is also more than the brackets or braces of an empty one; Braces
	// are those of a struct; Comma follows each element; KeyExtra is a
	// key's quotes, its colon, and the comma after the value; EntryExtra
	// is the colon and the comma of a map entry.
	Bool, Null, Braces, Comma, KeyExtra, EntryExtra int64
	// Float64 and Float32 are the longest number a float prints as.
	Float64, Float32 int64
	// IntLess is taken from the digits of an integer, for the test only.
	IntLess int64
	// Time is a time.Time with nanoseconds and an offset, in quotes.
	Time int64
	// A string is StringPer bytes for each byte (\u00XX) and its quotes;
	// under the option string, QuotedPer and QuotedConst; a number or a
	// bool under it gains QuotedExtra, its quotes.
	StringPer, StringConst, QuotedPer, QuotedConst, QuotedExtra int64
	// []byte is base64 with padding in quotes, or null.
	BytesPer, BytesConst int64
	// A json.RawMessage is compacted with <, >, &, U+2028, and U+2029
	// escaped, or null; a json.Number is its text, or 0 when empty.
	RawPer, RawConst, NumberPer, NumberConst int64
	// NoEntryAlloc leaves out what a map's entries allocate, which is no
	// part of the output, for the test of the output's weights only.
	NoEntryAlloc bool
}

// jsonWeights is the table the verifier uses.
var jsonWeights = jsonWeightTable{
	Bool: 5, Null: 4, Braces: 2, Comma: 1, KeyExtra: 4, EntryExtra: 2,
	Float64: 25, Float32: 22, Time: 37,
	StringPer: 6, StringConst: 2, QuotedPer: 7, QuotedConst: 6, QuotedExtra: 2,
	BytesPer: 2, BytesConst: 4, RawPer: 6, RawConst: 4, NumberPer: 1, NumberConst: 1,
}

// jsonWalk walks a type as encoding/json encodes it, from the static type
// of what a call hands over, and gathers the groups of the bound, or says
// why the type is refused.
type jsonWalk struct {
	wt     jsonWeightTable
	pkg    *types.Package
	sizes  types.Sizes
	groups []*jsonGroup
	// depth is the deepest nesting of arrays and objects the type allows,
	// and raw is set when it holds a json.RawMessage, whose own nesting
	// encoding/json bounds by 10000.
	depth int
	raw   bool
	// stack holds the named types being walked, so that a type that
	// holds itself is refused.
	stack []types.Type
	n     int
	// elems and keys count the bound variables named so far, and steps
	// the types entered.
	elems, keys, steps int
}

// jsonPlainReason says why a value of type t, written as e, cannot be
// encoded under the claim of encodes, or returns "" with the groups of the
// bound when it can.
func jsonPlainReason(pkg *types.Package, sizes types.Sizes, t types.Type, name string) (string, *jsonWalk) {
	return jsonWalkWith(jsonWeights, pkg, sizes, t, name)
}

// jsonWalkWith is jsonPlainReason with a table of weights.
func jsonWalkWith(wt jsonWeightTable, pkg *types.Package, sizes types.Sizes, t types.Type, name string) (string, *jsonWalk) {
	w := &jsonWalk{wt: wt, pkg: pkg, sizes: sizes}
	top := &jsonGroup{}
	w.groups = append(w.groups, top)
	if why := w.value(t, name, name, top, false, 0); why != "" {
		return why, nil
	}
	return "", w
}

// shown spells a type relative to the package.
func (w *jsonWalk) shown(t types.Type) string {
	return types.TypeString(t, types.RelativeTo(w.pkg))
}

// The walk's hard limits. A type past one is refused: no type, whatever
// the rest of the walk does, can make it grow without end.
const (
	jsonMaxDepth  = 32    // levels of arrays, objects, and embedded structs
	jsonMaxGroups = 256   // groups of the bound
	jsonMaxSteps  = 20000 // types entered in one walk
)

// child opens the group under one more step of a chain.
func (w *jsonWalk) child(g *jsonGroup, step jsonStep) *jsonGroup {
	c := &jsonGroup{steps: append(slices.Clip(g.steps), step)}
	w.groups = append(w.groups, c)
	return c
}

// enter is passed by every type the walk looks into, at the given depth.
// It refuses a named type that is already being walked, since a value of
// it could then hold itself, and a walk past the limits; otherwise it
// returns a function that leaves the type.
func (w *jsonWalk) enter(t types.Type, shown string, depth int) (string, func()) {
	w.steps++
	switch {
	case depth > jsonMaxDepth:
		return fmt.Sprintf("%s lies more than %d levels deep, which the bound of encoding/json in vego does not follow", shown, jsonMaxDepth), nil
	case len(w.groups) > jsonMaxGroups:
		return fmt.Sprintf("%s makes the bound of encoding/json in vego count more than %d chains of slices, maps, and pointers; encode a smaller type", shown, jsonMaxGroups), nil
	case w.steps > jsonMaxSteps:
		return fmt.Sprintf("%s makes the walk of encoding/json in vego look at more than %d types; encode a smaller type", shown, jsonMaxSteps), nil
	}
	named, ok := types.Unalias(t).(*types.Named)
	if !ok {
		return "", func() {}
	}
	if slices.ContainsFunc(w.stack, func(s types.Type) bool { return types.Identical(s, named) }) {
		return fmt.Sprintf("%s is of type %s, which holds itself, so a value of it can be nested without end or refer to itself", shown, w.shown(t)), nil
	}
	w.stack = append(w.stack, named)
	return "", func() { w.stack = w.stack[:len(w.stack)-1] }
}

// name returns a new name for a bound variable: i, j, then i3, i4, ...
// for the elements of slices, and k, k2, ... for the keys of maps.
func (w *jsonWalk) name(kind string) string {
	w.n++
	if kind == "k" {
		w.keys++
		if w.keys == 1 {
			return "k"
		}
		return fmt.Sprintf("k%d", w.keys)
	}
	w.elems++
	switch w.elems {
	case 1:
		return "i"
	case 2:
		return "j"
	}
	return fmt.Sprintf("i%d", w.elems)
}

// jsonMethodOf returns a method of jsonMethods that a value of type t, or a
// pointer to one, has, or "".
func jsonMethodOf(t types.Type, names []string) string {
	sets := []*types.MethodSet{types.NewMethodSet(t)}
	if _, isPointer := types.Unalias(t).(*types.Pointer); !isPointer && !types.IsInterface(t) {
		sets = append(sets, types.NewMethodSet(types.NewPointer(t)))
	}
	for _, set := range sets {
		for _, name := range names {
			if set.Lookup(nil, name) != nil {
				return name
			}
		}
	}
	return ""
}

// value adds what a value of type t at path takes to g. shown is how a
// message names the value; quoted is set under the option string; depth
// is how deep in arrays and objects it lies.
func (w *jsonWalk) value(t types.Type, path, shown string, g *jsonGroup, quoted bool, depth int) string {
	w.depth = max(w.depth, depth)
	if leaf := jsonLeaf(t); leaf != "" {
		switch leaf {
		case "time":
			// "2006-01-02T15:04:05.999999999-07:00" with its quotes.
			g.konst += w.wt.Time
		case "raw":
			// null when nil; otherwise compacted with <, >, &, U+2028,
			// and U+2029 escaped to six bytes each.
			g.konst += w.wt.RawConst
			g.terms = append(g.terms, jsonTerm{w.wt.RawPer, path})
			w.raw = true
		case "number":
			// 0 when empty.
			g.konst += w.wt.NumberConst
			g.terms = append(g.terms, jsonTerm{w.wt.NumberPer, path})
		}
		if quoted {
			return fmt.Sprintf("%s has the option string, which encoding/json applies only to strings, numbers, and booleans", shown)
		}
		return ""
	}
	if method := jsonMethodOf(t, jsonMethods); method != "" {
		return fmt.Sprintf("%s is of type %s, which has the method %s, and encoding/json would call it; no method of a value runs under "+
			"the contract of encoding/json in vego but those of time.Time, json.RawMessage, and json.Number; encode a type without it", shown, w.shown(t), method)
	}
	// A struct is entered by object, where every way to it passes.
	if _, isStruct := t.Underlying().(*types.Struct); !isStruct {
		why, leave := w.enter(t, shown, depth)
		if why != "" {
			return why
		}
		defer leave()
	}
	if inner, ok := holdsState(t); ok {
		return fmt.Sprintf("%s holds %s, which is not data that encoding/json can see", shown, holding(inner, types.RelativeTo(w.pkg)))
	}
	switch u := t.Underlying().(type) {
	case *types.Basic:
		var weight int64
		switch {
		case u.Kind() == types.Bool:
			weight = w.wt.Bool
		case u.Info()&types.IsInteger != 0:
			weight = integerDigits(u, w.sizes) - w.wt.IntLess
		case u.Kind() == types.Float64:
			weight = w.wt.Float64
		case u.Kind() == types.Float32:
			weight = w.wt.Float32
		case u.Kind() == types.String:
			if quoted {
				// The JSON string, quoted again: every byte that is
				// escaped gains a backslash, and the quotes two.
				g.konst += w.wt.QuotedConst
				g.terms = append(g.terms, jsonTerm{w.wt.QuotedPer, path})
				return ""
			}
			g.konst += w.wt.StringConst
			g.terms = append(g.terms, jsonTerm{w.wt.StringPer, path})
			return ""
		default:
			return fmt.Sprintf("%s is of type %s, which encoding/json cannot encode", shown, w.shown(t))
		}
		if quoted {
			weight += w.wt.QuotedExtra
		}
		g.konst += weight
		return ""
	case *types.Slice:
		if quoted {
			return fmt.Sprintf("%s has the option string, which encoding/json applies only to strings, numbers, and booleans", shown)
		}
		if b, ok := u.Elem().Underlying().(*types.Basic); ok && b.Kind() == types.Uint8 && jsonMethodOf(u.Elem(), jsonMethods) == "" {
			// Base64 with padding, or null: 4 * ceil(n / 3) + 2.
			g.konst += w.wt.BytesConst
			g.terms = append(g.terms, jsonTerm{w.wt.BytesPer, path})
			return ""
		}
		// null, or the brackets.
		g.konst += w.wt.Null
		index := w.name("i")
		c := w.child(g, jsonStep{binder: fmt.Sprintf("%s in [0, |%s|)", index, path), length: "|" + path + "|"})
		c.konst += w.wt.Comma
		return w.value(u.Elem(), path+"["+index+"]", shown+"["+index+"]", c, false, depth+1)
	case *types.Map:
		if quoted {
			return fmt.Sprintf("%s has the option string, which encoding/json applies only to strings, numbers, and booleans", shown)
		}
		key, ok := u.Key().Underlying().(*types.Basic)
		if !ok || (key.Info()&types.IsInteger == 0 && key.Kind() != types.String) {
			return fmt.Sprintf("%s is a map with keys of type %s; encoding/json encodes maps with keys that are strings or integers", shown, w.shown(u.Key()))
		}
		if method := jsonMethodOf(u.Key(), append(slices.Clip(jsonMethods), "String")); method != "" {
			return fmt.Sprintf("%s is a map with keys of type %s, which has the method %s; use keys of a type without methods", shown, w.shown(u.Key()), method)
		}
		g.konst += w.wt.Null
		k := w.name("k")
		c := w.child(g, jsonStep{binder: fmt.Sprintf("%s in %s", k, path), length: "|" + path + "|"})
		// The colon and the comma, and what the builds allocate for each
		// entry to sort the keys: v1 makes a slice of a reflect.Value and a
		// string (5 words) for each entry; v2 a slice of members, of a
		// string and two addressable reflect.Values (10 words), and slices
		// of the keys and of the values, or for keys of a string kind a
		// slice of their strings (2 words). Every one of these is at most
		// 10 words, the key, and the value.
		c.konst += w.wt.EntryExtra
		if !w.wt.NoEntryAlloc {
			c.konst += 10*w.sizes.Sizeof(types.Typ[types.Uintptr]) + w.sizes.Sizeof(u.Key()) + w.sizes.Sizeof(u.Elem())
		}
		if key.Kind() == types.String {
			c.konst += w.wt.StringConst
			c.terms = append(c.terms, jsonTerm{w.wt.StringPer, k})
		} else {
			c.konst += integerDigits(key, w.sizes) - w.wt.IntLess + w.wt.QuotedExtra
		}
		return w.value(u.Elem(), path+"["+k+"]", shown+"["+k+"]", c, false, depth+1)
	case *types.Pointer:
		if quoted {
			return fmt.Sprintf("%s has the option string, which encoding/json applies only to strings, numbers, and booleans", shown)
		}
		if _, ok := u.Elem().Underlying().(*types.Struct); !ok {
			return fmt.Sprintf("%s is of type %s; pointers to anything but a struct are not supported", shown, w.shown(t))
		}
		if method := jsonMethodOf(u.Elem(), jsonMethods); method != "" {
			return fmt.Sprintf("%s is of type %s, which has the method %s, and encoding/json would call it; no method of a value runs under "+
				"the contract of encoding/json in vego but those of time.Time, json.RawMessage, and json.Number; encode a type without it", shown, w.shown(t), method)
		}
		g.konst += w.wt.Null
		c := w.child(g, jsonStep{guard: path + " != nil"})
		return w.object(u.Elem(), path, shown, c, depth)
	case *types.Struct:
		if quoted {
			return fmt.Sprintf("%s has the option string, which encoding/json applies only to strings, numbers, and booleans", shown)
		}
		return w.object(t, path, shown, g, depth)
	case *types.Interface:
		return fmt.Sprintf("%s is an interface value of type %s, whose dynamic type vego does not know; encode a value of a concrete type", shown, w.shown(t))
	default:
		return fmt.Sprintf("%s is of type %s, which encoding/json cannot encode or vego does not support", shown, w.shown(t))
	}
}

// object adds a struct of type t at path: its braces and its fields.
func (w *jsonWalk) object(t types.Type, path, shown string, g *jsonGroup, depth int) string {
	why, leave := w.enter(t, shown, depth)
	if why != "" {
		return why
	}
	defer leave()
	g.konst += w.wt.Braces
	return w.fields(t, path, shown, g, depth+1)
}

// fields adds the fields of a struct of type t at path, as encoding/json
// lists them: each exported field, under the name its tag gives, and the
// fields of each embedded struct, exported or not, by value and through a
// pointer, as if they were the struct's own (F2). Every field is counted,
// so the bound holds whichever of two fields of one name encoding/json
// keeps and whatever omitempty and omitzero omit.
func (w *jsonWalk) fields(t types.Type, path, shown string, g *jsonGroup, depth int) string {
	st := t.Underlying().(*types.Struct)
	for i := range st.NumFields() {
		f := st.Field(i)
		tag, why := parseJSONTag(st.Tag(i))
		fieldPath, fieldShown := path+"."+f.Name(), shown+"."+f.Name()
		if why != "" {
			return fmt.Sprintf("%s: %s", fieldShown, why)
		}
		if tag.skip {
			continue
		}
		if f.Embedded() {
			if tag.hasValue {
				return fmt.Sprintf("%s is embedded with a json tag, which the builds of encoding/json treat differently; give the field a name, or remove the tag", fieldShown)
			}
			ft, isPointer := f.Type(), false
			if p, ok := types.Unalias(ft).(*types.Pointer); ok {
				ft, isPointer = p.Elem(), true
			}
			if _, ok := ft.Underlying().(*types.Struct); ok {
				if !f.Exported() && f.Pkg() != w.pkg {
					return fmt.Sprintf("%s is an embedded struct of package %s that is not exported, whose fields a formula here cannot name", fieldShown, f.Pkg().Path())
				}
				if method := jsonMethodOf(ft, jsonMethods); method != "" {
					return fmt.Sprintf("%s is of type %s, which has the method %s, and encoding/json would call it; encode a type without it", fieldShown, w.shown(ft), method)
				}
				why, leave := w.enter(ft, fieldShown, depth+1)
				if why != "" {
					return why
				}
				if isPointer {
					c := w.child(g, jsonStep{guard: fieldPath + " != nil"})
					why = w.fields(ft, fieldPath, fieldShown, c, depth)
				} else {
					why = w.fields(ft, fieldPath, fieldShown, g, depth)
				}
				leave()
				if why != "" {
					return why
				}
				continue
			}
			if !f.Exported() {
				return fmt.Sprintf("%s is an embedded field of type %s, which is not exported and not a struct, and the builds of encoding/json treat it differently", fieldShown, w.shown(f.Type()))
			}
		} else if !f.Exported() {
			if tag.present {
				return fmt.Sprintf("%s is not exported and has a json tag, which the builds of encoding/json treat differently; remove the tag", fieldShown)
			}
			continue
		}
		if !f.Exported() && f.Pkg() != w.pkg {
			return fmt.Sprintf("%s cannot be named by a formula here", fieldShown)
		}
		if tag.omitzero && jsonLeaf(f.Type()) != "time" && jsonMethodOf(f.Type(), []string{"IsZero"}) != "" {
			return fmt.Sprintf("%s has the option omitzero, and its type %s has the method IsZero, which encoding/json would call; remove the option or the method",
				fieldShown, w.shown(f.Type()))
		}
		name := tag.name
		if name == "" {
			name = f.Name()
		}
		g.konst += jsonKeyWeight(name) - 4 + w.wt.KeyExtra
		if why := w.value(f.Type(), fieldPath, fieldShown, g, tag.quoted, depth); why != "" {
			return why
		}
	}
	return ""
}

// integerDigits is the longest decimal form of an integer of a basic
// type, with its sign.
func integerDigits(b *types.Basic, sizes types.Sizes) int64 {
	size := sizes.Sizeof(b)
	signed := b.Info()&types.IsUnsigned == 0
	n := new(big.Int).Lsh(big.NewInt(1), uint(8*size))
	if signed {
		n.Rsh(n, 1)
		return int64(len(n.String())) + 1 // -128
	}
	n.Sub(n, big.NewInt(1))
	return int64(len(n.String()))
}

// jsonDepthLimit is the deepest nesting that encoding/json accepts in every
// build.
const jsonDepthLimit = 10000

// clauses returns the generated obligations, in terms of the parameter
// named v: for each group, that what it builds, with its share of the
// groups, fits twice and a page within MaxAlloc and five times within
// MaxInt. factor multiplies what each byte becomes, for MarshalIndent.
func (w *jsonWalk) clauses(factor string) []string {
	n := len(w.groups)
	var out []string
	for _, g := range w.groups {
		product := []string{strconv.Itoa(n)}
		for _, s := range g.steps {
			if s.length != "" {
				product = append(product, s.length)
			}
		}
		weight := []string{strconv.FormatInt(g.konst, 10)}
		for _, t := range g.terms {
			weight = append(weight, fmt.Sprintf("%d * |%s|", t.coef, t.path))
		}
		built := strings.Join(product, " * ") + " * (" + strings.Join(weight, " + ") + ")"
		if factor != "" {
			built += " * (" + factor + ")"
		}
		for _, goal := range []string{"3 * " + built + " + 65536 <= MaxAlloc", "5 * " + built + " <= MaxInt"} {
			out = append(out, w.wrap(g.steps, goal))
		}
	}
	return out
}

// wrap puts a goal under the steps of a chain.
func (w *jsonWalk) wrap(steps []jsonStep, goal string) string {
	body := goal
	for i := len(steps) - 1; i >= 0; i-- {
		if steps[i].guard != "" {
			body = steps[i].guard + " -> (" + body + ")"
		} else {
			body = "Forall " + steps[i].binder + " : (" + body + ")"
		}
	}
	return body
}

// readEncodes reads what the entry of a trusted function lists under
// encodes: one parameter of type any. Only a shipped entry may (F29, F13):
// the claim is checked per value at each call, and what it would mean for
// a wrapper of a project is not written down.
func (pv *pkgVerifier) readEncodes(fn *funcInfo, entry *trustEntry) {
	if len(entry.encodes) == 0 {
		return
	}
	if entry.file == nil || !entry.file.shipped {
		fn.defect("it lists encodes, which only the entries that come with vego can list; a function of your own that encodes a value it is handed is not supported yet")
		return
	}
	sig := fn.obj.Type().(*types.Signature)
	for _, item := range entry.encodes {
		param, ok := fn.paramNames[item.text]
		switch {
		case !ok || param == sig.Recv():
			fn.defect("its encodes %q: %s is not a parameter", item.text, item.text)
		case fn.encoded != nil:
			fn.defect("its encodes lists %s and %s; it can list one parameter of type any", fn.encoded.Name(), item.text)
		case !isAnyParam(sig, param) || (sig.Variadic() && param == sig.Params().At(sig.Params().Len()-1)):
			fn.defect("its encodes lists %s, of type %s; it can list a parameter of type any", item.text, param.Type())
		case fn.runs.get(param):
			fn.defect("its encodes lists %s, which its runs lists too; encodes says what the function runs of it", item.text)
		default:
			fn.encoded = param
		}
	}
	if len(entry.formats) > 0 || len(entry.calls) > 0 || len(entry.keeps) > 0 || len(entry.asserts) > 0 || len(entry.prints) > 0 {
		fn.defect("it lists encodes with formats, calls, keeps, asserts, or prints; encodes says all the function runs and keeps of what it encodes")
	}
}

// encodedArg returns the expression a call hands to the parameter that
// a contract encodes, or nil.
func (v *fnVerifier) encodedArg(call *ast.CallExpr, fn *funcInfo) ast.Expr {
	if fn.encoded == nil {
		return nil
	}
	for _, b := range v.bindCall(call, fn.obj.Type().(*types.Signature)) {
		if b.param == fn.encoded && b.expr != nil {
			return b.expr
		}
	}
	return nil
}

// checkEncodable refuses a call whose encoded value is of a type the walk
// refuses, before the arguments are evaluated.
func (v *fnVerifier) checkEncodable(call *ast.CallExpr, fn *funcInfo) {
	arg := v.encodedArg(call, fn)
	if arg == nil {
		return
	}
	if why, _ := jsonPlainReason(v.pass.Pkg, v.pass.TypesSizes, v.info.TypeOf(arg), types.ExprString(arg)); why != "" {
		v.unsupported(arg.Pos(), fmt.Sprintf("%s encodes %s, and %s", fn.obj.Name(), types.ExprString(arg), why))
	}
}

// checkEncodedAlloc proves, at a call of a function whose entry lists
// encodes, that what it builds from the value can be allocated: the
// obligations jsonWalk.clauses generates for the static type of what the
// call hands over, read with the parameter bound to that value as it was
// before its conversion to any. extra is what the function builds beyond
// what Marshal builds, as Encode's newline.
func (v *fnVerifier) checkEncodedAlloc(st *state, guard []*logic.Term, call *ast.CallExpr, fn *funcInfo, args map[*types.Var]value, held map[ast.Expr]value, extra int64) {
	arg := v.encodedArg(call, fn)
	if arg == nil {
		return
	}
	t := v.info.TypeOf(arg)
	why, walk := jsonPlainReason(v.pass.Pkg, v.pass.TypesSizes, t, "v")
	if why != "" {
		// Refused before the arguments were evaluated.
		return
	}
	walk.groups[0].konst += extra
	val := held[ast.Unparen(arg)]
	if val == nil {
		panic(fmt.Sprintf("vego: internal error: the value %s handed to %s was not kept as it was before its conversion", types.ExprString(arg), fn.obj.Name()))
	}
	// A contract of one parameter, v, of the static type, and the string
	// parameters MarshalIndent reads.
	vars := []*types.Var{types.NewParam(arg.Pos(), v.pass.Pkg, "v", t)}
	bound := map[*types.Var]value{vars[0]: val}
	factor := ""
	for _, b := range v.bindCall(call, fn.obj.Type().(*types.Signature)) {
		if b.param != fn.encoded && b.expr != nil && isString(b.param.Type()) {
			p := types.NewParam(b.expr.Pos(), v.pass.Pkg, b.param.Name(), b.param.Type())
			vars = append(vars, p)
			bound[p] = args[b.param]
		}
	}
	if len(vars) == 3 {
		// Each byte of the compact output may become a newline, the
		// prefix, and the indent once for each level of nesting, beside the
		// byte and a space after a colon.
		factor = fmt.Sprintf("3 + |%s| + %d * |%s|", vars[1].Name(), walk.indentDepth(), vars[2].Name())
	}
	view := newFuncInfo(types.NewFunc(call.Pos(), v.pass.Pkg, fn.obj.Name(), types.NewSignatureType(nil, nil, nil, types.NewTuple(vars...), nil, false)))
	pre := &specEnv{v: v, sink: st, fn: view, args: bound, now: st.mem}
	var goals []*logic.Term
	for _, text := range walk.clauses(factor) {
		node, err := logic.ParseFormula(text)
		if err != nil {
			panic(fmt.Sprintf("vego: internal error: the bound of encoding %s cannot be read: %v: %s", types.ExprString(arg), err, text))
		}
		c := &clause{kind: "requires", text: text, node: node, pos: call.Pos(), res: v.pkgVerifier.plain}
		// encoding/json reads the value once the arguments are evaluated,
		// as fmt reads what it formats.
		v.quietly(func() { goals = append(goals, v.formula(c, node, pre)) })
	}
	goal := logic.And(goals...)
	done := v.at(call.Pos())
	result := v.attempt(st, guard, goal)
	done()
	if result != solver.Proved {
		v.report(call.Pos(), "what %s builds from %s may be more than can be allocated%s%s", fn.obj.Name(), types.ExprString(arg),
			v.encodeHint(st, guard, walk, arg, factor, pre), limitNote(result))
	}
	st.assume(logic.Implies(logic.And(guard...), goal))
}

// encodeHint says what bound on each length the walk counts is enough on
// this platform: the largest power of ten such that, with every length at
// most that, every group fits, written in the names of the caller when the
// value is a parameter or a field of one.
func (v *fnVerifier) encodeHint(st *state, guard []*logic.Term, walk *jsonWalk, arg ast.Expr, factor string, pre *specEnv) string {
	room := jsonRoom(v.maxAlloc(), v.pass.TypesSizes)
	// With the prefix and the indent at the bound too, for MarshalIndent.
	fits := func(n *big.Int) bool {
		if factor == "" {
			return walk.fitsWith(n, room, nil)
		}
		return walk.fitsWith(n, room, new(big.Int).Add(big.NewInt(3), new(big.Int).Mul(big.NewInt(walk.indentDepth()+1), n)))
	}
	n := new(big.Int).Exp(big.NewInt(10), big.NewInt(15), nil)
	for n.Cmp(big.NewInt(1)) > 0 && !fits(n) {
		n.Div(n, big.NewInt(10))
	}
	if !fits(n) {
		return "; it cannot fit on this platform"
	}
	name := types.ExprString(arg)
	// The lengths of each group, and the length of the container of each
	// group under it, at the level where they can be named.
	bounds := make([][]string, len(walk.groups))
	for i, g := range walk.groups {
		for _, t := range g.terms {
			bounds[i] = append(bounds[i], fmt.Sprintf("|%s| <= %s", t.path, n))
		}
		if last := len(g.steps) - 1; last >= 0 && g.steps[last].length != "" {
			for p, parent := range walk.groups {
				if len(parent.steps) == last && slices.Equal(parent.steps, g.steps[:last]) {
					bounds[p] = append(bounds[p], fmt.Sprintf("%s <= %s", g.steps[last].length, n))
				}
			}
		}
	}
	// One nested clause: what each group bounds, with the clause of
	// each group under it inside its quantifier or guard. Z3 proves the
	// bound from it where separate quantified clauses over one slice run
	// to the limit.
	var render func(i int) string
	render = func(i int) string {
		parts := slices.Clone(bounds[i])
		g := walk.groups[i]
		for c, child := range walk.groups {
			if len(child.steps) != len(g.steps)+1 || !slices.Equal(child.steps[:len(g.steps)], g.steps) {
				continue
			}
			inner := render(c)
			if inner == "" {
				continue
			}
			step := child.steps[len(g.steps)]
			if step.guard != "" {
				parts = append(parts, "("+step.guard+" -> "+inner+")")
			} else {
				parts = append(parts, "(Forall "+step.binder+" : "+inner+")")
			}
		}
		return strings.Join(parts, " And ")
	}
	var clauses []string
	if text := render(0); text != "" {
		// Leave it out when the facts here prove it already.
		proved := false
		if node, err := logic.ParseFormula(text); err == nil {
			var term *logic.Term
			v.quietly(func() {
				term, err = v.resolverOf(&clause{text: text, node: node, res: v.pkgVerifier.plain}).Formula(node, pre)
			})
			proved = err == nil && v.quickly(st, guard, term)
		}
		if !proved {
			clauses = append(clauses, renameJSONRoot(text, name))
		}
	}
	if factor != "" {
		clauses = append(clauses, fmt.Sprintf("|prefix| <= %s And |indent| <= %s", n, n))
	}
	if len(clauses) == 0 {
		return "; bound the lengths of the strings, slices, and maps it encodes"
	}
	if v.fromParameter(arg) {
		return "; bound what it encodes, as in // @Requires " + strings.Join(clauses, " And ")
	}
	return "; it fits when " + strings.Join(clauses, " and ") + ", so check the lengths before the call, or bound them in an invariant of the type"
}

// indentDepth is the deepest nesting MarshalIndent may indent.
func (w *jsonWalk) indentDepth() int64 {
	if w.raw {
		return jsonDepthLimit
	}
	return int64(w.depth)
}

// fitsWith reports whether every group fits in room with every length the
// walk counts at most n, given what each byte becomes under
// MarshalIndent, or nil for Marshal.
func (w *jsonWalk) fitsWith(n, room, factor *big.Int) bool {
	groups := big.NewInt(int64(len(w.groups)))
	for _, g := range w.groups {
		built := new(big.Int).Set(groups)
		for _, s := range g.steps {
			if s.length != "" {
				built.Mul(built, n)
			}
		}
		weight := big.NewInt(g.konst)
		for _, t := range g.terms {
			weight.Add(weight, new(big.Int).Mul(big.NewInt(t.coef), n))
		}
		built.Mul(built, weight)
		if factor != nil {
			built.Mul(built, factor)
		}
		if built.Cmp(room) > 0 {
			return false
		}
	}
	return true
}

// jsonRoom is what the generated clauses let a group build on a platform:
// the least of (MaxAlloc - 65536) / 3 and MaxInt / 5.
func jsonRoom(maxAlloc *big.Int, sizes types.Sizes) *big.Int {
	room := new(big.Int).Sub(maxAlloc, big.NewInt(1<<16))
	room.Div(room, big.NewInt(3))
	maxInt := new(big.Int).Lsh(big.NewInt(1), uint(8*sizes.Sizeof(types.Typ[types.Int])-1))
	maxInt.Sub(maxInt, big.NewInt(1)).Div(maxInt, big.NewInt(5))
	if maxInt.Cmp(room) < 0 {
		return maxInt
	}
	return room
}

// renameJSONRoot writes a generated formula over v in terms of the
// expression the call hands over.
func renameJSONRoot(text, name string) string {
	var b strings.Builder
	for i := 0; i < len(text); i++ {
		if text[i] == 'v' && (i == 0 || !isIdentByte(text[i-1]) && text[i-1] != '.') && (i+1 == len(text) || !isIdentByte(text[i+1])) {
			b.WriteString(name)
			continue
		}
		b.WriteByte(text[i])
	}
	return b.String()
}

func isIdentByte(c byte) bool {
	return c == '_' || c >= '0' && c <= '9' || c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z'
}

// The in-place encoder (F29, step 2). json.NewEncoder(w).Encode(v),
// written as one expression, makes an encoder that nothing else holds,
// and both builds of Encode marshal v as Marshal does, append a newline,
// and call w.Write once with that, before which nothing of w runs; on an
// error of marshalling they write nothing and return it. So the call is
// verified as the walk and the bound of Marshal, one byte more for the
// newline, followed by w's own Write of a new slice: the method that
// enc.w.Write dispatches to, called on the writer as it is written, with
// no interface value made and nothing kept. The error is Marshal's or
// what Write returned, of which nothing vouches for the second, so it is
// of unknown origin. Any other use of an Encoder or of NewEncoder is
// refused: an Encoder from elsewhere may indent, may not escape HTML, or
// hold an earlier error.

// jsonEncodeKey and jsonNewEncoderKey are the functions of the route.
const (
	jsonEncodeKey     = "(*encoding/json.Encoder).Encode"
	jsonNewEncoderKey = "encoding/json.NewEncoder"
)

// encoderInPlace returns, for a call json.NewEncoder(w).Encode(v) written
// as one expression, the expression w, and otherwise nil.
func (pv *pkgVerifier) encoderInPlace(call *ast.CallExpr) ast.Expr {
	sel, ok := ast.Unparen(call.Fun).(*ast.SelectorExpr)
	if !ok || sel.Sel.Name != "Encode" {
		return nil
	}
	if encode := typeutil.StaticCallee(pv.info, call); encode == nil || encode.FullName() != jsonEncodeKey {
		return nil
	}
	inner, ok := ast.Unparen(sel.X).(*ast.CallExpr)
	if !ok || len(inner.Args) != 1 {
		return nil
	}
	if made := typeutil.StaticCallee(pv.info, inner); made == nil || made.FullName() != jsonNewEncoderKey {
		return nil
	}
	return inner.Args[0]
}

// isEncoderInner reports whether a call is the json.NewEncoder(w) of a
// json.NewEncoder(w).Encode(v) written as one expression: the encoder it
// makes is handed only to that Encode, which calls only w.Write, so the
// call keeps nothing of w.
func (pv *pkgVerifier) isEncoderInner(call *ast.CallExpr) bool {
	if pv.encoderInners == nil {
		pv.encoderInners = map[*ast.CallExpr]bool{}
		for _, file := range pv.pass.Files {
			ast.Inspect(file, func(n ast.Node) bool {
				if outer, ok := n.(*ast.CallExpr); ok && pv.encoderInPlace(outer) != nil {
					pv.encoderInners[ast.Unparen(ast.Unparen(outer.Fun).(*ast.SelectorExpr).X).(*ast.CallExpr)] = true
				}
				return true
			})
		}
	}
	return pv.encoderInners[call]
}

// jsonEncoderUse is the message for any other use of NewEncoder or of an
// Encoder, or "" for a function that is neither.
func jsonEncoderUse(callee *types.Func) string {
	switch callee.FullName() {
	case jsonNewEncoderKey:
		return "json.NewEncoder keeps w in the encoder it returns; write json.NewEncoder(w).Encode(v) in one expression, since an encoder held in a variable is not supported yet"
	case jsonEncodeKey:
		return "Encode is verified only on a new encoder, written as json.NewEncoder(w).Encode(v) in one expression: an Encoder made elsewhere may indent, may not escape HTML, or may hold an earlier error"
	}
	return ""
}

// callEncoder verifies json.NewEncoder(w).Encode(v) written as one
// expression; see encoderInPlace.
func (v *fnVerifier) callEncoder(call *ast.CallExpr, w ast.Expr, st *state, guard []*logic.Term) []value {
	encode := typeutil.StaticCallee(v.info, call)
	fn := v.contractOf(encode)
	if fn == nil || fn.encoded == nil {
		v.unsupported(call.Pos(), "json.NewEncoder(w).Encode(v) needs the entry of (*encoding/json.Encoder).Encode that comes with vego, which lists encodes")
	}
	fn = v.usable(call.Pos(), fn, encode.Name(), st, guard, true)
	v.noteUse(fn, call.Pos())
	v.checkEncodable(call, fn)
	// The writer's own Write: through the interface it is written as, or
	// the method of its concrete type.
	wt := v.info.TypeOf(w)
	obj, _, _ := types.LookupFieldOrMethod(wt, true, v.pass.Pkg, "Write")
	method, _ := obj.(*types.Func)
	if method == nil {
		v.unsupported(w.Pos(), fmt.Sprintf("%s has no method Write", types.ExprString(w)))
	}
	var write *funcInfo
	if isIface(wt) {
		write = v.methodContract(method)
	} else {
		write = v.contractOf(method)
	}
	if write == nil {
		v.unsupported(w.Pos(), fmt.Sprintf("json.NewEncoder(%s).Encode calls %s.Write, which has no contract", types.ExprString(w), types.ExprString(w)))
	}
	write = v.usable(call.Pos(), write, types.ExprString(w)+".Write", st, guard, true)
	if isIface(wt) {
		v.ifaceStatesOf(wt)
	}
	u := v.unit
	operands := u.pushCeiling()
	made := unitCall{name: encode.Name(), pos: call.Pos()}
	// The writer is evaluated as it is: Go converts it to io.Writer for
	// NewEncoder, and the call is verified without that interface value.
	inner := ast.Unparen(w)
	v.converting[inner]++
	writer := v.eval(w, st, guard)
	v.converting[inner]--
	args := map[*types.Var]value{}
	for _, b := range v.bindCall(call, encode.Type().(*types.Signature)) {
		args[b.param] = v.evalPassed(b, st, guard)
	}
	u.reach(operands)
	if isIface(wt) {
		// NewEncoder(nil).Encode panics at the Write.
		v.check(st, guard, logic.Ne(writer[0], logic.RefLit(0)), call.Pos(), "the writer %s handed to json.NewEncoder may be nil", types.ExprString(w))
	}
	v.checkEncodedAlloc(st, guard, call, fn, args, v.held, 1)
	// A new slice of what Encode writes, whose length nothing bounds but
	// the bound proved above, which is not a term.
	writeSig := write.obj.Type().(*types.Signature)
	p := writeSig.Params().At(0)
	bytes := v.copiedBytes(st, v.fresh("encoded", logic.IntSeq), p.Type())
	writeArgs := map[*types.Var]value{p: bytes}
	if write.receiver != nil {
		writeArgs[write.receiver] = writer
	} else if recv := writeSig.Recv(); recv != nil {
		writeArgs[recv] = writer
	}
	pre := &specEnv{v: v, sink: st, fn: write, args: writeArgs, now: st.mem}
	var needs []*logic.Term
	v.quietly(func() {
		for _, c := range write.requires {
			needs = append(needs, v.formula(c, c.node, pre))
		}
	})
	if v.attempt(st, guard, logic.And(needs...)) != solver.Proved {
		v.report(call.Pos(), "json.NewEncoder(%s).Encode writes to %s JSON whose length is not a term the logic has, and the Write of %s needs a bound on what it is given; "+
			"encode with json.Marshal and write what it returns", types.ExprString(w), types.ExprString(w), types.TypeString(wt, types.RelativeTo(v.pass.Pkg)))
		v.cut(st, guard)
		return v.nothingKnown(encode, st)
	}
	shown := &ast.Ident{NamePos: call.Lparen, Name: "[]byte(json.Marshal(...) + \"\\n\")"}
	writeCall := &ast.CallExpr{Fun: &ast.SelectorExpr{X: w, Sel: &ast.Ident{NamePos: call.Lparen, Name: "Write"}}, Lparen: call.Lparen, Args: []ast.Expr{shown}, Rparen: call.Rparen}
	if write.trust != nil {
		v.noteUse(write, call.Pos())
	}
	v.invoke(writeCall, write, writeArgs, st, guard)
	// The error is Marshal's or what Write returned: the result of Encode's
	// own entry, applied to the new encoder, which nothing else holds, so
	// that a call nothing predicts decides it.
	// What it writes of the encoder, the one thing its frame lists, is
	// memory nothing else holds, so the frame is left out here.
	args[fn.params[0]] = value{v.alloc(st, true), logic.IntLit(0)}
	result := *fn
	result.modifies = nil
	results := v.invoke(call, &result, args, st, guard)
	u.calls = append(u.calls, made)
	u.event()
	return results
}
