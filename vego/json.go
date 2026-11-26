package vego

import (
	"fmt"
	"go/ast"
	"go/types"
	"math/big"
	"reflect"
	"slices"
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
// encoding/json runs, and runs them only while the call
// lasts, on the calling goroutine; it keeps nothing of the value; and what
// it allocates is within the bound that vego proves at each call. In place
// of runs, the static type of what each call hands it is walked
// (jsonPlainReason), and what it builds is bounded where the call stands
// from a bound on each length the type holds (checkEncodedAlloc, total).
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
	// stringKeys is set on the step of a map whose keys are strings.
	stringKeys bool
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

// mapValueReason says why the bound of encoding a type cannot be proved,
// or returns "": a length under a quantifier over the elements of a slice
// or a map that is itself the value of a map with string keys. When the
// facts bound the length of the keys, vego does not prove such a bound
// even from the same fact, as `Forall k in m : (Forall i in [0, |m[k]|) :
// |m[k][i]| <= 10000000)` from the same with 1000 and a bound on |k| (Z3
// runs to its limit, also with the bound on the keys in a clause of its
// own), so encoding it is refused before it becomes an obligation nobody
// can meet. A map with integer keys has no such bound, and proves.
// Decoding counts no length, and is not refused.
func (w *jsonWalk) mapValueReason() string {
	for _, l := range w.lengths() {
		underMap := ""
		for _, s := range l.steps {
			switch {
			case s.binder == "":
			case underMap != "":
				return fmt.Sprintf("%s holds elements inside the value of %s, a map with string keys, and vego cannot yet bound what they hold under a quantifier "+
					"over the keys; encode a map whose values hold no slice or map with elements of unknown length, or a map with integer keys", s.length[1:len(s.length)-1], underMap)
			case s.stringKeys:
				underMap = s.length[1 : len(s.length)-1]
			}
		}
	}
	return ""
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
		c := w.child(g, jsonStep{binder: fmt.Sprintf("%s in %s", k, path), length: "|" + path + "|", stringKeys: key.Kind() == types.String})
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
		return fmt.Sprintf("%s is an interface value of type %s, whose dynamic type vego does not know; use a value of a concrete type", shown, w.shown(t))
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

// A jsonLength is a length the bound counts: the length of a container on
// a chain, or one a term weighs, with the steps of the chain it lies under,
// whose quantifiers and guards it is read inside.
type jsonLength struct {
	steps []jsonStep
	text  string // "|v.Tags|", "|v.Tags[i]|", "|k|", or "|prefix|"
}

// key names a length uniquely in a walk.
func (l jsonLength) key() string {
	var b strings.Builder
	for _, s := range l.steps {
		b.WriteString(s.binder + s.guard + ";")
	}
	return b.String() + l.text
}

// lengths returns every length the bound counts, each once, in the order
// of the groups.
func (w *jsonWalk) lengths() []jsonLength {
	var found []jsonLength
	seen := map[string]bool{}
	add := func(l jsonLength) {
		if !seen[l.key()] {
			seen[l.key()] = true
			found = append(found, l)
		}
	}
	for _, g := range w.groups {
		for i, s := range g.steps {
			if s.length != "" {
				add(jsonLength{steps: slices.Clip(g.steps[:i]), text: s.length})
			}
		}
		for _, t := range g.terms {
			add(jsonLength{steps: g.steps, text: "|" + t.path + "|"})
		}
	}
	return found
}

// jsonAlgebra is what jsonFold computes in: numbers, for the bound a call
// is proved against, or terms of the logic, for what is stated of the
// result. length gives a length's value, or false when it has none.
type jsonAlgebra[T any] struct {
	num      func(n *big.Int) T
	length   func(l jsonLength) (T, bool)
	add, mul func(a, b T) T
}

// jsonFold is what encoding builds at most when every length is at most
// what the algebra gives for it: for each group, the product of the
// lengths of its chain, which bounds how many times the group occurs,
// times the most one occurrence weighs, summed over the groups, and for
// MarshalIndent times what each byte becomes, 3 + |prefix| + depth *
// |indent|. It is the one place the weights are combined: total and the
// term stated of the result are this fold (F23 of the review of step 1).
func jsonFold[T any](w *jsonWalk, a jsonAlgebra[T], indented bool) (T, bool) {
	var zero T
	sum := a.num(big.NewInt(0))
	for _, g := range w.groups {
		count := a.num(big.NewInt(1))
		for i, s := range g.steps {
			if s.length == "" {
				continue
			}
			b, ok := a.length(jsonLength{steps: g.steps[:i], text: s.length})
			if !ok {
				return zero, false
			}
			count = a.mul(count, b)
		}
		weight := a.num(big.NewInt(g.konst))
		for _, t := range g.terms {
			b, ok := a.length(jsonLength{steps: g.steps, text: "|" + t.path + "|"})
			if !ok {
				return zero, false
			}
			weight = a.add(weight, a.mul(a.num(big.NewInt(t.coef)), b))
		}
		sum = a.add(sum, a.mul(count, weight))
	}
	if indented {
		prefix, okPrefix := a.length(jsonLength{text: "|prefix|"})
		indent, okIndent := a.length(jsonLength{text: "|indent|"})
		if !okPrefix || !okIndent {
			return zero, false
		}
		// The deepest nesting MarshalIndent may indent: that of the type,
		// or the limit of every build under a json.RawMessage.
		depth := int64(w.depth)
		if w.raw {
			depth = jsonDepthLimit
		}
		factor := a.add(a.add(a.num(big.NewInt(3)), prefix), a.mul(a.num(big.NewInt(depth)), indent))
		sum = a.mul(sum, factor)
	}
	return sum, true
}

// total is jsonFold over numbers: what encoding builds at most when every
// length is at most what bound gives for it, or nil when bound is nil for
// a length. It is what vego proves a call against (checkEncodedAlloc) and
// what TestJSONEntries and TestEncoding386 hold against the real encoders.
func (w *jsonWalk) total(bound func(jsonLength) *big.Int, indented bool) *big.Int {
	sum, ok := jsonFold(w, jsonAlgebra[*big.Int]{
		num: func(n *big.Int) *big.Int { return n },
		length: func(l jsonLength) (*big.Int, bool) {
			b := bound(l)
			return b, b != nil
		},
		add: func(a, b *big.Int) *big.Int { return new(big.Int).Add(a, b) },
		mul: func(a, b *big.Int) *big.Int { return new(big.Int).Mul(a, b) },
	}, indented)
	if !ok {
		return nil
	}
	return sum
}

// jsonFits reports whether what encoding builds, at most total bytes,
// can be allocated: three times and a page within MaxAlloc, five times
// within MaxInt, the factors of a bytes.Buffer that grows (v1) and of a
// slice grown by append (v2) with the rounding of growslice.
func jsonFits(total, maxAlloc *big.Int, sizes types.Sizes) bool {
	room := new(big.Int).Mul(total, big.NewInt(3))
	room.Add(room, big.NewInt(1<<16))
	maxInt := new(big.Int).Lsh(big.NewInt(1), uint(8*sizes.Sizeof(types.Typ[types.Int])-1))
	maxInt.Sub(maxInt, big.NewInt(1))
	return room.Cmp(maxAlloc) <= 0 && new(big.Int).Mul(total, big.NewInt(5)).Cmp(maxInt) <= 0
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
	why, walk := jsonPlainReason(v.pass.Pkg, v.pass.TypesSizes, v.info.TypeOf(arg), types.ExprString(arg))
	// A map with string keys whose values hold elements is refused only
	// because the walk cannot state its bound, which the declared memory
	// does not ask for (F25 of the review of step 3 of F38).
	if why == "" && !v.encodesDeclared() {
		why = walk.mapValueReason()
	}
	if why != "" {
		v.unsupported(arg.Pos(), fmt.Sprintf("%s encodes %s, and %s", fn.obj.Name(), types.ExprString(arg), why))
	}
}

// jsonEntryAlloc is what encoding allocates at once for each entry of a
// map whose keys it sorts, at most: v2's member of 80 bytes and the key and
// the value, whose entries the declared memory bounds together; the test
// of the largest allocation reads it.
const jsonEntryAlloc = 81

// encodesDeclared reports whether a declared memory makes every encoding
// call fit, whatever it builds: encoding grows its output step by step, and
// each allocation it makes is at most three times what exists, the output
// so far or one value that what it encodes holds, 81 bytes for each entry
// of a map whose keys it sorts, and 2^20 for the stacks of its states (read
// in the four builds, and held by TestJSONEntries; see Sizes under a
// declared memory in the ROADMAP). Every array that exists is within R and
// a map has at most M entries, so that holds when 3 * R + 81 * M + 2^20
// fits one allocation.
func (v *fnVerifier) encodesDeclared() bool {
	decl := v.sizesOf()
	if decl == nil {
		return false
	}
	request := new(big.Int).Mul(decl.arrayBound(), big.NewInt(3))
	request.Add(request, new(big.Int).Mul(decl.memory, big.NewInt(jsonEntryAlloc)))
	return request.Add(request, big.NewInt(1<<20)).Cmp(v.maxAlloc()) <= 0
}

// checkEncodedAlloc proves, at a call of a function whose entry lists
// encodes, that what it builds from the value can be allocated. Each length
// the walk counts for the static type of what the call hands over is
// bounded from the facts here, read with the parameter bound to the value
// as it was before its conversion to any: a power of ten that Z3 proves
// (lengthBounds), as a formula with no product. Then total multiplies and adds those bounds, and jsonFits
// compares the result with what can be allocated. A product of lengths
// under quantifiers ran Z3 to its limit on ordinary shapes, such as a map
// of slices (F15 of the review of step 1). extra is what the function
// builds beyond what Marshal builds, as Encode's newline. It returns a
// bound on what is built, or nil when none was proved: for Marshal, the
// part that lies under no chain and no guard as the sum of its lengths
// with their weights, exact in the terms the caller has, and the rest as
// the number total gives for the bounds proved; for MarshalIndent that
// number.
func (v *fnVerifier) checkEncodedAlloc(st *state, guard []*logic.Term, call *ast.CallExpr, fn *funcInfo, args map[*types.Var]value, held map[ast.Expr]value, extra int64) *logic.Term {
	arg := v.encodedArg(call, fn)
	if arg == nil {
		return nil
	}
	t := v.info.TypeOf(arg)
	why, walk := jsonPlainReason(v.pass.Pkg, v.pass.TypesSizes, t, "v")
	if why != "" {
		// Refused before the arguments were evaluated.
		return nil
	}
	if walk.mapValueReason() != "" {
		// Refused before the arguments were evaluated, or accepted under
		// a declared memory with no bound, which the walk cannot state.
		if v.encodesDeclared() && v.sizedProved != nil {
			v.sizedProved.Add(1)
		}
		return nil
	}
	walk.groups[0].konst += extra
	val := held[ast.Unparen(arg)]
	if val == nil {
		panic(fmt.Sprintf("vego: internal error: the value %s handed to %s was not kept as it was before its conversion", types.ExprString(arg), fn.obj.Name()))
	}
	// A contract of one parameter, v, of the static type, and the string
	// parameters MarshalIndent reads, prefix and indent.
	vars := []*types.Var{types.NewParam(arg.Pos(), v.pass.Pkg, "v", t)}
	bound := map[*types.Var]value{vars[0]: val}
	indented := false
	for _, b := range v.bindCall(call, fn.obj.Type().(*types.Signature)) {
		if b.param != fn.encoded && b.expr != nil && isString(b.param.Type()) {
			p := types.NewParam(b.expr.Pos(), v.pass.Pkg, b.param.Name(), b.param.Type())
			vars = append(vars, p)
			bound[p] = args[b.param]
			indented = true
		}
	}
	view := newFuncInfo(types.NewFunc(call.Pos(), v.pass.Pkg, fn.obj.Name(), types.NewSignatureType(nil, nil, nil, types.NewTuple(vars...), nil, false)))
	pre := &specEnv{v: v, sink: st, fn: view, args: bound, now: st.mem}
	lengths := walk.lengths()
	if indented {
		lengths = append(lengths, jsonLength{text: "|prefix|"}, jsonLength{text: "|indent|"})
	}
	done := v.at(call.Pos())
	found := v.lengthBounds(st, guard, walk, lengths, indented, pre)
	done()
	total := walk.total(func(l jsonLength) *big.Int { return found[l.key()] }, indented)
	if total != nil && jsonFits(total, v.maxAlloc(), v.pass.TypesSizes) {
		if indented {
			return logic.BigLit(total)
		}
		// The same fold over terms: a length under no quantifier and no
		// guard is the caller's own, and any other is its bound proved.
		// Each product is a term times numbers.
		term, _ := jsonFold(walk, jsonAlgebra[*logic.Term]{
			num: logic.BigLit,
			length: func(l jsonLength) (*logic.Term, bool) {
				if len(l.steps) > 0 {
					return logic.BigLit(found[l.key()]), true
				}
				node, err := logic.ParseFormula(l.text + " >= 0")
				if err != nil {
					panic("vego: internal error: " + err.Error())
				}
				c := &clause{kind: "requires", text: l.text, node: node, res: v.pkgVerifier.plain}
				var length *logic.Term
				v.quietly(func() { length, err = v.resolverOf(c).Term(node.Kids[0], pre, logic.Int) })
				if err != nil {
					panic("vego: internal error: " + err.Error())
				}
				return length, true
			},
			add: logic.Add,
			mul: logic.Mul,
		}, false)
		return term
	}
	// Under a declared memory what it builds fits whatever its total, of
	// which nothing is known then (encodesDeclared).
	if v.encodesDeclared() {
		if v.sizedProved != nil {
			v.sizedProved.Add(1)
		}
		return nil
	}
	v.report(call.Pos(), "what %s builds from %s may be more than can be allocated%s", fn.obj.Name(), types.ExprString(arg),
		v.encodeHint(walk, arg, indented, found))
	return nil
}

// lengthBounds returns, for each length the bound counts, a bound that
// the facts prove, under the quantifiers and guards of its chain, keyed by
// the length. A question is linear, a length at most a number, but one
// under two quantifiers takes Z3 about a million units, past the quick
// budget, so the questions are few. First, one question: every length at
// most n0, the largest power of ten at which what is built fits when every
// length is at most it, which is the bound the message suggests. When that
// fails, each length alone: at most n0 at the full limit, then lowered by
// powers of ten while the quick budget proves it; or, not proved at n0,
// raised by powers of ten until the quick budget proves it. After the
// first question, each bound is lowered the same way. A length with no
// bound proved is left out.
func (v *fnVerifier) lengthBounds(st *state, guard []*logic.Term, walk *jsonWalk, lengths []jsonLength, indented bool, pre *specEnv) map[string]*big.Int {
	goalOf := func(l jsonLength, n *big.Int) *logic.Term {
		text := walk.wrap(l.steps, l.text+" <= "+n.String())
		node, err := logic.ParseFormula(text)
		if err != nil {
			panic(fmt.Sprintf("vego: internal error: a bound of encoding cannot be read: %v: %s", err, text))
		}
		c := &clause{kind: "requires", text: text, node: node, res: v.pkgVerifier.plain}
		var goal *logic.Term
		// encoding/json reads the value once the arguments are
		// evaluated, as fmt reads what it formats.
		v.quietly(func() { goal = v.formula(c, node, pre) })
		return goal
	}
	full := func(goal *logic.Term) bool { return v.attempt(st, guard, goal) == solver.Proved }
	ten := big.NewInt(10)
	top := new(big.Int).Exp(ten, big.NewInt(jsonMaxExponent), nil)
	n0 := new(big.Int).Set(top)
	uniform := func(n *big.Int) bool {
		return jsonFits(walk.total(func(jsonLength) *big.Int { return n }, indented), v.maxAlloc(), v.pass.TypesSizes)
	}
	for n0.Cmp(big.NewInt(1)) > 0 && !uniform(n0) {
		n0.Div(n0, ten)
	}
	found := map[string]*big.Int{}
	var all []*logic.Term
	for _, l := range lengths {
		all = append(all, goalOf(l, n0))
	}
	// A bound proved at n0 is lowered while the quick budget proves it,
	// so that what is stated of the result comes from the facts the
	// caller has, not from the loosest bound that fits (F21 of the review
	// of step 1).
	lower := func(l jsonLength, b *big.Int) *big.Int {
		for b.Cmp(big.NewInt(1)) > 0 {
			lower := new(big.Int).Div(b, ten)
			if !v.quickly(st, guard, goalOf(l, lower)) {
				break
			}
			b = lower
		}
		return b
	}
	if uniform(n0) && full(logic.And(all...)) {
		for _, l := range lengths {
			found[l.key()] = lower(l, new(big.Int).Set(n0))
		}
		return found
	}
	for i, l := range lengths {
		if full(all[i]) {
			found[l.key()] = lower(l, new(big.Int).Set(n0))
			continue
		}
		// Not proved at n0: raised until the quick budget proves it. A
		// length past n0 that only the full limit proves leaves what is
		// built past what fits whatever else is bounded.
		for b := new(big.Int).Mul(n0, ten); b.Cmp(top) <= 0; b.Mul(b, ten) {
			if v.quickly(st, guard, goalOf(l, b)) {
				found[l.key()] = new(big.Int).Set(b)
				break
			}
		}
	}
	return found
}

// jsonMaxExponent is the largest power of ten a length is bounded by.
const jsonMaxExponent = 15

// encodeHint says what bound on each length the walk counts is enough on
// this platform: the largest power of ten such that, with every length at
// most that, what is built fits. It names only the lengths whose proved
// bound is larger or missing (F16), in one nested clause, in the names of
// the caller when the value is a parameter or a field of one.
func (v *fnVerifier) encodeHint(walk *jsonWalk, arg ast.Expr, indented bool, found map[string]*big.Int) string {
	n := new(big.Int).Exp(big.NewInt(10), big.NewInt(jsonMaxExponent), nil)
	fits := func(n *big.Int) bool {
		t := walk.total(func(l jsonLength) *big.Int {
			if b := found[l.key()]; b != nil && b.Cmp(n) < 0 {
				return b
			}
			return n
		}, indented)
		return jsonFits(t, v.maxAlloc(), v.pass.TypesSizes)
	}
	for n.Cmp(big.NewInt(1)) > 0 && !fits(n) {
		n.Div(n, big.NewInt(10))
	}
	if !fits(n) {
		return "; it cannot fit on this platform"
	}
	needs := func(l jsonLength) bool {
		b := found[l.key()]
		return b == nil || b.Cmp(n) > 0
	}
	// The lengths each group names, and the length of the container of
	// each group under it, at the level where they can be named.
	bounds := make([][]string, len(walk.groups))
	for i, g := range walk.groups {
		for _, t := range g.terms {
			if l := (jsonLength{steps: g.steps, text: "|" + t.path + "|"}); needs(l) {
				bounds[i] = append(bounds[i], fmt.Sprintf("%s <= %s", l.text, n))
			}
		}
		if last := len(g.steps) - 1; last >= 0 && g.steps[last].length != "" && needs(jsonLength{steps: g.steps[:last], text: g.steps[last].length}) {
			for p, parent := range walk.groups {
				if len(parent.steps) == last && slices.Equal(parent.steps, g.steps[:last]) {
					bounds[p] = append(bounds[p], fmt.Sprintf("%s <= %s", g.steps[last].length, n))
				}
			}
		}
	}
	// One nested clause: what each group bounds, with the clause of each
	// group under it inside its quantifier or guard.
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
		clauses = append(clauses, renameJSONRoot(text, types.ExprString(arg)))
	}
	for _, name := range []string{"prefix", "indent"} {
		if l := (jsonLength{text: "|" + name + "|"}); indented && needs(l) {
			clauses = append(clauses, fmt.Sprintf("|%s| <= %s", name, n))
		}
	}
	if len(clauses) == 0 {
		// Every bound that is enough holds, and Z3 did not prove one of
		// them within its limit.
		return "; each length it encodes is bounded enough, as " + n.String() + " would be, but a bound was not proved within the limit; -vego.rlimit raises it"
	}
	if v.fromParameter(arg) {
		return "; bound what it encodes, as in // @Requires " + strings.Join(clauses, " And ")
	}
	return "; it fits when " + strings.Join(clauses, " and ") + ", so check the lengths before the call, or bound them in an invariant of the type"
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

// routeMethod returns the contract of the method name that a call through
// the io.Writer or io.Reader made of e would run, chosen as a conversion
// chooses it (concreteMethod): a method promoted from an embedded field is
// refused with the conversion's message. receiverOf turns the value of e
// into the receiver the method is called with: for a value receiver
// reached through a pointer, the struct read after a proof that the
// pointer is not nil, where Go panics (F24 of the review of step 2).
func (v *fnVerifier) routeMethod(call *ast.CallExpr, e ast.Expr, name, maker string, st *state, guard []*logic.Term) (*funcInfo, func(value) value) {
	t := v.info.TypeOf(e)
	same := func(val value) value { return val }
	if isIface(t) {
		selection := types.NewMethodSet(t).Lookup(nil, name)
		if selection == nil {
			v.unsupported(e.Pos(), fmt.Sprintf("%s has no method %s", types.ExprString(e), name))
		}
		method := selection.Obj().(*types.Func)
		fn := v.methodContract(method)
		if fn == nil {
			v.unsupported(e.Pos(), fmt.Sprintf("%s calls %s.%s, which has no contract", maker, types.ExprString(e), name))
		}
		fn = v.usable(call.Pos(), fn, types.ExprString(e)+"."+name, st, guard, true)
		v.ifaceStatesOf(t)
		return fn, same
	}
	concrete, why := concreteMethod(t, nil, name, v.pass.Pkg)
	if why != "" {
		v.unsupported(e.Pos(), why)
	}
	fn := v.contractOf(concrete)
	if fn == nil {
		v.unsupported(e.Pos(), fmt.Sprintf("%s calls %s.%s, which has no contract", maker, types.ExprString(e), name))
	}
	fn = v.usable(call.Pos(), fn, types.ExprString(e)+"."+name, st, guard, true)
	_, fromPointer := t.Underlying().(*types.Pointer)
	_, recvPointer := concrete.Type().(*types.Signature).Recv().Type().(*types.Pointer)
	if !fromPointer || recvPointer {
		return fn, same
	}
	return fn, func(held value) value {
		// Go reads what the pointer points to when the method runs, and
		// panics if it is nil.
		v.check(st, guard, logic.Ne(held[0], logic.RefLit(0)), call.Pos(),
			"%s has a value receiver, and the pointer %s handed to %s may be nil", methodOf(concrete.Type().(*types.Signature).Recv().Type(), concrete, v.pass.Pkg), types.ExprString(e), maker)
		object := t.Underlying().(*types.Pointer).Elem()
		var read value
		v.quietly(func() {
			read = v.fetch(st, st.mem, v.cellsOf(object), held[0], held[1])
			v.noteTyped(st, read, object)
		})
		return read
	}
}

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
				// The NewDecoder and the LimitReader of the in-place
				// decoder too: the decoder and the limited reader live for
				// the expression (jsondecode.go).
				if outer, ok := n.(*ast.CallExpr); ok {
					if made, limit, limited := pv.decoderInPlace(outer); limited {
						pv.encoderInners[made] = true
						pv.encoderInners[limit] = true
					}
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
	write, receiverOf := v.routeMethod(call, w, "Write", "json.NewEncoder", st, guard)
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
	encoded := v.checkEncodedAlloc(st, guard, call, fn, args, v.held, 1)
	// A new slice of what Encode writes, no longer than what it builds.
	writeSig := write.obj.Type().(*types.Signature)
	p := writeSig.Params().At(0)
	text := v.fresh("encoded", logic.IntSeq)
	if encoded != nil {
		st.assume(logic.Implies(logic.And(guard...), logic.Le(logic.Len(text), encoded)))
	}
	bytes := v.copiedBytes(st, text, p.Type())
	writeArgs := map[*types.Var]value{p: bytes}
	if write.receiver != nil {
		writeArgs[write.receiver] = writer
	} else if recv := writeSig.Recv(); recv != nil {
		writeArgs[recv] = receiverOf(writer)
	}
	pre := &specEnv{v: v, sink: st, fn: write, args: writeArgs, now: st.mem}
	var needs []*logic.Term
	v.quietly(func() {
		for _, c := range write.requires {
			needs = append(needs, v.formula(c, c.node, pre))
		}
	})
	if v.attempt(st, guard, logic.And(needs...)) != solver.Proved {
		if encoded == nil {
			// What it encodes was reported as not bounded.
			v.cut(st, guard)
			return v.nothingKnown(encode, st)
		}
		v.report(call.Pos(), "precondition of %s.Write may not hold where json.NewEncoder(%s).Encode writes what it encodes; bound the lengths of what it encodes more tightly",
			types.ExprString(w), types.ExprString(w))
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
