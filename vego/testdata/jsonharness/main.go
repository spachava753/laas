// Command jsonharness runs the entries of encoding/json that vego ships
// against the build of encoding/json it is built with, for
// TestJSONEntries: the test walks the types declared here as vego does,
// hands the groups of the bound to this program on standard input, and
// reads what it found on standard output. It is built once for each build
// of encoding/json the test covers (with and without GOEXPERIMENT=jsonv2,
// and with Go 1.26 under VEGO_GO126=1), so that every claim is held
// against each.
package main

import (
	"encoding/json"
	"fmt"
	"math"
	"math/rand/v2"
	"os"
	"reflect"
	"sort"
	"strings"
	"sync/atomic"
	"time"
	"unsafe"
)

// Input is what the test hands over.
type Input struct {
	Seed    uint64
	Samples int
	Cases   []Case
}

// Case is one type with the bound vego generates for it.
type Case struct {
	Type   string
	Groups []Group
	Depth  int
	Raw    bool
	// Want is set when the case must find a sample above the bound: the
	// groups were made with a weight one smaller.
	Want bool
}

// Group is a group of the bound; see json.go.
type Group struct {
	Steps []Step
	Konst int64
	Terms []Term
}

// Step is a quantifier or a guard of a group.
type Step struct{ Binder, Length, Guard string }

// Term is a length with its weight.
type Term struct {
	Coef int64
	Path string
}

// Output is what the program found.
type Output struct {
	// Build names the build of encoding/json.
	Build string
	// Failures holds what broke a claim.
	Failures []string
	// Above counts, for each case, the samples whose output passed the
	// sum of the bound.
	Above map[string]int
	// Called holds the methods of jsonMethods that the build called.
	Called []string
	// Errors holds the dynamic types of the errors in the trees of what
	// the entries returned.
	Errors []string
	// Samples counts what was run.
	Samples int
}

var out = Output{Above: map[string]int{}}

func fail(format string, args ...any) {
	if len(out.Failures) < 50 {
		out.Failures = append(out.Failures, fmt.Sprintf(format, args...))
	}
}

func main() {
	var in Input
	if err := json.NewDecoder(os.Stdin).Decode(&in); err != nil {
		panic(err)
	}
	out.Build = build()
	rng := rand.New(rand.NewPCG(in.Seed, 29))
	errTypes := map[string]bool{}
	for _, c := range in.Cases {
		t, ok := registry[c.Type]
		if !ok {
			fail("no type %s in the harness", c.Type)
			continue
		}
		for range in.Samples {
			v := reflect.New(t).Elem()
			worst = rng.IntN(2) == 0
			fill(rng, v, 0)
			out.Samples++
			sum := bound(c, v)
			calls.Store(0)
			for _, indent := range []struct{ prefix, indent string }{{}, {"", "  "}, {">", "\t\t\t"}, {"<<", ""}} {
				var b []byte
				var err error
				indented := indent.prefix != "" || indent.indent != ""
				if indented {
					b, err = json.MarshalIndent(v.Interface(), indent.prefix, indent.indent)
				} else {
					b, err = json.Marshal(v.Interface())
				}
				if err != nil {
					if b != nil {
						fail("%s: an error and a result that is not nil", c.Type)
					}
					treeTypes(err, errTypes)
					checkHeld(c.Type, err, v)
					continue
				}
				limit := sum
				if indented {
					depth := int64(c.Depth)
					if c.Raw {
						depth = 10000
					}
					limit = sum * (3 + int64(len(indent.prefix)) + depth*int64(len(indent.indent)))
				}
				if int64(len(b)) > limit {
					out.Above[c.Type]++
					if !c.Want {
						fail("%s: %d bytes above the bound %d (prefix %q, indent %q): %s", c.Type, len(b), limit, indent.prefix, indent.indent, clip(b))
					}
				}
			}
			if n := calls.Load(); n != 0 {
				fail("%s: encoding called %d methods it must not call", c.Type, n)
			}
		}
	}
	out.Called = calledMethods()
	for t := range errTypes {
		out.Errors = append(out.Errors, t)
	}
	sort.Strings(out.Errors)
	if err := json.NewEncoder(os.Stdout).Encode(out); err != nil {
		panic(err)
	}
}

func clip(b []byte) string {
	if len(b) > 200 {
		return string(b[:200]) + "..."
	}
	return string(b)
}

// treeTypes adds the dynamic type of each error in the tree of err.
func treeTypes(err error, into map[string]bool) {
	if err == nil {
		return
	}
	into[reflect.TypeOf(err).String()] = true
	switch e := err.(type) {
	case interface{ Unwrap() []error }:
		for _, inner := range e.Unwrap() {
			treeTypes(inner, into)
		}
	case interface{ Unwrap() error }:
		treeTypes(e.Unwrap(), into)
	}
}

// --- the bound, evaluated on the value ---

// bound is the sum, over the groups and over every element on their
// chains, of what each group counts: the sum that the clauses vego
// generates bound, group by group. It also checks, for each group, that
// this sum is no more than the largest product the clause of the group
// bounds, so that the step from the clauses to the sum is checked too.
func bound(c Case, v reflect.Value) int64 {
	var total int64
	for gi, g := range c.Groups {
		var sum, most int64
		env := map[string]reflect.Value{"v": v}
		var walk func(i int, product int64)
		walk = func(i int, product int64) {
			if i == len(g.Steps) {
				w := g.Konst
				for _, t := range g.Terms {
					w += t.Coef * int64(lengthOf(eval(t.Path, env)))
				}
				sum += w
				most = max(most, product*w)
				return
			}
			s := g.Steps[i]
			if s.Guard != "" {
				p := eval(strings.TrimSuffix(s.Guard, " != nil"), env)
				if !p.IsNil() {
					walk(i+1, product)
				}
				return
			}
			name, over, _ := strings.Cut(s.Binder, " in ")
			if strings.HasPrefix(over, "[0, |") {
				seq := eval(strings.TrimSuffix(strings.TrimPrefix(over, "[0, |"), "|)"), env)
				for k := range seq.Len() {
					env[name] = reflect.ValueOf(k)
					walk(i+1, product*int64(seq.Len()))
				}
			} else {
				m := eval(over, env)
				for _, k := range m.MapKeys() {
					env[name] = k
					walk(i+1, product*int64(m.Len()))
				}
			}
			delete(env, name)
		}
		walk(0, 1)
		if sum > most {
			fail("%s: group %d sums to %d, more than %d, the largest product its clause bounds", c.Type, gi, sum, most)
		}
		total += sum
	}
	return total
}

// lengthOf is |x| of a string, a slice, a map, or a key.
func lengthOf(v reflect.Value) int {
	return v.Len()
}

// eval reads a path of a generated formula, as v.A[i].B[k].
func eval(path string, env map[string]reflect.Value) reflect.Value {
	i := strings.IndexAny(path, ".[")
	root := path
	if i >= 0 {
		root = path[:i]
	}
	cur, ok := env[root]
	if !ok {
		panic("no binding of " + root + " in " + path)
	}
	rest := path[len(root):]
	for rest != "" {
		for cur.Kind() == reflect.Pointer {
			cur = cur.Elem()
		}
		if rest[0] == '.' {
			end := strings.IndexAny(rest[1:], ".[")
			name := rest[1:]
			if end >= 0 {
				name = rest[1 : end+1]
			}
			cur = cur.FieldByName(name)
			rest = rest[1+len(name):]
			continue
		}
		end := strings.IndexByte(rest, ']')
		key := env[rest[1:end]]
		if cur.Kind() == reflect.Map {
			cur = cur.MapIndex(key)
		} else {
			cur = cur.Index(int(key.Int()))
		}
		rest = rest[end+1:]
	}
	return cur
}

// --- values ---

// palette holds what strings are made of: control bytes, the bytes HTML
// escaping changes, U+2028, an invalid byte, a quote and a backslash, and
// plain letters.
var palette = []string{"\x00", "\x1f", "<", ">", "&", " ", " ", "\xff", "\"", "\\", "a", "é", "\t"}

// worst is set while a sample is made of the values that print longest,
// so that a weight one smaller shows.
var worst bool

var floats = []float64{-0.0000010041483654975866, 0, -0.0000012345678901234567, -1.2345678901234567e-308, -1.7976931348623157e+308, -999999999999999900000,
	-123456789012345680000, math.SmallestNonzeroFloat64, 1e21, 1e-7, math.NaN(), math.Inf(1), -5e-324, 0.1, -0.000001}

var floats32 = []float32{-183116110000000000000, 0, -0.0000012345678, -9.9999994e20, -3.4028235e+38, -1.1754944e-38, 1e-7, float32(math.Inf(-1)), -1.2345678e-6, -123456790000000000000}

var raws = []string{"", "null", "1", `"<<<<"`, `{"a":[1,2,{"b":" <>&"}]}`, `[[[[[[[[[[]]]]]]]]]]`, `{`, `"\xff"`, `  [ 1 , 2 ]  `, `"` + strings.Repeat("<", 40) + `"`}

var numbers = []string{"", "0", "-1.5e10", "12345678901234567890", "1.", "abc", "-0"}

var times = []time.Time{
	time.Date(2026, 11, 23, 23, 59, 59, 123456789, time.FixedZone("x", -7*3600-30*60)),
	time.Date(9999, 12, 31, 23, 59, 59, 999999999, time.FixedZone("y", -(23*3600+59*60))),
	time.Date(10000, 1, 1, 0, 0, 0, 0, time.UTC),
	time.Date(-1, 1, 1, 0, 0, 0, 0, time.UTC),
	{},
}

// settable gives a value that can be set even when it was reached through
// an unexported field.
func settable(v reflect.Value) reflect.Value {
	if v.CanSet() {
		return v
	}
	return reflect.NewAt(v.Type(), unsafe.Pointer(v.UnsafeAddr())).Elem()
}

var timeType = reflect.TypeFor[time.Time]()
var rawType = reflect.TypeFor[json.RawMessage]()
var numberType = reflect.TypeFor[json.Number]()

// fill gives v a random value of its type, nil and empty included.
func fill(rng *rand.Rand, v reflect.Value, depth int) {
	v = settable(v)
	switch v.Type() {
	case timeType:
		v.Set(reflect.ValueOf(times[rng.IntN(len(times))]))
		return
	case rawType:
		if r := raws[rng.IntN(len(raws))]; r != "" || rng.IntN(2) == 0 {
			v.SetBytes([]byte(r))
		}
		return
	case numberType:
		v.SetString(numbers[rng.IntN(len(numbers))])
		return
	}
	if worst {
		if fillWorst(rng, v, depth) {
			return
		}
	}
	switch v.Kind() {
	case reflect.Bool:
		v.SetBool(rng.IntN(2) == 0)
	case reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64:
		bits := v.Type().Bits()
		switch rng.IntN(3) {
		case 0:
			v.SetInt(-1 << (bits - 1))
		case 1:
			v.SetInt(1<<(bits-1) - 1)
		default:
			v.SetInt(rng.Int64N(1000) - 500)
		}
	case reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64, reflect.Uintptr:
		if rng.IntN(2) == 0 {
			v.SetUint(math.MaxUint64 >> (64 - v.Type().Bits()))
		} else {
			v.SetUint(rng.Uint64N(1000))
		}
	case reflect.Float64:
		v.SetFloat(floats[rng.IntN(len(floats))])
	case reflect.Float32:
		v.SetFloat(float64(floats32[rng.IntN(len(floats32))]))
	case reflect.String:
		var b strings.Builder
		for range rng.IntN(6) {
			b.WriteString(palette[rng.IntN(len(palette))])
		}
		v.SetString(b.String())
	case reflect.Slice:
		if rng.IntN(4) == 0 {
			return // nil
		}
		n := rng.IntN(4)
		if depth > 3 {
			n = min(n, 1)
		}
		s := reflect.MakeSlice(v.Type(), n, n)
		for i := range n {
			fill(rng, s.Index(i), depth+1)
		}
		v.Set(s)
	case reflect.Map:
		if rng.IntN(4) == 0 {
			return
		}
		m := reflect.MakeMap(v.Type())
		for range rng.IntN(6) {
			k := reflect.New(v.Type().Key()).Elem()
			fill(rng, k, depth+1)
			e := reflect.New(v.Type().Elem()).Elem()
			fill(rng, e, depth+1)
			m.SetMapIndex(k, e)
		}
		v.Set(m)
	case reflect.Pointer:
		if rng.IntN(3) == 0 {
			return
		}
		p := reflect.New(v.Type().Elem())
		fill(rng, p.Elem(), depth+1)
		v.Set(p)
	case reflect.Struct:
		for i := range v.NumField() {
			fill(rng, v.Field(i), depth+1)
		}
	}
}

// fillWorst gives v a value that prints as long as its type allows, and
// reports whether it did.
func fillWorst(rng *rand.Rand, v reflect.Value, depth int) bool {
	switch v.Type() {
	case timeType:
		v.Set(reflect.ValueOf(times[0]))
		return true
	case rawType:
		v.SetBytes([]byte(`"` + strings.Repeat("<", rng.IntN(50)) + `"`))
		return true
	case numberType:
		v.SetString([]string{"", "12345678901234567890"}[rng.IntN(2)])
		return true
	}
	switch v.Kind() {
	case reflect.Bool:
		v.SetBool(false)
	case reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64:
		v.SetInt(-1 << (v.Type().Bits() - 1))
	case reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64, reflect.Uintptr:
		v.SetUint(math.MaxUint64 >> (64 - v.Type().Bits()))
	case reflect.Float64:
		v.SetFloat(floats[0])
	case reflect.Float32:
		v.SetFloat(float64(floats32[0]))
	case reflect.String:
		v.SetString(strings.Repeat("\x00", rng.IntN(7)))
	case reflect.Slice:
		n := 4 + rng.IntN(4)
		if depth > 2 {
			n = 1
		}
		s := reflect.MakeSlice(v.Type(), n, n)
		for i := range n {
			fill(rng, s.Index(i), depth+1)
		}
		v.Set(s)
	case reflect.Map:
		m := reflect.MakeMap(v.Type())
		n := 4 + rng.IntN(3)
		if depth > 2 {
			n = 1
		}
		for i := range n {
			k := reflect.New(v.Type().Key()).Elem()
			switch k.Kind() {
			case reflect.String:
				k.SetString(strings.Repeat("\x00", i))
			case reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64:
				k.SetInt(-1<<(k.Type().Bits()-1) + int64(i))
			default:
				k.SetUint(math.MaxUint64>>(64-k.Type().Bits()) - uint64(i))
			}
			e := reflect.New(v.Type().Elem()).Elem()
			fill(rng, e, depth+1)
			m.SetMapIndex(k, e)
		}
		v.Set(m)
	default:
		return false
	}
	return true
}

// --- held references (F9 of the review) ---

// checkHeld fails when an error refers to memory the value reaches, other
// than a float, which only reflection can write and no formula reads.
func checkHeld(name string, err error, v reflect.Value) {
	reached := map[uintptr]reflect.Type{}
	reach(v, reached, map[uintptr]bool{})
	seen := map[uintptr]bool{}
	var walk func(x reflect.Value)
	walk = func(x reflect.Value) {
		switch x.Kind() {
		case reflect.Pointer, reflect.Slice, reflect.Map, reflect.UnsafePointer:
			if x.IsNil() {
				return
			}
			p := x.Pointer()
			if t, ok := reached[p]; ok && t.Kind() != reflect.Float32 && t.Kind() != reflect.Float64 {
				fail("%s: the error %T refers to memory the value reaches, of type %s", name, err, t)
			}
			if seen[p] || x.Kind() == reflect.UnsafePointer {
				return
			}
			seen[p] = true
			if x.Kind() == reflect.Pointer {
				walk(x.Elem())
			} else if x.Kind() == reflect.Slice {
				for i := range x.Len() {
					walk(x.Index(i))
				}
			}
		case reflect.Interface:
			if !x.IsNil() {
				walk(x.Elem())
			}
		case reflect.Struct:
			if x.Type() == reflect.TypeFor[reflect.Value]() {
				// What a reflect.Value refers to is its ptr field.
				walk(x.Field(1))
				return
			}
			for i := range x.NumField() {
				walk(x.Field(i))
			}
		}
	}
	walk(reflect.ValueOf(&err).Elem())
}

// reach records the address of every piece of memory a value refers to,
// with its type, and of every field and element in it.
func reach(v reflect.Value, into map[uintptr]reflect.Type, seen map[uintptr]bool) {
	if v.CanAddr() {
		into[v.UnsafeAddr()] = v.Type()
	}
	switch v.Kind() {
	case reflect.Pointer:
		if !v.IsNil() && !seen[v.Pointer()] {
			seen[v.Pointer()] = true
			reach(v.Elem(), into, seen)
		}
	case reflect.Slice:
		if !v.IsNil() {
			for i := range v.Len() {
				reach(v.Index(i), into, seen)
			}
		}
	case reflect.Struct:
		for i := range v.NumField() {
			reach(v.Field(i), into, seen)
		}
	case reflect.Map:
		// What a map holds is copied out by MapIndex; the map itself is
		// the one address.
		if !v.IsNil() {
			into[v.Pointer()] = v.Type()
		}
	}
}

// --- methods that must not run, and those that some build runs ---

var calls atomic.Int64

// Loud has every method fmt and encoding/json could find but those of
// jsonMethods; encoding must call none of them.
type Loud string

func (Loud) String() string                    { calls.Add(1); return "" }
func (Loud) Error() string                     { calls.Add(1); return "" }
func (Loud) GoString() string                  { calls.Add(1); return "" }
func (Loud) Format(fmt.State, rune)            { calls.Add(1) }
func (Loud) IsZero() bool                      { calls.Add(1); return false }
func (*Loud) Set(string) error                 { calls.Add(1); return nil }
func (Loud) Len() int                          { calls.Add(1); return 0 }
func (Loud) Unwrap() error                     { calls.Add(1); return nil }
func (Loud) Is(error) bool                     { calls.Add(1); return false }
func (LoudInt) String() string                 { calls.Add(1); return "" }
func (LoudInt) IsZero() bool                   { calls.Add(1); return false }
func (*LoudStruct) String() string             { calls.Add(1); return "" }
func (LoudStruct) Error() string               { calls.Add(1); return "" }
func (*LoudStruct) IsZero() bool               { calls.Add(1); return false }
func (LoudMap) String() string                 { calls.Add(1); return "" }
func (LoudSlice) GoString() string             { calls.Add(1); return "" }
func (LoudKey) Error() string                  { calls.Add(1); return "" }
func (e *LoudEmbedded) Format(fmt.State, rune) { calls.Add(1) }

type LoudInt int64
type LoudStruct struct {
	A Loud
	B LoudInt `json:",omitempty"`
}
type LoudMap map[string]Loud
type LoudSlice []LoudStruct
type LoudKey string
type LoudEmbedded struct{ X int }

var called = map[string]*atomic.Int64{}

func record(name string) {
	called[name].Add(1)
}

func init() {
	for _, name := range []string{"MarshalJSON", "MarshalJSONTo", "AppendText", "MarshalText", "UnmarshalJSON", "UnmarshalJSONFrom", "UnmarshalText"} {
		called[name] = new(atomic.Int64)
	}
}

// Each of these has one method of jsonMethods; calledMethods runs the
// entries on each and reports which methods ran.
type HasMarshalJSON struct{ X int }
type HasAppendText struct{ X int }
type HasMarshalText struct{ X int }
type HasUnmarshalJSON struct{ X int }
type HasUnmarshalText struct{ X int }

func (HasMarshalJSON) MarshalJSON() ([]byte, error) { record("MarshalJSON"); return []byte("1"), nil }
func (HasAppendText) AppendText(b []byte) ([]byte, error) {
	record("AppendText")
	return append(b, 'x'), nil
}
func (HasMarshalText) MarshalText() ([]byte, error)  { record("MarshalText"); return []byte("x"), nil }
func (*HasUnmarshalJSON) UnmarshalJSON([]byte) error { record("UnmarshalJSON"); return nil }
func (*HasUnmarshalText) UnmarshalText([]byte) error { record("UnmarshalText"); return nil }

// methodValues are values of each type above, alone and as a field; the
// builds with jsonv2 add those of MarshalJSONTo and UnmarshalJSONFrom.
var methodValues = []any{HasMarshalJSON{}, HasAppendText{}, HasMarshalText{}, HasUnmarshalJSON{}, HasUnmarshalText{}}

func calledMethods() []string {
	for _, v := range methodValues {
		_, _ = json.Marshal(v)
		_, _ = json.Marshal(struct{ F any }{v})
		p := reflect.New(reflect.TypeOf(v))
		_ = json.Unmarshal([]byte(`"x"`), p.Interface())
		_ = json.Unmarshal([]byte(`1`), p.Interface())
	}
	var names []string
	for name, n := range called {
		if n.Load() > 0 {
			names = append(names, name)
		}
	}
	sort.Strings(names)
	return names
}
