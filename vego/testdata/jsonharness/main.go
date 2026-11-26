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
	"errors"
	"fmt"
	"io"
	"math"
	"math/rand/v2"
	"os"
	"reflect"
	"runtime"
	"sort"
	"strings"
	"sync/atomic"
	"time"
	"unsafe"
)

// Input is what the test hands over. With Allocs set the program only
// measures the largest single allocation of each encoding call (allocs).
type Input struct {
	Seed    uint64
	Samples int
	Cases   []Case
	Allocs  bool
}

// Case is one type with the lengths vego bounds for it.
type Case struct {
	Type    string
	Lengths []Length
}

// Length is a length the bound counts, under the steps of its chain; see
// json.go.
type Length struct {
	Key   string
	Steps []Step
	Text  string
}

// Step is a quantifier or a guard of a chain.
type Step struct{ Binder, Length, Guard string }

// Sample is what one value gave: the length of what Marshal returned and
// of what MarshalIndent returned under each prefix and indent of indents,
// or -1 for an error, and the longest instance of each length.
type Sample struct {
	Type  string
	Outs  []int64
	Maxes map[string]int64
}

// Output is what the program found.
type Output struct {
	// Build names the build of encoding/json.
	Build string
	// Failures holds what broke a claim.
	Failures []string
	// Samples holds what each value gave.
	Samples []Sample
	// Called holds the methods of jsonMethods that the build called.
	Called []string
	// Errors holds the dynamic types of the errors in the trees of what
	// the entries returned, and DecodeErrors those Unmarshal returned.
	Errors       []string
	DecodeErrors []string
	// Allocs holds, with Input.Allocs, what each encoding call allocated.
	Allocs []Alloc
}

// Alloc is the largest single allocation that one call of Marshal,
// MarshalIndent, or Encode made, with the length of what it wrote and the
// largest string, slice, or map's entries in bytes that the value holds.
type Alloc struct {
	Type, Call                  string
	Largest, Out, Held, Entries int64
}

var out = Output{}

// indents are the prefixes and indents MarshalIndent is run with; the
// test reads their lengths from here.
var indents = []struct{ prefix, indent string }{{"", "  "}, {">", "\t\t\t"}, {"<<", ""}}

func fail(format string, args ...any) {
	if len(out.Failures) < 50 {
		out.Failures = append(out.Failures, fmt.Sprintf(format, args...))
	}
}

func main() {
	for _, method := range recorderMethods {
		if _, ok := reflect.TypeOf(&recorder{}).MethodByName(method); !ok {
			fail("the recorder has no method %s", method)
		}
	}
	var in Input
	if err := json.NewDecoder(os.Stdin).Decode(&in); err != nil {
		panic(err)
	}
	out.Build = build()
	rng := rand.New(rand.NewPCG(in.Seed, 29))
	if in.Allocs {
		allocs(rng, in)
		if err := json.NewEncoder(os.Stdout).Encode(out); err != nil {
			panic(err)
		}
		return
	}
	errTypes, decodeErrTypes := map[string]bool{}, map[string]bool{}
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
			sample := Sample{Type: c.Type, Maxes: measure(c, v)}
			calls.Store(0)
			for i := -1; i < len(indents); i++ {
				var b []byte
				var err error
				if i < 0 {
					b, err = json.Marshal(v.Interface())
				} else {
					b, err = json.MarshalIndent(v.Interface(), indents[i].prefix, indents[i].indent)
				}
				if err != nil {
					if b != nil {
						fail("%s: an error and a result that is not nil", c.Type)
					}
					treeTypes(err, errTypes)
					checkHeld(c.Type, err, v)
					sample.Outs = append(sample.Outs, -1)
					continue
				}
				checkFresh(c.Type, b, v)
				sample.Outs = append(sample.Outs, int64(len(b)))
			}
			checkEncode(c.Type, v)
			checkDecode(c.Type, t, v, decodeErrTypes)
			checkDecoder(c.Type, t, v, decodeErrTypes)
			if n := calls.Load(); n != 0 {
				fail("%s: encoding called %d methods it must not call", c.Type, n)
			}
			out.Samples = append(out.Samples, sample)
		}
	}
	out.Called = calledMethods()
	for t := range errTypes {
		out.Errors = append(out.Errors, t)
	}
	sort.Strings(out.Errors)
	for t := range decodeErrTypes {
		out.DecodeErrors = append(out.DecodeErrors, t)
	}
	sort.Strings(out.DecodeErrors)
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

// --- the in-place encoder ---

// recorder records what an encoder writes; its other methods fail.
type recorder struct {
	writes [][]byte
	n      int // what Write reports, -1 for all
	err    error
}

func (r *recorder) Write(p []byte) (int, error) {
	r.writes = append(r.writes, append([]byte(nil), p...))
	if r.n >= 0 {
		return min(r.n, len(p)), r.err
	}
	return len(p), r.err
}

// The other methods are those that the standard library is known to look
// for by a type assertion (lookedFor in probes_test.go), each of which
// counts as a call that Encode's entry, with enc under runs and nothing
// under asserts, says it does not make.
func (r *recorder) WriteString(string) (int, error)   { calls.Add(1); return 0, nil }
func (r *recorder) ReadFrom(io.Reader) (int64, error) { calls.Add(1); return 0, nil }
func (r *recorder) WriteTo(io.Writer) (int64, error)  { calls.Add(1); return 0, nil }
func (r *recorder) Close() error                      { calls.Add(1); return nil }
func (r *recorder) Flush() error                      { calls.Add(1); return nil }
func (r *recorder) String() string                    { calls.Add(1); return "" }
func (r *recorder) Error() string                     { calls.Add(1); return "" }
func (r *recorder) Format(fmt.State, rune)            { calls.Add(1) }
func (r *recorder) GoString() string                  { calls.Add(1); return "" }
func (r *recorder) Unwrap() error                     { calls.Add(1); return nil }
func (r *recorder) Is(error) bool                     { calls.Add(1); return false }
func (r *recorder) As(any) bool                       { calls.Add(1); return false }
func (r *recorder) Timeout() bool                     { calls.Add(1); return false }
func (r *recorder) Temporary() bool                   { calls.Add(1); return false }

// recorderMethods are the methods the recorder must have, which main
// checks.
var recorderMethods = []string{"String", "Error", "Format", "GoString", "WriteString", "ReadFrom", "WriteTo",
	"Unwrap", "Is", "As", "Timeout", "Temporary", "Close", "Flush"}

var errWriter = errors.New("the writer failed")

// checkEncode holds the claim of Encode's entry: on a new encoder, Encode
// writes once, exactly what Marshal returns and a newline, and returns the
// error Write returned; when Marshal fails, it writes nothing and returns
// an error. It is run on a writer that succeeds, one that fails, and one
// that writes short.
func checkEncode(name string, v reflect.Value) {
	want, merr := json.Marshal(v.Interface())
	for _, w := range []*recorder{{n: -1}, {n: -1, err: errWriter}, {n: 1}} {
		err := json.NewEncoder(w).Encode(v.Interface())
		switch {
		case merr != nil:
			if err == nil || len(w.writes) != 0 {
				fail("%s: Marshal failed, and Encode returned %v after %d writes", name, err, len(w.writes))
			}
		case len(w.writes) != 1 || string(w.writes[0]) != string(want)+"\n":
			fail("%s: Encode wrote %d times, not once what Marshal returns and a newline", name, len(w.writes))
		case w.err != nil && err != w.err:
			fail("%s: Encode returned %v where Write returned %v", name, err, w.err)
		case w.err == nil && err != nil:
			fail("%s: Encode returned %v where Write succeeded", name, err)
		}
	}
}

// --- decoding ---

// checkDecode holds the claim of Unmarshal's entry, decoding into a zero
// value of the type (what vego requires: every slice, map, and pointer
// nil) from what Marshal returns for v and from broken forms of it: the
// unexported fields keep their values, the data is unchanged, nothing
// decoded refers into the data or changes when the data does afterwards,
// no method of jsonMethods' complement runs, and every error has a type
// that was read.
func checkDecode(name string, t reflect.Type, v reflect.Value, errTypes map[string]bool) {
	good, _ := json.Marshal(v.Interface())
	inputs := [][]byte{good, good[:len(good)/2], []byte(strings.Replace(string(good), `"`, `1`, 1)),
		[]byte(`{"` + "\xff\xfe" + `":1, "B":"` + "\xff" + `"}`), []byte(`[` + "\"\xff\xff\"" + `]`), []byte(`{"n":"!!!!"}`), []byte(`"AA="`)}
	for _, in := range inputs {
		data := append([]byte(nil), in...)
		p := reflect.New(t)
		// Unexported fields get values at every depth the value holds by
		// value, embedded structs included, which must be kept (F27).
		var kept []reflect.Value
		var copies []any
		plant(p.Elem(), &kept, &copies)
		calls.Store(0)
		err := json.Unmarshal(data, p.Interface())
		if err != nil {
			treeTypes(err, errTypes)
		}
		if n := calls.Load(); n != 0 {
			fail("%s: decoding called %d methods it must not call", name, n)
		}
		if string(data) != string(in) {
			fail("%s: Unmarshal changed the data", name)
		}
		for i, fv := range kept {
			if !reflect.DeepEqual(fv.Interface(), copies[i]) {
				fail("%s: Unmarshal wrote an unexported field", name)
			}
		}
		// What it allocated behind a pointer has its unexported fields
		// zero.
		zeroBehind(name, p.Elem(), false)
		// Nothing decoded lies in the data's array.
		reached := map[uintptr]reflect.Type{}
		reach(p.Elem(), reached, map[uintptr]bool{})
		lo := uintptr(unsafe.Pointer(unsafe.SliceData(data)))
		for addr, typ := range reached {
			if addr >= lo && addr < lo+uintptr(cap(data)) {
				fail("%s: what Unmarshal decoded, of type %s, lies in the data", name, typ)
			}
		}
		// Nothing decoded changes when the data does.
		before, _ := json.Marshal(p.Interface())
		for i := range data {
			data[i] = 'x'
		}
		after, _ := json.Marshal(p.Interface())
		if string(before) != string(after) {
			fail("%s: what Unmarshal decoded changed with the data", name)
		}
	}
}

// readRecorder serves data to a decoder and records how much was read;
// its other methods fail.
type readRecorder struct {
	data []byte
	pos  int
	// during holds the goroutine of the Decode that may call Read, and is
	// "" outside it; faults counts calls with an empty buffer, outside the
	// call, or on another goroutine.
	during string
	faults int
}

// goroutine returns the header line of the stack of the calling goroutine,
// which names it.
func goroutine() string {
	buf := make([]byte, 64)
	buf = buf[:runtime.Stack(buf, false)]
	line, _, _ := strings.Cut(string(buf), " [")
	return line
}

func (r *readRecorder) Read(p []byte) (int, error) {
	if len(p) == 0 || r.during == "" || r.during != goroutine() {
		r.faults++
	}
	if r.pos == len(r.data) {
		return 0, io.EOF
	}
	n := copy(p, r.data[r.pos:])
	r.pos += n
	return n, nil
}

func (r *readRecorder) WriteTo(io.Writer) (int64, error) { calls.Add(1); return 0, nil }
func (r *readRecorder) ReadByte() (byte, error)          { calls.Add(1); return 0, nil }
func (r *readRecorder) Close() error                     { calls.Add(1); return nil }

// checkDecoder holds the claim of Decode's entry: a new decoder over
// io.LimitReader(r, n) reads at most n bytes of r, decodes the first value
// as Unmarshal does when it fits in n, and calls nothing of r but Read,
// which it calls only with a buffer that is not empty, during Decode, and
// on the goroutine that called Decode.
func checkDecoder(name string, t reflect.Type, v reflect.Value, errTypes map[string]bool) {
	good, err := json.Marshal(v.Interface())
	if err != nil {
		return
	}
	full := append(append([]byte(nil), good...), []byte(` {"after":1}`)...)
	for _, n := range []int64{int64(len(good)) - 3, int64(len(good)), int64(len(good)) + 5, int64(len(full)) + 100, -1} {
		r := &readRecorder{data: full}
		p := reflect.New(t)
		calls.Store(0)
		r.during = goroutine()
		err := json.NewDecoder(io.LimitReader(r, n)).Decode(p.Interface())
		r.during = ""
		if r.faults != 0 {
			fail("%s: the decoder called Read %d times with an empty buffer, outside Decode, or on another goroutine", name, r.faults)
		}
		if err != nil {
			treeTypes(err, errTypes)
		}
		if n >= 0 && int64(r.pos) > n || n < 0 && r.pos != 0 {
			fail("%s: a decoder over io.LimitReader(r, %d) read %d bytes", name, n, r.pos)
		}
		if c := calls.Load(); c != 0 {
			fail("%s: the decoder called %d methods of the reader or the value but Read", name, c)
		}
		if n >= int64(len(good)) && err == nil {
			q := reflect.New(t)
			if json.Unmarshal(good, q.Interface()) == nil {
				a, _ := json.Marshal(p.Interface())
				b, _ := json.Marshal(q.Interface())
				if string(a) != string(b) {
					fail("%s: the decoder decoded %s where Unmarshal decodes %s", name, clip(a), clip(b))
				}
			}
		}
	}
}

// plant fills every unexported field of what v holds by value, at any
// depth through structs, and records each with a copy of its value.
func plant(v reflect.Value, kept *[]reflect.Value, copies *[]any) {
	if v.Kind() != reflect.Struct || v.Type() == timeType {
		return
	}
	for i := range v.NumField() {
		f := v.Type().Field(i)
		fv := settable(v.Field(i))
		if !f.IsExported() && !f.Anonymous {
			fill(rand.New(rand.NewPCG(uint64(len(*kept)), 3)), fv, 3)
			*kept = append(*kept, fv)
			*copies = append(*copies, reflect.ValueOf(fv.Interface()).Interface())
			continue
		}
		plant(fv, kept, copies)
	}
}

// zeroBehind fails when a struct that Unmarshal allocated behind a pointer
// has an unexported field that is not zero.
func zeroBehind(name string, v reflect.Value, allocated bool) {
	switch v.Kind() {
	case reflect.Pointer:
		if !v.IsNil() {
			zeroBehind(name, v.Elem(), true)
		}
	case reflect.Slice:
		for i := range v.Len() {
			zeroBehind(name, v.Index(i), true)
		}
	case reflect.Map:
		for _, k := range v.MapKeys() {
			zeroBehind(name, v.MapIndex(k), true)
		}
	case reflect.Struct:
		if v.Type() == timeType {
			return
		}
		for i := range v.NumField() {
			f := v.Type().Field(i)
			fv := v.Field(i)
			if allocated && !f.IsExported() && !f.Anonymous && !fv.IsZero() {
				fail("%s: what Unmarshal allocated has the unexported field %s set", name, f.Name)
			}
			zeroBehind(name, fv, allocated)
		}
	}
}

// --- the lengths, measured on the value ---

// measure returns, for each length of a case, the longest instance of it
// in the value: the length read at every element and key of the chain it
// lies under, where each guard holds. A length with no instance is 0.
func measure(c Case, v reflect.Value) map[string]int64 {
	maxes := map[string]int64{}
	for _, l := range c.Lengths {
		env := map[string]reflect.Value{"v": v}
		var most int64
		var walk func(i int)
		walk = func(i int) {
			if i == len(l.Steps) {
				most = max(most, int64(lengthOf(eval(strings.Trim(l.Text, "|"), env))))
				return
			}
			s := l.Steps[i]
			if s.Guard != "" {
				if !eval(strings.TrimSuffix(s.Guard, " != nil"), env).IsNil() {
					walk(i + 1)
				}
				return
			}
			name, over, _ := strings.Cut(s.Binder, " in ")
			if strings.HasPrefix(over, "[0, |") {
				seq := eval(strings.TrimSuffix(strings.TrimPrefix(over, "[0, |"), "|)"), env)
				for k := range seq.Len() {
					env[name] = reflect.ValueOf(k)
					walk(i + 1)
				}
			} else {
				m := eval(over, env)
				for _, k := range m.MapKeys() {
					env[name] = k
					walk(i + 1)
				}
			}
			delete(env, name)
		}
		walk(0)
		maxes[l.Key] = most
	}
	return maxes
}

// checkFresh fails when what an entry returned lies in memory the value
// reaches, or in what an earlier call returned (F18 of the review).
func checkFresh(name string, b []byte, v reflect.Value) {
	if cap(b) == 0 {
		return
	}
	lo := uintptr(unsafe.Pointer(unsafe.SliceData(b)))
	hi := lo + uintptr(cap(b))
	reached := map[uintptr]reflect.Type{}
	reach(v, reached, map[uintptr]bool{})
	for p, t := range reached {
		if p >= lo && p < hi {
			fail("%s: what was returned lies in memory of type %s that the value reaches", name, t)
		}
	}
	for _, r := range results {
		if lo < r[1] && r[0] < hi {
			fail("%s: what was returned overlaps what an earlier call returned", name)
		}
	}
	results = append(results, [2]uintptr{lo, hi})
	kept = append(kept, b)
}

// results holds the stretches earlier calls returned, kept alive by kept.
var (
	results [][2]uintptr
	kept    [][]byte
)

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
				// Keys of one length, each byte escaped.
				k.SetString(string([]byte{byte(i % 32), byte(i / 32 % 32), 0}))
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

// --- allocations ---

// allocs measures, for samples of each type, the largest single allocation
// that Marshal, MarshalIndent, and Encode make while they run (F8 of the
// review of F38): every request of the encoder is to be at most a small
// multiple of what exists, the output so far or one value the encoded value
// holds. Half the samples have their strings and byte slices made one long
// value shared by every place that holds one, so that the output is far
// longer than anything the value holds.
func allocs(rng *rand.Rand, in Input) {
	runtime.MemProfileRate = 1
	shared := strings.Repeat("a<\x00é\"", 40000)
	for _, c := range in.Cases {
		t := registry[c.Type]
		for i := range in.Samples {
			v := reflect.New(t).Elem()
			worst = rng.IntN(2) == 0
			fill(rng, v, 0)
			if i%2 == 1 {
				lengthen(v, shared, map[uintptr]bool{})
			}
			held := heldBytes(v, map[uintptr]bool{})
			entries := mostEntries(v, map[uintptr]bool{})
			for _, call := range []string{"Marshal", "MarshalIndent", "Encode"} {
				var n int64
				var failed bool
				largest := largestAllocation(func() {
					var b []byte
					var err error
					switch call {
					case "Marshal":
						b, err = json.Marshal(v.Interface())
					case "MarshalIndent":
						b, err = json.MarshalIndent(v.Interface(), "", "  ")
					default:
						w := &counter{}
						err = json.NewEncoder(w).Encode(v.Interface())
						n = w.n
					}
					if call != "Encode" {
						n = int64(len(b))
					}
					failed = err != nil
				})
				if !failed {
					out.Allocs = append(out.Allocs, Alloc{Type: c.Type, Call: call, Largest: largest, Out: n, Held: held, Entries: entries})
				}
			}
		}
	}
}

// counter is a writer that counts what it is handed and keeps nothing.
type counter struct{ n int64 }

func (c *counter) Write(p []byte) (int, error) { c.n += int64(len(p)); return len(p), nil }

// largestAllocation returns the size of the largest single object that f
// allocated. The memory profile keeps one record for each stack and size
// of object, and is complete only after a few collections.
func largestAllocation(f func()) int64 {
	type key struct {
		stack [32]uintptr
		size  int64
	}
	snapshot := func() map[key]int64 {
		for range 3 {
			runtime.GC()
		}
		n, _ := runtime.MemProfile(nil, true)
		records := make([]runtime.MemProfileRecord, n+100)
		n, _ = runtime.MemProfile(records, true)
		seen := map[key]int64{}
		for _, r := range records[:n] {
			if r.AllocObjects > 0 && !measuring(r.Stack()) {
				seen[key{r.Stack0, r.AllocBytes / r.AllocObjects}] = r.AllocObjects
			}
		}
		return seen
	}
	before := snapshot()
	f()
	after := snapshot()
	var largest int64
	for k, objects := range after {
		if objects > before[k] && k.size > largest {
			largest = k.size
		}
	}
	return largest
}

// measuring reports whether a stack is that of what largestAllocation
// allocates itself to read the profile, which f does not.
func measuring(stack []uintptr) bool {
	frames := runtime.CallersFrames(stack)
	for {
		frame, more := frames.Next()
		// The innermost frame of this program decides: the encoder runs
		// in the closure that allocs hands over.
		if strings.HasPrefix(frame.Function, "main.") {
			return strings.HasPrefix(frame.Function, "main.largestAllocation")
		}
		if !more {
			return false
		}
	}
}

// lengthen makes every string and byte slice that v holds one shared long
// value.
func lengthen(v reflect.Value, long string, seen map[uintptr]bool) {
	switch v.Kind() {
	case reflect.String:
		if v.CanSet() && v.Type() != numberType {
			v.SetString(long)
		}
	case reflect.Slice:
		if v.Type().Elem().Kind() == reflect.Uint8 && v.CanSet() && v.Type() != rawType {
			v.SetBytes([]byte(long[:len(long)/2]))
			return
		}
		for i := range v.Len() {
			lengthen(v.Index(i), long, seen)
		}
	case reflect.Array:
		for i := range v.Len() {
			lengthen(v.Index(i), long, seen)
		}
	case reflect.Pointer:
		if !v.IsNil() && !seen[v.Pointer()] {
			seen[v.Pointer()] = true
			lengthen(v.Elem(), long, seen)
		}
	case reflect.Struct:
		for i := range v.NumField() {
			if v.Type().Field(i).IsExported() {
				lengthen(v.Field(i), long, seen)
			}
		}
	case reflect.Map:
		// The values of a map cannot be set in place; its keys stay. A
		// map of a key type with many values gets many entries, so that
		// what sorting its keys allocates shows.
		if !v.CanSet() {
			return
		}
		key := v.Type().Key()
		m := reflect.MakeMap(v.Type())
		for i := range 5000 {
			k := reflect.New(key).Elem()
			switch key.Kind() {
			case reflect.String:
				k.SetString(fmt.Sprintf("k%d", i))
			case reflect.Int16, reflect.Int32, reflect.Int64, reflect.Int:
				k.SetInt(int64(i))
			case reflect.Uint16, reflect.Uint32, reflect.Uint64, reflect.Uint:
				k.SetUint(uint64(i))
			default:
				return
			}
			m.SetMapIndex(k, reflect.New(v.Type().Elem()).Elem())
		}
		v.Set(m)
	}
}

// mostEntries returns the most entries of a map that v holds.
func mostEntries(v reflect.Value, seen map[uintptr]bool) int64 {
	var most int64
	note := func(n int64) { most = max(most, n) }
	switch v.Kind() {
	case reflect.Slice, reflect.Array:
		for i := range v.Len() {
			note(mostEntries(v.Index(i), seen))
		}
	case reflect.Pointer, reflect.Interface:
		if !v.IsNil() && (v.Kind() == reflect.Interface || !seen[v.Pointer()]) {
			if v.Kind() == reflect.Pointer {
				seen[v.Pointer()] = true
			}
			note(mostEntries(v.Elem(), seen))
		}
	case reflect.Struct:
		for i := range v.NumField() {
			note(mostEntries(v.Field(i), seen))
		}
	case reflect.Map:
		note(int64(v.Len()))
		for it := v.MapRange(); it.Next(); {
			note(mostEntries(it.Value(), seen))
		}
	}
	return most
}

// heldBytes returns the largest string, slice array, or map's entries, in
// bytes, that v holds.
func heldBytes(v reflect.Value, seen map[uintptr]bool) int64 {
	var most int64
	note := func(n int64) { most = max(most, n) }
	switch v.Kind() {
	case reflect.String:
		note(int64(v.Len()))
	case reflect.Slice:
		note(int64(v.Cap()) * int64(v.Type().Elem().Size()))
		for i := range v.Len() {
			note(heldBytes(v.Index(i), seen))
		}
	case reflect.Array:
		for i := range v.Len() {
			note(heldBytes(v.Index(i), seen))
		}
	case reflect.Pointer, reflect.Interface:
		if !v.IsNil() && (v.Kind() == reflect.Interface || !seen[v.Pointer()]) {
			if v.Kind() == reflect.Pointer {
				seen[v.Pointer()] = true
			}
			note(heldBytes(v.Elem(), seen))
		}
	case reflect.Struct:
		for i := range v.NumField() {
			note(heldBytes(v.Field(i), seen))
		}
	case reflect.Map:
		note(int64(v.Len()) * int64(v.Type().Key().Size()+v.Type().Elem().Size()))
		for it := v.MapRange(); it.Next(); {
			note(heldBytes(it.Key(), seen))
			note(heldBytes(it.Value(), seen))
		}
	}
	return most
}
