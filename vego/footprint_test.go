package vego

import (
	"bufio"
	"bytes"
	"fmt"
	"go/importer"
	"go/token"
	"go/types"
	"io"
	"maps"
	"math/rand"
	"reflect"
	"slices"
	"strings"
	"testing"
	"unsafe"
)

// TestOwnsDeclarations holds every owns declaration of the shipped files
// against the types of the toolchain: the type is a struct, each field it
// names exists and can be owned, and the type declares a state or has a
// field that is not exported, so that no struct of another package is
// identical to it. A project file cannot declare what a type owns.
func TestOwnsDeclarations(t *testing.T) {
	parallel(t)
	project := parseTrustFile("vego-trusted.yaml", []byte("version: 1\nowns:\n  example.com/x.T:\n    fields: [buf]\n    reason: r\n"), false)
	if len(project.problems) != 1 || len(project.owns) != 0 {
		t.Errorf("a project file that declares owns: problems = %+v, owns = %+v", project.problems, project.owns)
	}
	unreasoned := parseTrustFile("vego/trusted/std/x.yaml", []byte("version: 1\nowns:\n  bytes.Buffer:\n    fields: [buf]\n"), true)
	if len(unreasoned.problems) != 1 || len(unreasoned.owns) != 0 {
		t.Errorf("an owns declaration without a reason: problems = %+v, owns = %+v", unreasoned.problems, unreasoned.owns)
	}
	imports := importer.ForCompiler(token.NewFileSet(), "source", nil)
	declared := 0
	for _, file := range shippedContracts() {
		for _, decl := range file.owns {
			declared++
			pkg, err := imports.Import(decl.pkg)
			if err != nil {
				t.Fatalf("import %s: %v", decl.pkg, err)
			}
			obj, ok := pkg.Scope().Lookup(decl.typ).(*types.TypeName)
			if !ok {
				t.Errorf("%s.%s: no such type", decl.pkg, decl.typ)
				continue
			}
			u, isStruct := obj.Type().Underlying().(*types.Struct)
			if !isStruct {
				t.Errorf("%s.%s is not a struct type", decl.pkg, decl.typ)
				continue
			}
			for _, name := range decl.fields {
				found := false
				for field := range u.Fields() {
					if field.Name() == name {
						found = true
						_, isPointer := pointee(field.Type())
						if !isPointer && !isSlice(field.Type()) && !isMap(field.Type()) && !isIface(field.Type()) {
							t.Errorf("%s.%s owns %s, of type %s, which holds nothing that can be owned", decl.pkg, decl.typ, name, field.Type())
						}
						if field.Exported() {
							t.Errorf("%s.%s owns %s, which is exported, so code of other packages may write it", decl.pkg, decl.typ, name)
						}
					}
				}
				if !found {
					t.Errorf("%s.%s has no field %s", decl.pkg, decl.typ, name)
				}
			}
			if t.Failed() {
				continue
			}
			if got := ownedFieldsOf(obj.Type()); len(got) != len(decl.fields) {
				t.Errorf("%s.%s owns %d fields, and ownedFields finds %d", decl.pkg, decl.typ, len(decl.fields), len(got))
			}
		}
	}
	if declared != 6 {
		t.Errorf("the shipped files declare what %d types own; this test was written for 6, so read the new ones against the source of their package and change the count", declared)
	}
}

// ownedState is what the owned fields of an owner hold at one moment: for a
// slice, its array from its start to the end of its capacity, and for an
// interface value, a pointer, or a map, the words of the value.
type ownedState struct {
	arrays map[string][]byte
	words  map[string][2]uintptr
}

// ownerArrays holds every array that a harness of owners has seen or
// handed to a call, so that an array an owner comes to hold can be told
// new: one that overlaps none of them. Holding the arrays keeps them from
// being collected, so that a new array cannot be at the address of one.
type ownerArrays struct {
	held [][]byte
}

// add records the array of a slice from its start to its capacity.
func (a *ownerArrays) add(s []byte) {
	if cap(s) > 0 {
		a.held = append(a.held, s[:cap(s)])
	}
}

// snapshot reads the fields that the shipped declaration of owner's type
// names, through owner, a pointer to the struct, and records the arrays.
func (a *ownerArrays) snapshot(t *testing.T, owner any) ownedState {
	t.Helper()
	value := reflect.ValueOf(owner).Elem()
	typ := value.Type()
	var decl *ownsDecl
	for _, file := range shippedContracts() {
		if d, ok := file.owns[stateKey(typ.PkgPath(), typ.Name())]; ok {
			decl = &d
		}
	}
	if decl == nil {
		t.Fatalf("%s owns nothing by the shipped declarations", typ)
	}
	state := ownedState{arrays: map[string][]byte{}, words: map[string][2]uintptr{}}
	for _, name := range decl.fields {
		field := value.FieldByName(name)
		at := unsafe.Pointer(field.UnsafeAddr())
		switch field.Kind() {
		case reflect.Slice:
			if field.Type().Elem().Kind() != reflect.Uint8 {
				t.Fatalf("%s.%s is a slice of %s; the check reads slices of bytes", typ, name, field.Type().Elem())
			}
			s := *(*[]byte)(at)
			state.arrays[name] = s[:cap(s)]
			a.add(s)
		case reflect.Interface:
			state.words[name] = *(*[2]uintptr)(at)
		case reflect.Pointer, reflect.Map:
			state.words[name] = [2]uintptr{*(*uintptr)(at)}
		default:
			t.Fatalf("%s.%s is a %s, which the check does not read", typ, name, field.Kind())
		}
	}
	return state
}

// span is the addresses of an array, from its first byte to past its last.
func span(s []byte) (lo, hi uintptr) {
	if cap(s) == 0 {
		return 0, 0
	}
	lo = uintptr(unsafe.Pointer(unsafe.SliceData(s)))
	return lo, lo + uintptr(cap(s))
}

// grew reports how what an owner owns changed from before to after, if
// not as ownerGrowth says it may: each owned slice is without capacity, or
// lies inside the stretch of its array it held before, or lies in an array
// that overlaps none that the harness had seen before the call; every
// other owned field is the value it was. known holds the arrays seen
// before the call.
func grew(before, after ownedState, known [][]byte) string {
	for name, now := range after.arrays {
		lo, hi := span(now)
		if hi == lo {
			continue
		}
		oldLo, oldHi := span(before.arrays[name])
		if oldLo <= lo && hi <= oldHi && oldHi > oldLo {
			continue
		}
		for _, earlier := range known {
			if eLo, eHi := span(earlier); lo < eHi && eLo < hi {
				return fmt.Sprintf("%s holds memory that existed before the call and that it did not own", name)
			}
		}
	}
	for name, now := range after.words {
		if now != before.words[name] {
			return fmt.Sprintf("%s changed", name)
		}
	}
	return ""
}

// checkGrowth runs a call of a shipped method of owner and fails if what
// owner owns changed other than as ownerGrowth assumes.
func (a *ownerArrays) checkGrowth(t *testing.T, owner any, what string, call func()) {
	t.Helper()
	before := a.snapshot(t, owner)
	known := slices.Clone(a.held)
	call()
	if why := grew(before, a.snapshot(t, owner), known); why != "" {
		t.Fatalf("after %s, what the %T owns grew other than its owns declaration claims: %s", what, owner, why)
	}
}

// TestGrowthCheck holds the check of owner growth against calls that
// break it, so that the harnesses that use it can fail: a Scanner handed an
// array of the caller's, as Buffer is, a Writer whose writer is replaced,
// as Reset does, and a Scanner that grows into a new array, which is
// allowed.
func TestGrowthCheck(t *testing.T) {
	parallel(t)
	a := &ownerArrays{}
	s := bufio.NewScanner(strings.NewReader("a\nb\n"))
	given := make([]byte, 16)
	a.add(given)
	before := a.snapshot(t, s)
	known := slices.Clone(a.held)
	s.Buffer(given, 64)
	if why := grew(before, a.snapshot(t, s), known); why == "" {
		t.Error("a Scanner handed an array that existed before passed the check")
	}
	w := bufio.NewWriter(io.Discard)
	before = a.snapshot(t, w)
	known = slices.Clone(a.held)
	w.Reset(&bytes.Buffer{})
	if why := grew(before, a.snapshot(t, w), known); why == "" {
		t.Error("a Writer given another writer passed the check")
	}
	long := bufio.NewScanner(strings.NewReader(strings.Repeat("x", 10000) + "\n"))
	a.checkGrowth(t, long, "Scan", func() { long.Scan() })
}

// TestBufferMethodsGrowth holds the owns claim of bytes.Buffer and
// strings.Builder, that what a value owns grows only into memory the call
// made, for every exported method of the two types, shipped or not: code
// that is not verified and holds a buffer converted to an interface may
// assert it back and call any of them (condition (1) of the orchestrator's
// ruling on D6 of F38). A method of a newer Go that no case calls fails the
// test, so that it is read before the claim stays.
func TestBufferMethodsGrowth(t *testing.T) {
	parallel(t)
	rng := rand.New(rand.NewSource(7))
	text := func() []byte { return bytes.Repeat([]byte("ab\n"), rng.Intn(3000)) }
	t.Run("bytes.Buffer", func(t *testing.T) {
		calls := map[string]func(b *bytes.Buffer, a *ownerArrays){
			"Available":       func(b *bytes.Buffer, _ *ownerArrays) { b.Available() },
			"AvailableBuffer": func(b *bytes.Buffer, _ *ownerArrays) { b.AvailableBuffer() },
			"Bytes":           func(b *bytes.Buffer, _ *ownerArrays) { b.Bytes() },
			"Cap":             func(b *bytes.Buffer, _ *ownerArrays) { b.Cap() },
			"Grow":            func(b *bytes.Buffer, _ *ownerArrays) { b.Grow(rng.Intn(100000)) },
			"Len":             func(b *bytes.Buffer, _ *ownerArrays) { b.Len() },
			"Next":            func(b *bytes.Buffer, _ *ownerArrays) { b.Next(rng.Intn(b.Len() + 2)) },
			// Peek is new in Go 1.27, and called through reflection so that
			// the test builds with Go 1.26 too.
			"Peek": func(b *bytes.Buffer, _ *ownerArrays) {
				if m := reflect.ValueOf(b).MethodByName("Peek"); m.IsValid() {
					m.Call([]reflect.Value{reflect.ValueOf(rng.Intn(b.Len() + 2))})
				}
			},
			"Read": func(b *bytes.Buffer, a *ownerArrays) {
				p := make([]byte, rng.Intn(b.Len()+3))
				a.add(p)
				b.Read(p)
			},
			"ReadByte":  func(b *bytes.Buffer, _ *ownerArrays) { b.ReadByte() },
			"ReadBytes": func(b *bytes.Buffer, _ *ownerArrays) { b.ReadBytes('\n') },
			"ReadFrom": func(b *bytes.Buffer, a *ownerArrays) {
				p := text()
				a.add(p)
				b.ReadFrom(bytes.NewReader(p))
			},
			"ReadRune":   func(b *bytes.Buffer, _ *ownerArrays) { b.ReadRune() },
			"ReadString": func(b *bytes.Buffer, _ *ownerArrays) { b.ReadString('\n') },
			"Reset":      func(b *bytes.Buffer, _ *ownerArrays) { b.Reset() },
			"String":     func(b *bytes.Buffer, _ *ownerArrays) { _ = b.String() },
			"Truncate":   func(b *bytes.Buffer, _ *ownerArrays) { b.Truncate(rng.Intn(b.Len() + 1)) },
			"UnreadByte": func(b *bytes.Buffer, _ *ownerArrays) { b.UnreadByte() },
			"UnreadRune": func(b *bytes.Buffer, _ *ownerArrays) { b.UnreadRune() },
			"Write": func(b *bytes.Buffer, a *ownerArrays) {
				p := text()
				a.add(p)
				b.Write(p)
			},
			"WriteByte":   func(b *bytes.Buffer, _ *ownerArrays) { b.WriteByte('x') },
			"WriteRune":   func(b *bytes.Buffer, _ *ownerArrays) { b.WriteRune('é') },
			"WriteString": func(b *bytes.Buffer, _ *ownerArrays) { b.WriteString(string(text())) },
			"WriteTo":     func(b *bytes.Buffer, _ *ownerArrays) { b.WriteTo(io.Discard) },
		}
		checkAllMethods(t, reflect.TypeOf(&bytes.Buffer{}), calls, func() *bytes.Buffer { return new(bytes.Buffer) })
	})
	t.Run("strings.Builder", func(t *testing.T) {
		calls := map[string]func(b *strings.Builder, a *ownerArrays){
			"Cap":  func(b *strings.Builder, _ *ownerArrays) { b.Cap() },
			"Grow": func(b *strings.Builder, _ *ownerArrays) { b.Grow(rng.Intn(100000)) },
			"Len":  func(b *strings.Builder, _ *ownerArrays) { b.Len() },
			"Reset": func(b *strings.Builder, _ *ownerArrays) {
				b.Reset()
			},
			"String": func(b *strings.Builder, _ *ownerArrays) { _ = b.String() },
			"Write": func(b *strings.Builder, a *ownerArrays) {
				p := text()
				a.add(p)
				b.Write(p)
			},
			"WriteByte":   func(b *strings.Builder, _ *ownerArrays) { b.WriteByte('x') },
			"WriteRune":   func(b *strings.Builder, _ *ownerArrays) { b.WriteRune('é') },
			"WriteString": func(b *strings.Builder, _ *ownerArrays) { b.WriteString(string(text())) },
		}
		checkAllMethods(t, reflect.TypeOf(&strings.Builder{}), calls, func() *strings.Builder { return new(strings.Builder) })
	})
}

// checkAllMethods calls the methods of a buffer type at random, each round
// a fresh value, around the check of owner growth, and fails for an
// exported method that calls has no case for.
func checkAllMethods[B any](t *testing.T, typ reflect.Type, calls map[string]func(B, *ownerArrays), fresh func() B) {
	for i := range typ.NumMethod() {
		if name := typ.Method(i).Name; calls[name] == nil {
			t.Fatalf("%s has a method %s that no case calls; read whether it keeps what the type owns growing only into new memory, and add it", typ, name)
		}
	}
	names := slices.Sorted(maps.Keys(calls))
	rng := rand.New(rand.NewSource(11))
	for range 200 {
		b := fresh()
		arrays := &ownerArrays{}
		for range 1 + rng.Intn(20) {
			name := names[rng.Intn(len(names))]
			arrays.checkGrowth(t, any(b), name, func() { calls[name](b, arrays) })
		}
	}
}
