package vego

import (
	"fmt"
	"go/token"
	"go/types"
	"math/big"
	"math/rand"
	"testing"

	"golang.org/x/tools/go/analysis"

	"github.com/spachava753/laas/vego/internal/logic"
	"github.com/spachava753/laas/vego/internal/spans"
)

// The layout invariant every comparison of a position with a stretch rests
// on (F42, step 3a; numberArray, internal/spans). In an allocation:
//
//   - every cell has a position of its own in its region;
//   - the byte a footprint row or the reach counts a cell at (spans.ByteOf)
//     is a byte of that cell's value: distinct for distinct cells, and in
//     the stretch of bytes of every value that holds the cell;
//   - the stretch of bytes [b, b + size) of a value holds, through In, in
//     each region exactly the cells of that value;
//   - the run of an array is contiguous, as an array value and a slice of
//     it need;
//   - the bound every slice carries, off·n + cap·n <= the end of the
//     allocation (wellFormed), is true of every slice of every run.
//
// The struct types are generated, beside those of the corpus, with fields
// of every size and alignment, arrays of them at every offset, nested
// structs, and arrays and slices of the result, at the sizes of amd64 and
// of 386, where int64 aligns to 4.

// layoutCell is a cell of an allocation at its position in its region.
type layoutCell struct {
	key    string
	region spans.Region
	pos    int64
}

// elemPosition gives the position of element k of a run whose cell is c,
// in a value at the byte at: the layout under test.
type elemPosition func(c cell, at, k int64) int64

// termInt evaluates a term of integer literals, sums, products, and
// quotients.
func termInt(t *logic.Term) int64 {
	switch t.Op {
	case logic.OpIntLit:
		return t.Val
	case logic.OpAdd:
		return termInt(t.Args[0]) + termInt(t.Args[1])
	case logic.OpMul:
		return termInt(t.Args[0]) * termInt(t.Args[1])
	case logic.OpDiv:
		return termInt(t.Args[0]) / termInt(t.Args[1])
	}
	panic(fmt.Sprintf("not a sum of literals: %v", t))
}

// layoutOfVerifier is the layout the verifier makes: element k of a run at
// start + k, from cell.start.
func layoutOfVerifier(c cell, at, k int64) int64 { return termInt(c.start(logic.IntLit(at))) + k }

// cellsAt returns the cells of a value of type t at the byte at, with the
// positions the layout gives.
func cellsAt(pv *pkgVerifier, t types.Type, at int64, layout elemPosition) []layoutCell {
	var out []layoutCell
	for _, c := range pv.cellsOf(t) {
		if !c.isRun() {
			out = append(out, layoutCell{c.key, c.region(), at + c.off})
			continue
		}
		for k := range c.run {
			out = append(out, layoutCell{c.key, c.region(), layout(c, at, k)})
		}
	}
	return out
}

// counted returns the byte at which the rows count a cell.
func counted(c layoutCell) int64 {
	return termInt(spans.ByteOf(c.region, logic.IntLit(c.pos)).Term())
}

// subValue is a value inside another: a nested struct or an array field,
// at its offset.
type subValue struct {
	t   types.Type
	off int64
}

// subValues returns every struct and array a struct holds by value, at any
// depth, with its offset.
func subValues(sizes types.Sizes, t types.Type, off int64) []subValue {
	out := []subValue{{t, off}}
	u, ok := t.Underlying().(*types.Struct)
	if !ok {
		return out
	}
	fields := make([]*types.Var, u.NumFields())
	for i := range fields {
		fields[i] = u.Field(i)
	}
	offsets := sizes.Offsetsof(fields)
	for i, field := range fields {
		switch field.Type().Underlying().(type) {
		case *types.Struct:
			out = append(out, subValues(sizes, field.Type(), off+offsets[i])...)
		case *types.Array:
			out = append(out, subValue{field.Type(), off + offsets[i]})
		}
	}
	return out
}

// checkLayout checks the invariant of an allocation of count values of a
// struct type t laid out one after another, as the array of a slice of t
// is, and returns what breaks it.
func checkLayout(pv *pkgVerifier, t types.Type, count int64, layout elemPosition) []string {
	sizes := pv.pass.TypesSizes
	size := sizes.Sizeof(t)
	var problems []string
	var cells []layoutCell
	for i := range count {
		cells = append(cells, cellsAt(pv, t, i*size, layout)...)
	}
	at, bytes := map[layoutCell]bool{}, map[int64]layoutCell{}
	for _, c := range cells {
		if at[c] {
			problems = append(problems, fmt.Sprintf("%s: two cells of %s at %d", t, c.key, c.pos))
		}
		at[c] = true
		b := counted(c)
		if other, seen := bytes[b]; seen {
			problems = append(problems, fmt.Sprintf("%s: %s at %d and %s at %d are both counted at the byte %d", t, other.key, other.pos, c.key, c.pos, b))
		}
		bytes[b] = c
	}
	allocBytes := count * size
	for i := range count {
		for _, sub := range subValues(sizes, t, i*size) {
			lo, hi := sub.off, sub.off+sizes.Sizeof(sub.t)
			stretch := spans.Bytes(logic.IntLit(lo), logic.IntLit(hi))
			// The cells of the value laid out on its own at its offset:
			// those of a nested struct, or the run of an array field.
			mine := map[layoutCell]bool{}
			for _, c := range cellsAt(pv, sub.t, sub.off, layout) {
				mine[c] = true
				if b := counted(c); b < lo || b >= hi {
					problems = append(problems, fmt.Sprintf("%s: %s at %d of the %s at %d is counted at %d, outside its bytes [%d, %d)", t, c.key, c.pos, sub.t, sub.off, b, lo, hi))
				}
			}
			for _, c := range cells {
				in := false
				if plo, phi, ok := stretch.In(c.region); ok {
					in = termInt(plo) <= c.pos && c.pos < termInt(phi)
				}
				switch {
				case in && !mine[c]:
					problems = append(problems, fmt.Sprintf("%s: %s at %d lies in the bytes [%d, %d) of the %s at %d, which does not hold it", t, c.key, c.pos, lo, hi, sub.t, sub.off))
				case !in && mine[c]:
					problems = append(problems, fmt.Sprintf("%s: %s at %d of the %s at %d lies outside its bytes [%d, %d)", t, c.key, c.pos, sub.t, sub.off, lo, hi))
				}
			}
		}
		// Each run is contiguous, and the bound of every slice of it holds.
		for _, c := range pv.cellsOf(t) {
			if !c.isRun() {
				continue
			}
			start := layout(c, i*size, 0)
			for k := range c.run {
				if layout(c, i*size, k) != start+k {
					problems = append(problems, fmt.Sprintf("%s: element %d of the run %s is not at %d", t, k, c.key, start+k))
				}
			}
			for lo := range c.run + 1 {
				if off, capacity := start+lo, c.run-lo; off*c.unit+capacity*c.unit > allocBytes {
					problems = append(problems, fmt.Sprintf("%s: the slice from %d of the run %s ends past the allocation of %d bytes", t, lo, c.key, allocBytes))
				}
			}
		}
	}
	return problems
}

// layoutTypes generates struct types: fields of every basic size, arrays
// of them, zero-size fields, and nested structs, to depth two.
func layoutTypes(r *rand.Rand, pkg *types.Package, n int) []types.Type {
	basics := []types.Type{types.Typ[types.Bool], types.Typ[types.Int8], types.Typ[types.Uint16], types.Typ[types.Int32],
		types.Typ[types.Int64], types.Typ[types.Float32], types.Typ[types.Float64], types.Typ[types.Int], types.Typ[types.Uint8]}
	leaf := func() types.Type {
		switch r.Intn(4) {
		case 0:
			return types.NewArray(basics[r.Intn(len(basics))], int64(1+r.Intn(3)))
		case 1:
			if r.Intn(4) == 0 {
				return types.NewStruct(nil, nil)
			}
		}
		return basics[r.Intn(len(basics))]
	}
	var structOf func(depth int) types.Type
	structOf = func(depth int) types.Type {
		var fields []*types.Var
		for i := range 1 + r.Intn(4) {
			ft := leaf()
			if depth > 0 && r.Intn(3) == 0 {
				ft = structOf(depth - 1)
			}
			name := fmt.Sprintf("F%d", i)
			if r.Intn(2) == 0 {
				name = fmt.Sprintf("f%d", i)
			}
			fields = append(fields, types.NewField(token.NoPos, pkg, name, ft, false))
		}
		return types.NewStruct(fields, nil)
	}
	out := make([]types.Type, n)
	for i := range out {
		out[i] = structOf(2)
	}
	return out
}

func TestCellPositions(t *testing.T) {
	for _, variant := range []struct{ goarch, fields string }{{"amd64", "place"}, {"386", "place"}, {"amd64", "own"}, {"386", "own"}} {
		goarch := variant.goarch
		pkg := types.NewPackage("example.com/layout/"+goarch+"/"+variant.fields, "layout")
		pv := &pkgVerifier{pass: &analysis.Pass{Pkg: pkg, TypesSizes: types.SizesFor("gc", goarch)}}
		if variant.fields == "own" {
			// No field of the package has its address taken, so the
			// unexported ones lie in the regions of their struct types.
			addressedOf.Store(pkg, &addressedFact{})
		}
		r := rand.New(rand.NewSource(1))
		checked := 0
		for _, st := range layoutTypes(r, pkg, 3000) {
			if _, ok := layoutOf(st); !ok {
				continue
			}
			checked++
			for _, count := range []int64{1, 3} {
				if problems := checkLayout(pv, st, count, layoutOfVerifier); len(problems) > 0 {
					t.Fatalf("%s: %v", goarch, problems[0])
				}
			}
		}
		if checked < 1000 {
			t.Fatalf("%s: only %d of the generated types were laid out", goarch, checked)
		}
	}
}

// TestWrongLayoutsFail shows that the check fails on wrong layouts:
// a run at A + k, whose slices break the bound every slice carries (the
// layout tried and dropped in step 3a, which proves F21's G), and a run at
// A + k·n, which is not contiguous.
func TestWrongLayoutsFail(t *testing.T) {
	pkg := types.NewPackage("example.com/layout/wrong", "layout")
	pv := &pkgVerifier{pass: &analysis.Pass{Pkg: pkg, TypesSizes: types.SizesFor("gc", "amd64")}}
	st := types.NewStruct([]*types.Var{
		types.NewField(token.NoPos, pkg, "A", types.Typ[types.Int64], false),
		types.NewField(token.NoPos, pkg, "B", types.NewArray(types.Typ[types.Int64], 2), false),
	}, nil)
	plus := func(c cell, at, k int64) int64 { return at + c.off + k }
	stride := func(c cell, at, k int64) int64 { return (at+c.off)/c.unit + k*c.unit }
	if problems := checkLayout(pv, st, 3, plus); len(problems) == 0 {
		t.Error("the layout at A + k passes the check")
	}
	if problems := checkLayout(pv, st, 3, stride); len(problems) == 0 {
		t.Error("a run with a stride passes the check")
	}
	if problems := checkLayout(pv, st, 3, layoutOfVerifier); len(problems) > 0 {
		t.Error(problems[0])
	}
}

// TestZeroSizeRuns: an array of elements of size zero in a struct is not
// laid out, since A + k would leave its bytes; the layout that laid one
// out at A + k would put its elements on the field after it.
func TestZeroSizeRuns(t *testing.T) {
	pkg := types.NewPackage("example.com/layout/zero", "layout")
	pv := &pkgVerifier{pass: &analysis.Pass{Pkg: pkg, TypesSizes: types.SizesFor("gc", "amd64")}}
	for _, elem := range []types.Type{types.NewStruct(nil, nil), types.NewArray(types.Typ[types.Int], 0)} {
		st := types.NewStruct([]*types.Var{
			types.NewField(token.NoPos, pkg, "Z", types.NewArray(elem, 4), false),
			types.NewField(token.NoPos, pkg, "N", types.Typ[types.Int64], false),
		}, nil)
		if _, ok := layoutOf(st); ok {
			t.Errorf("%s is laid out", st)
		}
		// What laying it out at A + k would do: the elements 1 to 3 lie
		// at the bytes of N, which is at 0 with them.
		offsets := pv.pass.TypesSizes.Offsetsof([]*types.Var{st.Field(0), st.Field(1)})
		if offsets[1] != 0 {
			t.Fatalf("N is at %d", offsets[1])
		}
		positions := map[int64]bool{offsets[1]: true}
		clash := false
		for k := range int64(4) {
			clash = clash || positions[offsets[0]+k]
		}
		if !clash {
			t.Errorf("a run of %s at A + k meets no field", elem)
		}
	}
}

// TestSliceBoundEdges: the bound every slice carries, off·n + cap·n <=
// the bound on arrays, holds of a slice of a wide array at the end of a
// large struct under the floor, and fails under A + k, where the slice is
// real and the bound false (F21 of the review of the design of step 3a):
// on 386, where MaxAlloc is 2^32 - 1, and on amd64 under a declared memory
// of 2GB.
func TestSliceBoundEdges(t *testing.T) {
	for _, edge := range []struct {
		goarch string
		pad    int64
		elem   types.Type
		bound  *big.Int
	}{
		{"386", 1100 << 20, types.Typ[types.Int32], nil},
		{"amd64", 1500 << 20, types.Typ[types.Int64], (&sizesDecl{memory: big.NewInt(2 << 30)}).arrayBound()},
	} {
		pkg := types.NewPackage("example.com/layout/edge"+edge.goarch, "layout")
		pv := &pkgVerifier{pass: &analysis.Pass{Pkg: pkg, TypesSizes: types.SizesFor("gc", edge.goarch)}}
		bound := edge.bound
		if bound == nil {
			bound = pv.maxAlloc()
		}
		st := types.NewStruct([]*types.Var{
			types.NewField(token.NoPos, pkg, "Pad", types.NewArray(types.Typ[types.Byte], edge.pad), false),
			types.NewField(token.NoPos, pkg, "C", types.NewArray(edge.elem, 4), false),
		}, nil)
		cells := pv.cellsOf(st)
		run := cells[len(cells)-1]
		fact := func(start int64) *big.Int {
			off, capacity, size := big.NewInt(start), big.NewInt(run.run), big.NewInt(run.unit)
			return new(big.Int).Add(new(big.Int).Mul(off, size), new(big.Int).Mul(capacity, size))
		}
		if floor := fact(layoutOfVerifier(run, 0, 0)); floor.Cmp(bound) > 0 {
			t.Errorf("%s: off·n + cap·n = %s passes %s for the slice of C under the floor", edge.goarch, floor, bound)
		}
		if plus := fact(run.off); plus.Cmp(bound) <= 0 {
			t.Errorf("%s: under A + k, off·n + cap·n = %s does not pass %s, so this is not the edge", edge.goarch, plus, bound)
		}
	}
}
