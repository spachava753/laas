package vego

import (
	"fmt"
	"go/ast"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"strings"
	"testing"
)

// TestWalkOfEncodingEnds holds the walk of encoding/json to its limits: a type
// that holds itself, by any way the walk goes in, is refused, and so is a
// type deeper or wider than the limits, each at once. A walk that did not
// end took sixteen gigabytes in 23 seconds (the first version entered a
// struct behind a pointer without its cycle guard); the limits alone stop
// it.
func TestWalkOfEncodingEnds(t *testing.T) {
	parallel(t)
	var src strings.Builder
	src.WriteString(`package p
type Chain struct{ Next *Chain }
type Nest []Nest
type Mapped struct{ M map[string]Mapped }
type A struct{ B *B }
type B struct{ As []A }
type Embeds struct{ *Embeds }
type Inner struct{ Outer }
type Outer struct{ I *Inner }
`)
	for i := range jsonMaxDepth + 2 {
		fmt.Fprintf(&src, "type Deep%d struct{ X Deep%d }\n", i, i+1)
	}
	fmt.Fprintf(&src, "type Deep%d struct{ S string }\n", jsonMaxDepth+2)
	src.WriteString("type Wide struct {\n")
	for i := range jsonMaxGroups + 1 {
		fmt.Fprintf(&src, "\tF%d []int\n", i)
	}
	src.WriteString("}\n")
	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "p.go", src.String(), 0)
	if err != nil {
		t.Fatal(err)
	}
	pkg, err := (&types.Config{Importer: importer.Default()}).Check("p", fset, []*ast.File{file}, nil)
	if err != nil {
		t.Fatal(err)
	}
	sizes := types.SizesFor("gc", "amd64")
	for name, want := range map[string]string{
		"Chain":  "holds itself",
		"Nest":   "holds itself",
		"Mapped": "holds itself",
		"A":      "holds itself",
		"Embeds": "holds itself",
		"Outer":  "holds itself",
		"Deep0":  "levels deep",
		"Wide":   "chains of slices",
	} {
		typ := pkg.Scope().Lookup(name).Type()
		for _, ty := range []types.Type{typ, types.NewPointer(typ), types.NewSlice(typ)} {
			w := &jsonWalk{wt: jsonWeights, pkg: pkg, sizes: sizes}
			top := &jsonGroup{}
			w.groups = append(w.groups, top)
			why := w.value(ty, "v", "v", top, false, 0)
			if _, isPointer := ty.(*types.Pointer); isPointer && why != "" && name == "Nest" {
				// A pointer to a slice is refused for that.
			} else if !strings.Contains(why, want) {
				t.Errorf("%s: the walk says %q, not that it %s", ty, why, want)
			}
			if w.steps > jsonMaxSteps+1 || len(w.groups) > jsonMaxGroups+1 {
				t.Errorf("%s: the walk went past its limits: %d steps, %d groups", ty, w.steps, len(w.groups))
			}
		}
	}
}
