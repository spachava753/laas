package vego

import (
	"go/ast"
	"go/parser"
	"go/token"
	"go/types"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"sync"

	"golang.org/x/tools/go/analysis"
)

// Which fields of structs a pointer can point to (F42, design 3.2).
//
// A field of a number, a boolean, or a string that a pointer can point to
// lies in the place region of its type (layout.go), with every other such field of
// any struct type and every box: a pointer of type *T may point to any of
// them. A field that no pointer can point to keeps the region of its struct
// type and field, where no write through a pointer to a single value can
// reach it. A field is addressable when
//
//   - it is exported, since any package may take its address;
//   - it is embedded and its type has a method with a pointer receiver,
//     which a call of a promoted method takes the address of, from any
//     package and whatever the case of its name;
//   - its package takes the address of a field of its name: &x.f, a method
//     with a pointer receiver selected on x.f, or a slice of x.f; or
//   - its package may make a pointer to it without naming it: the package
//     imports unsafe, has assembly or cgo files, or holds an expression of
//     type unsafe.Pointer, through which reflect's UnsafePointer and NewAt
//     are reached.
//
// The last two are decided from the files of the package alone, its own
// _test.go files and the files its build constraints leave out included,
// which are read as syntax. Each pass exports the decision as a fact on its
// package, which every package that reads the field looks up by the field's
// package; a package without the fact has every field addressable. A field
// is named by its name only, so a name addressed in one struct of the
// package is addressable in every struct of the package that has it.

// addressedFact is what a package decides of the fields of its structs:
// whether every field is addressable, and otherwise the names of the
// unexported fields whose address the package takes.
type addressedFact struct {
	All   bool
	Names []string
}

func (*addressedFact) AFact() {}

func (f *addressedFact) String() string {
	if f.All {
		return "every field"
	}
	return strings.Join(f.Names, ",")
}

// addressedOf holds the decision of each package by its path, as the
// passes of this process made it or read it from facts.
var addressedOf sync.Map

// hasForeignCode reports whether a package holds code that is not Go:
// assembly, C or another language that cgo builds, or an object file, or
// imports C. Such code can name any symbol of the program.
func hasForeignCode(pass *analysis.Pass) bool {
	for _, name := range pass.OtherFiles {
		switch filepath.Ext(name) {
		case ".s", ".S", ".c", ".h", ".cc", ".cpp", ".cxx", ".m", ".f", ".F", ".for", ".f90", ".syso":
			return true
		}
	}
	for _, file := range pass.Files {
		for _, spec := range file.Imports {
			if spec.Path.Value == `"C"` {
				return true
			}
		}
	}
	return false
}

// scanAddressed reads the files of a package for what makes a field of its
// structs addressable.
func scanAddressed(pass *analysis.Pass) *addressedFact {
	names := map[string]bool{}
	all := false
	for _, imported := range pass.Pkg.Imports() {
		if imported.Path() == "unsafe" {
			all = true
		}
	}
	if hasForeignCode(pass) {
		all = true
	}
	for _, tv := range pass.TypesInfo.Types {
		if tv.Type != nil && types.Identical(tv.Type, types.Typ[types.UnsafePointer]) {
			all = true
		}
	}
	mark := func(e ast.Expr) {
		if sel, ok := ast.Unparen(e).(*ast.SelectorExpr); ok {
			if s := pass.TypesInfo.Selections[sel]; s != nil && s.Kind() == types.FieldVal {
				names[sel.Sel.Name] = true
			}
		}
	}
	for _, file := range pass.Files {
		ast.Inspect(file, func(n ast.Node) bool {
			switch n := n.(type) {
			case *ast.UnaryExpr:
				if n.Op == token.AND {
					mark(n.X)
				}
			case *ast.SliceExpr:
				mark(n.X)
			case *ast.SelectorExpr:
				// A method with a pointer receiver selected on x.f takes
				// the address of x.f, called or as a value.
				s := pass.TypesInfo.Selections[n]
				if s == nil || s.Kind() != types.MethodVal {
					break
				}
				if sig, ok := s.Obj().Type().(*types.Signature); ok && sig.Recv() != nil && isPointerRecv(sig) {
					mark(n.X)
				}
			}
			return true
		})
	}
	// The files read only as syntax: the package's own _test.go files,
	// which the plain build of the package does not hold, and the files
	// its build constraints leave out. Without types, every selector that
	// is addressed or that a selector or a call follows names a field that
	// may be addressed.
	for _, path := range syntaxOnlyFiles(pass) {
		file, err := parser.ParseFile(token.NewFileSet(), path, nil, parser.SkipObjectResolution)
		if err != nil {
			// A file that does not parse is not compiled either, but its
			// fields are not known: decide for every field.
			all = true
			continue
		}
		if file.Name.Name != pass.Pkg.Name() {
			continue
		}
		for _, spec := range file.Imports {
			if spec.Path.Value == `"unsafe"` || spec.Path.Value == `"C"` {
				all = true
			}
		}
		ast.Inspect(file, func(n ast.Node) bool {
			switch n := n.(type) {
			case *ast.UnaryExpr:
				if sel, ok := ast.Unparen(n.X).(*ast.SelectorExpr); ok && n.Op == token.AND {
					names[sel.Sel.Name] = true
				}
			case *ast.SliceExpr:
				if sel, ok := ast.Unparen(n.X).(*ast.SelectorExpr); ok {
					names[sel.Sel.Name] = true
				}
			case *ast.SelectorExpr:
				if inner, ok := ast.Unparen(n.X).(*ast.SelectorExpr); ok {
					names[inner.Sel.Name] = true
				}
				if n.Sel.Name == "UnsafePointer" || n.Sel.Name == "NewAt" {
					all = true
				}
			}
			return true
		})
	}
	fact := &addressedFact{All: all}
	if !all {
		fact.Names = slices.Sorted(func(yield func(string) bool) {
			for name := range names {
				if !yield(name) {
					return
				}
			}
		})
	}
	return fact
}

// isPointerRecv reports whether a method's receiver is a pointer.
func isPointerRecv(sig *types.Signature) bool {
	_, ok := sig.Recv().Type().Underlying().(*types.Pointer)
	return ok
}

// syntaxOnlyFiles returns the Go files of a package's directory that its
// pass does not type-check: its own _test.go files and the files left out
// by build constraints.
func syntaxOnlyFiles(pass *analysis.Pass) []string {
	checked := map[string]bool{}
	dir := ""
	for _, file := range pass.Files {
		name := pass.Fset.File(file.Pos()).Name()
		checked[name] = true
		if dir == "" {
			dir = filepath.Dir(name)
		}
	}
	var out []string
	for _, name := range pass.IgnoredFiles {
		if strings.HasSuffix(name, ".go") && !checked[name] {
			out = append(out, name)
		}
	}
	if dir == "" {
		return out
	}
	entries, err := os.ReadDir(dir)
	if err != nil {
		return out
	}
	for _, entry := range entries {
		name := filepath.Join(dir, entry.Name())
		if strings.HasSuffix(entry.Name(), "_test.go") && !checked[name] && !slices.Contains(out, name) {
			out = append(out, name)
		}
	}
	slices.Sort(out)
	return out
}

// addressedFactOf returns the decision of a package, or nil when it has
// none.
func (pv *pkgVerifier) addressedFactOf(pkg *types.Package) *addressedFact {
	if known, ok := addressedOf.Load(pkg); ok {
		return known.(*addressedFact)
	}
	fact := new(addressedFact)
	// A verifier a test makes by hand has no facts to read.
	if pv.pass == nil || pv.pass.ImportPackageFact == nil || pkg == pv.pass.Pkg || !pv.pass.ImportPackageFact(pkg, fact) {
		return nil
	}
	addressedOf.Store(pkg, fact)
	return fact
}

// hasPointerMethod reports whether a type has a method with a pointer
// receiver, which a call of it on an embedded field promotes.
func hasPointerMethod(t types.Type) bool {
	methods := types.NewMethodSet(types.NewPointer(t))
	for i := range methods.Len() {
		if sig, ok := methods.At(i).Obj().Type().(*types.Signature); ok && sig.Recv() != nil && isPointerRecv(sig) {
			return true
		}
	}
	return false
}
