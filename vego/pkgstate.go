package vego

import (
	"fmt"
	"go/ast"
	"go/types"
	"slices"
	"strconv"
	"strings"
)

// The state of a package (D1 of package-level variables). A Modifies entry
// may name the state of a package other than the function's own, by the
// name the package imports it as or by its import path as a string. It
// covers every variable the package declares, what those refer to, and the
// states that the package's functions list, transitively: covers(P) is P
// with covers(Q) for every package Q whose state or exported variable a
// contract of P lists, published as coversFact. So a caller covers a write
// by naming a package it imports, whose function's frame lists the state,
// or by the path of a package it depends on.

// coversFact is what the state of a package covers: the paths of the
// packages whose variables a function of the package may change.
type coversFact struct {
	Covers []string
}

func (*coversFact) AFact() {}

func (f *coversFact) String() string { return fmt.Sprintf("covers(%s)", strings.Join(f.Covers, ", ")) }

// covers returns the paths of the packages whose variables a function of
// pkg may change.
func (pv *pkgVerifier) covers(pkg *types.Package) []string {
	if pkg == pv.pass.Pkg {
		if pv.ownCovers == nil {
			pv.ownCovers = []string{pkg.Path()}
		}
		return pv.ownCovers
	}
	fact := new(coversFact)
	if !pv.pass.ImportPackageFact(pkg, fact) {
		return []string{pkg.Path()}
	}
	return fact.Covers
}

// exportCovers computes what the state of this package covers from the
// Modifies entries of its contracts and publishes it.
func (pv *pkgVerifier) exportCovers() {
	found := map[string]bool{pv.pass.Pkg.Path(): true}
	for _, fn := range pv.order {
		for _, m := range fn.modifies {
			var other *types.Package
			if pkg, named, err := pv.modifiesPackage(fn, m); named && err == nil {
				other = pkg
			} else if variable := pv.modifiesVariableOf(fn, m); variable != nil && variable.Pkg() != pv.pass.Pkg {
				other = variable.Pkg()
			}
			if other != nil {
				for _, path := range pv.covers(other) {
					found[path] = true
				}
			}
		}
	}
	pv.ownCovers = slices.Sorted(func(yield func(string) bool) {
		for path := range found {
			if !yield(path) {
				return
			}
		}
	})
	pv.pass.ExportPackageFact(&coversFact{Covers: pv.ownCovers})
}

// dependency returns the package with the given path among those pkg
// depends on, at any depth, or nil.
func dependency(pkg *types.Package, path string) *types.Package {
	seen := map[*types.Package]bool{}
	var walk func(p *types.Package) *types.Package
	walk = func(p *types.Package) *types.Package {
		for _, imported := range p.Imports() {
			if seen[imported] {
				continue
			}
			seen[imported] = true
			if imported.Path() == path {
				return imported
			}
			if found := walk(imported); found != nil {
				return found
			}
		}
		return nil
	}
	return walk(pkg)
}

// modifiesPackage resolves a Modifies entry that names the state of a
// package: a string, which is an import path, or a name with no path after
// it that the contract's file, or another file of its package, imports.
// named is set when the entry names a package, and then err says what is
// wrong with it.
func (pv *pkgVerifier) modifiesPackage(fn *funcInfo, m *modTarget) (pkg *types.Package, named bool, err error) {
	spelled := fn.spelling()
	home := spelled.obj.Pkg()
	if home == nil {
		return nil, false, nil
	}
	resolve := func(path, text string) (*types.Package, bool, error) {
		switch found := dependency(home, path); {
		case path == home.Path():
			return nil, true, fmt.Errorf("%s is the package of %s, whose variables a Modifies clause names one by one", text, spelled.obj.Name())
		case found == nil:
			return nil, true, fmt.Errorf("%s is not among the packages that package %s depends on, so what its state covers is not known here", text, home.Path())
		default:
			return found, true, nil
		}
	}
	if m.pkgPath != "" {
		return resolve(m.pkgPath, strconv.Quote(m.pkgPath))
	}
	if len(m.steps) > 0 || m.behind {
		return nil, false, nil
	}
	if fn.paramNames[m.name] != nil {
		return nil, false, nil
	}
	if imported := spelled.imported; imported != nil {
		path, ok := imported.Packages[m.name]
		if !ok {
			return nil, false, nil
		}
		return resolve(path, m.name)
	}
	if spelled.decl == nil || home != pv.pass.Pkg {
		return nil, false, nil
	}
	// The contract's own file first, as Go resolves the name there.
	if scope := home.Scope().Innermost(spelled.decl.Pos()); scope != nil {
		switch _, obj := scope.LookupParent(m.name, spelled.decl.Pos()); obj := obj.(type) {
		case *types.PkgName:
			return resolve(obj.Imported().Path(), m.name)
		case nil:
		default:
			return nil, false, nil
		}
	}
	// Then the imports of the package's other files.
	var paths []string
	for _, file := range pv.pass.Files {
		for _, spec := range file.Imports {
			if obj := pv.importedAs(spec); obj != nil && obj.Name() == m.name && !slices.Contains(paths, obj.Imported().Path()) {
				paths = append(paths, obj.Imported().Path())
			}
		}
	}
	switch len(paths) {
	case 0:
		return nil, false, nil
	case 1:
		return resolve(paths[0], m.name)
	}
	slices.Sort(paths)
	quoted := make([]string, len(paths))
	for i, path := range paths {
		quoted[i] = strconv.Quote(path)
	}
	return nil, true, fmt.Errorf("%s names more than one package in the files of this package (%s), and the file of %s imports none of them; "+
		"write the import path, as // @Modifies %s", m.name, strings.Join(quoted, " and "), spelled.obj.Name(), quoted[0])
}

// importedAs returns the name an import declares in its file.
func (pv *pkgVerifier) importedAs(spec *ast.ImportSpec) *types.PkgName {
	if spec.Name != nil {
		obj, _ := pv.info.Defs[spec.Name].(*types.PkgName)
		return obj
	}
	obj, _ := pv.info.Implicits[spec].(*types.PkgName)
	return obj
}

// stateTarget locates the state of a package: a target for each variable
// of each package it covers that verified code can write, the storage of
// an assigned variable and what it refers to, and what a fixed variable
// refers to. They are the target and its also.
func (v *fnVerifier) stateTarget(fn *funcInfo, m *modTarget, pkg *types.Package, sink *state, mem memory) (shape, target, error) {
	var forms []shape
	var targets []target
	for _, path := range v.covers(pkg) {
		covered := pkg
		if path != pkg.Path() {
			covered = dependency(v.pass.Pkg, path)
			if covered == nil {
				covered = dependency(pkg, path)
			}
		}
		if covered == nil {
			continue
		}
		scope := covered.Scope()
		for _, name := range scope.Names() {
			variable, ok := scope.Lookup(name).(*types.Var)
			if !ok || isError(variable.Type()) {
				continue
			}
			if !v.isAssigned(variable) {
				if v.reassigned[variable] || !holdsMemory(variable.Type()) {
					continue
				}
				if _, why := v.usableFixed(variable); why != "" {
					continue
				}
			}
			whole := &modTarget{name: name, text: m.text, clause: m.clause}
			form, t, err := v.variableTargetAny(fn, whole, variable, sink, mem)
			if err != nil {
				continue
			}
			forms = append(forms, append([]shape{form}, form.also...)...)
			targets = append(targets, append([]target{t}, t.also...)...)
		}
	}
	if len(targets) == 0 {
		return shape{}, target{text: m.text, clause: m.clause}, nil
	}
	for i := range targets {
		targets[i].text, targets[i].clause, targets[i].also = m.text, m.clause, nil
	}
	for i := range forms {
		forms[i].also = nil
	}
	first, rest := forms[0], forms[1:]
	first.also = rest
	t := targets[0]
	t.also = targets[1:]
	return first, t, nil
}

// variableOfCells returns the assigned variable whose storage the cells
// are, or nil.
func (v *fnVerifier) variableOfCells(cells []cell) *types.Var {
	if len(cells) == 0 || !isVarRegion(cells[0].key) {
		return nil
	}
	for _, variable := range v.assignedMet {
		for _, c := range v.globalCells(variable) {
			if c.key == cells[0].key {
				return variable
			}
		}
	}
	return nil
}

// stateRemedy says, for a call whose callee may change a variable of
// another package, what the call changes and the shortest entry that the
// caller's file can write to cover it: the variable's package if the file
// imports it, else the callee's package if its state covers it, else the
// path of the variable's package.
func (v *fnVerifier) stateRemedy(variable *types.Var, callee *funcInfo) (what, remedy string) {
	pkg := variable.Pkg()
	what = fmt.Sprintf("the state of package %s (%s)", pkg.Path(), v.spelling(variable))
	// The name the contract's file imports a package as, or else the one
	// name the other files of the package import it as, which
	// modifiesPackage resolves the same way.
	importedAs := func(p *types.Package) string {
		var files []*ast.File
		if v.fn.decl != nil {
			for _, file := range v.pass.Files {
				if file.FileStart <= v.fn.decl.Pos() && v.fn.decl.Pos() <= file.FileEnd {
					files = append(files, file)
				}
			}
		}
		for _, group := range [][]*ast.File{files, v.pass.Files} {
			var names []string
			for _, file := range group {
				for _, spec := range file.Imports {
					if obj := v.importedAs(spec); obj != nil && obj.Imported() == p && !slices.Contains(names, obj.Name()) {
						names = append(names, obj.Name())
					}
				}
			}
			if len(names) == 1 {
				if pkg, _, err := v.modifiesPackage(v.fn, &modTarget{name: names[0]}); err == nil && pkg == p {
					return names[0]
				}
			}
		}
		return ""
	}
	if name := importedAs(pkg); name != "" {
		return what, fmt.Sprintf("list %s in a // @Modifies clause", name)
	}
	if home := callee.obj.Pkg(); home != nil && home != v.pass.Pkg && slices.Contains(v.covers(home), pkg.Path()) {
		if name := importedAs(home); name != "" {
			return what, fmt.Sprintf("list %s, whose state includes it, in a // @Modifies clause", name)
		}
	}
	return what, fmt.Sprintf("list %s in a // @Modifies clause", strconv.Quote(pkg.Path()))
}
