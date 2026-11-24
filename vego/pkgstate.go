package vego

import (
	"fmt"
	"go/ast"
	"go/types"
	"maps"
	"path/filepath"
	"slices"
	"strconv"
	"strings"

	"golang.org/x/tools/go/types/typeutil"

	"github.com/spachava753/laas/vego/internal/logic"
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
	// Verified is set when the package has a function with annotations,
	// whose contract may speak of its unexported variables.
	Verified bool
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
	verified := slices.ContainsFunc(pv.order, func(fn *funcInfo) bool { return fn.annotated() })
	pv.pass.ExportPackageFact(&coversFact{Covers: pv.ownCovers, Verified: verified})
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
		case path == home.Path() && spelled.trust != nil:
			// A trusted function may change the variables of its own
			// package, which its entry cannot name one by one.
			return home, true, nil
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
			form, t, err := v.variableTargetAny(fn, whole, variable, nil, sink, mem)
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
		// The state of a package covers its variables, and names none of
		// them by itself.
		targets[i].text, targets[i].clause, targets[i].also, targets[i].fromVar = m.text, m.clause, nil, nil
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

// writesFact holds, for a function with a body, the package-level
// variables, by key, that its body assigns, or a function it calls by name
// does, with where for each: the check of a trusted entry reads it (F10 of
// the design review).
type writesFact struct {
	Keys map[string]string
	// Through holds the variables that refer to memory and that a use in
	// the body, or in a function it calls by name, lets a reference out
	// of, which may be a write of what they refer to.
	Through map[string]bool
}

func (*writesFact) AFact() {}

func (f *writesFact) String() string { return fmt.Sprintf("writes(%d)", len(f.Keys)) }

// exportWrites publishes, for every function of the package with a body,
// the package-level variables it assigns, directly, through their paths,
// or through the functions it calls by name, in this package or, by their
// facts, in others. A call with no static callee reaches what the call
// graph's rule says it may (F25 of the review of step 4): a call through a
// function value, every function, method value, and literal of the package
// used as a value of an identical signature, and every exported function
// of it; a call of an interface method, every method of that name and
// signature of the package.
func (pv *pkgVerifier) exportWrites() {
	type writes struct {
		keys    map[string]string
		through map[string]bool
		calls   []*types.Func
		// values and methods are the signatures of the calls with no
		// static callee, through a value and of a method by name.
		values  []*types.Signature
		methods []*types.Func
	}
	newWrites := func() *writes { return &writes{keys: map[string]string{}, through: map[string]bool{}} }
	byFunc := map[*types.Func]*writes{}
	byLit := map[*ast.FuncLit]*writes{}
	asValue := map[*types.Func]bool{}
	for _, file := range pv.pass.Files {
		var stack []ast.Node
		var current []*writes
		owner := map[ast.Node]bool{}
		// The parameters of the enclosing declared function that its
		// trusted entry lists under runs: the code they carry is the
		// caller's, which the caller counts at the call (F27 of the review
		// of the end of part 1).
		var handed map[*types.Var]bool
		ast.Inspect(file, func(n ast.Node) bool {
			if n == nil {
				if owner[stack[len(stack)-1]] {
					current = current[:len(current)-1]
				}
				stack = stack[:len(stack)-1]
				return true
			}
			stack = append(stack, n)
			switch n := n.(type) {
			case *ast.FuncDecl:
				if obj, ok := pv.info.Defs[n.Name].(*types.Func); ok && n.Body != nil {
					w := newWrites()
					byFunc[obj] = w
					current = append(current, w)
					owner[n] = true
					handed = map[*types.Var]bool{}
					if entry := pv.entryFor(obj.FullName()); entry != nil {
						sig := obj.Type().(*types.Signature)
						params := slices.Collect(sig.Params().Variables())
						if sig.Recv() != nil {
							params = append(params, sig.Recv())
						}
						for _, item := range entry.runs {
							for _, param := range params {
								if param.Name() == item.text {
									handed[param] = true
								}
							}
						}
						pv.handedLocals(n.Body, handed)
					}
				}
			case *ast.FuncLit:
				// A literal's writes are its function's too, and its own as
				// a value a call may reach.
				w := newWrites()
				byLit[n] = w
				current = append(current, w)
				owner[n] = true
			case *ast.CallExpr:
				callee, _ := typeutil.Callee(pv.info, n).(*types.Func)
				for _, w := range current {
					switch {
					case callee != nil && isIfaceMethod(callee):
						w.methods = append(w.methods, callee)
					case callee != nil:
						w.calls = append(w.calls, callee.Origin())
					default:
						if root := pv.rootVar(n.Fun); root != nil && handed[root] {
							break
						}
						if tv, ok := pv.info.Types[n.Fun]; ok && !tv.IsType() && !tv.IsBuiltin() {
							if sig, ok := tv.Type.Underlying().(*types.Signature); ok {
								w.values = append(w.values, sig)
							}
						}
					}
				}
			case *ast.Ident:
				if named, ok := pv.info.Uses[n].(*types.Func); ok && !calledAt(stack) {
					asValue[named.Origin()] = true
				}
				variable, ok := pv.info.Uses[n].(*types.Var)
				if !ok || variable.Pkg() == nil || variable.Parent() != variable.Pkg().Scope() {
					break
				}
				use := pv.useOf(stack)
				key := errorKey(variable)
				for _, w := range current {
					switch {
					case use.change != "" || pathWritten(pv.info, stack):
						if _, seen := w.keys[key]; !seen {
							position := pv.pass.Fset.Position(n.Pos())
							w.keys[key] = fmt.Sprintf("%s:%d", filepath.Base(position.Filename), position.Line)
						}
					case use.escape && holdsMemory(variable.Type()) && !isError(variable.Type()):
						w.through[key] = true
					}
				}
			}
			return true
		})
	}
	// What a call with no static callee may reach, indexed once by
	// signature and in the order of the source.
	funcs := slices.SortedFunc(maps.Keys(byFunc), func(a, b *types.Func) int { return int(a.Pos() - b.Pos()) })
	lits := slices.SortedFunc(maps.Keys(byLit), func(a, b *ast.FuncLit) int { return int(a.Pos() - b.Pos()) })
	byValueSig := map[string][]*writes{}
	byMethod := map[string][]*writes{}
	for _, obj := range funcs {
		objSig := obj.Type().(*types.Signature)
		key := sigKey(objSig)
		if objSig.Recv() != nil {
			byMethod[obj.Name()+" "+key] = append(byMethod[obj.Name()+" "+key], byFunc[obj])
		}
		if asValue[obj] || obj.Exported() && objSig.Recv() == nil {
			byValueSig[key] = append(byValueSig[key], byFunc[obj])
		}
	}
	for _, lit := range lits {
		if litSig, ok := pv.info.TypeOf(lit).(*types.Signature); ok {
			key := sigKey(litSig)
			byValueSig[key] = append(byValueSig[key], byLit[lit])
		}
	}
	reachValue := func(sig *types.Signature) []*writes {
		return byValueSig[sigKey(sig)]
	}
	reachMethod := func(method *types.Func) []*writes {
		return byMethod[method.Name()+" "+sigKey(method.Type().(*types.Signature))]
	}
	// To a fixed point; a call of a function of another package brings
	// what its fact says.
	merge := func(into *writes, keys map[string]string, through map[string]bool, via string) bool {
		changed := false
		for key, at := range keys {
			if _, seen := into.keys[key]; !seen {
				into.keys[key] = at + via
				changed = true
			}
		}
		for key := range through {
			if !into.through[key] {
				into.through[key] = true
				changed = true
			}
		}
		return changed
	}
	// In the order of the source, so that where a write is said to be is
	// the same in every run.
	var everyone []*writes
	for _, obj := range funcs {
		everyone = append(everyone, byFunc[obj])
	}
	for _, lit := range lits {
		everyone = append(everyone, byLit[lit])
	}
	for changed := true; changed; {
		changed = false
		for _, w := range everyone {
			for _, callee := range w.calls {
				if callee.Pkg() == pv.pass.Pkg {
					if theirs := byFunc[callee]; theirs != nil && merge(w, theirs.keys, theirs.through, " in "+callee.Name()) {
						changed = true
					}
				} else if fact := new(writesFact); pv.pass.ImportObjectFact(callee, fact) && merge(w, fact.Keys, fact.Through, " in "+callee.Name()) {
					changed = true
				}
			}
			for _, sig := range w.values {
				for _, theirs := range reachValue(sig) {
					if theirs != w && merge(w, theirs.keys, theirs.through, " in code that a call through a value may run") {
						changed = true
					}
				}
			}
			for _, method := range w.methods {
				for _, theirs := range reachMethod(method) {
					if theirs != w && merge(w, theirs.keys, theirs.through, " in a method "+method.Name()+" that a call may run") {
						changed = true
					}
				}
			}
		}
	}
	for obj, w := range byFunc {
		if len(w.keys) > 0 || len(w.through) > 0 {
			pv.pass.ExportObjectFact(obj, &writesFact{Keys: w.keys, Through: w.through})
		}
	}
}

// calledAt reports whether the name at the end of stack is the function of
// a call, as opposed to a function used as a value.
func calledAt(stack []ast.Node) bool {
	var cur ast.Node = stack[len(stack)-1]
	for i := len(stack) - 2; i >= 0; i-- {
		switch parent := stack[i].(type) {
		case *ast.SelectorExpr:
			if parent.Sel != cur {
				return false
			}
			cur = parent
		case *ast.ParenExpr, *ast.IndexExpr, *ast.IndexListExpr:
			cur = parent
		case *ast.CallExpr:
			return parent.Fun == cur
		default:
			return false
		}
	}
	return false
}

// pathWritten reports whether the use at the end of stack is the root of a
// path that a statement writes, as in table[0] = 5, cfg.n++, or
// delete(m, k): a write of what the variable refers to, as distinct from a
// use that hands a reference on.
func pathWritten(info *types.Info, stack []ast.Node) bool {
	cur := stack[len(stack)-1].(ast.Expr)
	i := len(stack) - 2
	if i >= 0 {
		if sel, ok := stack[i].(*ast.SelectorExpr); ok && sel.Sel == cur {
			cur, i = sel, i-1
		}
	}
	moved := false
	for ; i >= 0; i-- {
		switch parent := stack[i].(type) {
		case *ast.ParenExpr:
			cur = parent
			continue
		case *ast.SelectorExpr:
			if parent.X != cur {
				return false
			}
			cur, moved = parent, true
			continue
		case *ast.IndexExpr:
			if parent.X != cur {
				return false
			}
			cur, moved = parent, true
			continue
		case *ast.StarExpr:
			cur, moved = parent, true
			continue
		case *ast.AssignStmt:
			return moved && slices.Contains(parent.Lhs, cur)
		case *ast.IncDecStmt:
			return moved && parent.X == cur
		case *ast.RangeStmt:
			return moved && (parent.Key == cur || parent.Value == cur)
		case *ast.CallExpr:
			id, ok := ast.Unparen(parent.Fun).(*ast.Ident)
			if builtin, isBuiltin := info.Uses[id].(*types.Builtin); ok && isBuiltin && (builtin.Name() == "delete" || builtin.Name() == "clear") {
				return len(parent.Args) > 0 && parent.Args[0] == cur
			}
			return false
		default:
			return false
		}
	}
	return false
}

// checkTrustedWrites reports a call of a trusted function whose body, or
// a function it calls by name, assigns a package-level variable that a
// proof can read, or writes through its path, when the entry's modifies
// does not cover it: the entry would be false of what the call does, and
// every caller above would keep the variable (F10 of the design review,
// F24 of the review of step 4). It reports at every use of the entry.
func (v *fnVerifier) checkTrustedWrites(call *ast.CallExpr, fn *funcInfo, written []target) {
	if fn.trust == nil || fn.obj == nil {
		return
	}
	fact := new(writesFact)
	if !v.pass.ImportObjectFact(fn.obj.Origin(), fact) {
		return
	}
	for _, key := range slices.Sorted(maps.Keys(fact.Keys)) {
		variable := v.lookupKey(key)
		if variable == nil || isError(variable.Type()) {
			continue
		}
		if variable.Pkg() != v.pass.Pkg && !variable.Exported() {
			covers := new(coversFact)
			if !v.pass.ImportPackageFact(variable.Pkg(), covers) || !covers.Verified {
				continue
			}
		}
		var covered func(t target) bool
		switch {
		case v.isAssigned(variable):
			key := v.globalCells(variable)[0].key
			covered = func(t target) bool { return slices.ContainsFunc(t.cells, func(c cell) bool { return c.key == key }) }
		default:
			// A fixed variable whose memory the body writes through its
			// path: a target at its reference covers it.
			if _, why := v.usableFixed(variable); why != "" || !holdsMemory(variable.Type()) {
				continue
			}
			val, why := v.fixedValue(nil, variable)
			if why != "" {
				continue
			}
			covered = func(t target) bool { return t.ref != nil && t.ref.Op == logic.OpConst && t.ref.Name == val[0].Name }
		}
		if slices.ContainsFunc(written, covered) {
			continue
		}
		entry := strconv.Quote(strconv.Quote(variable.Pkg().Path()))
		if variable.Pkg() == fn.obj.Pkg() {
			entry = variable.Name()
		}
		v.report(call.Pos(), "the trusted contract of %s does not list %s, which its body writes at %s; an entry lists what its function changes, "+
			"as in modifies: [%s]", fn.obj.Name(), v.spelling(variable), fact.Keys[key], entry)
	}
}

// notImported says, for a Modifies entry that starts with the name of a
// package the contract's package depends on but no file of it imports,
// what to write instead (F23 of the review of step 3).
func (pv *pkgVerifier) notImported(fn *funcInfo, m *modTarget) string {
	home := fn.spelling().obj.Pkg()
	if home == nil || fn.spelling().imported != nil || fn.spelling().trust != nil {
		return ""
	}
	var found []*types.Package
	seen := map[*types.Package]bool{}
	var walk func(p *types.Package)
	walk = func(p *types.Package) {
		for _, imported := range p.Imports() {
			if seen[imported] {
				continue
			}
			seen[imported] = true
			if imported.Name() == m.name {
				found = append(found, imported)
			}
			walk(imported)
		}
	}
	walk(home)
	if len(found) != 1 {
		return ""
	}
	return fmt.Sprintf("%s is not imported by the files of package %s; name the state of a package it imports whose state covers it, or write the import path, as // @Modifies %s",
		m.name, home.Path(), strconv.Quote(found[0].Path()))
}

// fixedVariableAt returns the fixed variable whose value is the reference,
// or nil.
func (v *fnVerifier) fixedVariableAt(ref *logic.Term) *types.Var {
	if ref == nil || ref.Op != logic.OpConst {
		return nil
	}
	for key, met := range v.fixedMet {
		if len(met.val) > 0 && met.val[0].Name == ref.Name {
			return v.lookupKey(key)
		}
	}
	return nil
}

// rootVar returns the variable a path of fields, elements, and pointers
// starts from, or nil.
func (pv *pkgVerifier) rootVar(e ast.Expr) *types.Var {
	for {
		switch x := ast.Unparen(e).(type) {
		case *ast.Ident:
			variable, _ := pv.info.Uses[x].(*types.Var)
			return variable
		case *ast.SelectorExpr:
			e = x.X
		case *ast.IndexExpr:
			e = x.X
		case *ast.StarExpr:
			e = x.X
		default:
			return nil
		}
	}
}

// handedLocals adds to handed the local variables of a body that hold
// what is read from a handed variable: assigned or ranged from a path that
// starts at one, to a fixed point.
func (pv *pkgVerifier) handedLocals(body *ast.BlockStmt, handed map[*types.Var]bool) {
	local := func(e ast.Expr) *types.Var {
		id, ok := ast.Unparen(e).(*ast.Ident)
		if !ok {
			return nil
		}
		variable, _ := pv.info.ObjectOf(id).(*types.Var)
		if variable == nil || variable.Parent() == nil || variable.Pkg() == nil || variable.Parent() == variable.Pkg().Scope() {
			return nil
		}
		return variable
	}
	for changed := true; changed; {
		changed = false
		mark := func(target ast.Expr) {
			if variable := local(target); variable != nil && !handed[variable] {
				handed[variable] = true
				changed = true
			}
		}
		ast.Inspect(body, func(n ast.Node) bool {
			switch n := n.(type) {
			case *ast.AssignStmt:
				if len(n.Lhs) == len(n.Rhs) {
					for i, rhs := range n.Rhs {
						if root := pv.rootVar(rhs); root != nil && handed[root] {
							mark(n.Lhs[i])
						}
					}
				}
			case *ast.RangeStmt:
				if root := pv.rootVar(n.X); root != nil && handed[root] {
					if n.Key != nil {
						mark(n.Key)
					}
					if n.Value != nil {
						mark(n.Value)
					}
				}
			}
			return true
		})
	}
}

// sigKey spells a signature without its receiver and the names of its
// parameters and results, so that signatures that types.Identical takes
// for one spell the same.
func sigKey(sig *types.Signature) string {
	var b strings.Builder
	tuple := func(t *types.Tuple) {
		b.WriteString("(")
		for i := range t.Len() {
			b.WriteString(types.TypeString(t.At(i).Type(), nil))
			b.WriteString(";")
		}
		b.WriteString(")")
	}
	tuple(sig.Params())
	tuple(sig.Results())
	if sig.Variadic() {
		b.WriteString("...")
	}
	return b.String()
}
