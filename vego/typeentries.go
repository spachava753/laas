package vego

import (
	"fmt"
	"go/token"
	"go/types"
	"os"
	"path/filepath"
	"strings"
)

// A type of another package has nowhere to put a contract: io.Writer is
// declared in package io, which vego does not annotate. An entry of the
// trust file gives one, to a method of an interface type, keyed as Go
// prints the method, (io.Writer).Write, or to a function type, keyed as Go
// prints the type, context.CancelFunc. Such an entry is a contract of the
// type like one written in source (see interfaces.go and funcvalues.go), and
// is checked like one, but it is a claim: every value of the type that code
// which is not verified hands to verified code meets it, whatever
// implementation the value holds. A value that verified code makes is
// checked against it where it is made. A trusted function that returns such
// a value, or writes one, vouches for it in its own entry.
//
// An entry may give a contract only to a type of another module. A type of
// the module of the analysed package can carry its contract in source,
// where it is declared, and one thing would otherwise have two spellings.

// typeEntry returns the contract that the trust files give a method of an
// interface type or a function type, or nil when they give none. The
// contract is read and checked once per package; a fault in it is a defect,
// reported where it is used. Looking it up records that the proofs of the
// package rely on it, so that two entries for one type in a build are
// found (see the check of fingerprints), whatever made the proof look. An
// entry that cannot be used is not recorded: every use of it is an error.
func (pv *pkgVerifier) typeEntry(key string, obj *types.Func, methodOf *types.Func, valueOf *types.TypeName) *funcInfo {
	if fn, done := pv.typeEntries[key]; done {
		return fn
	}
	pv.typeEntries[key] = nil
	entry := pv.entryFor(key)
	if entry == nil {
		return nil
	}
	fn := newFuncInfo(obj)
	fn.trust, fn.methodOf, fn.valueOf = entry, methodOf, valueOf
	pv.typeEntries[key] = fn
	declared, pkg := obj.Pos(), obj.Pkg()
	if valueOf != nil {
		declared, pkg = valueOf.Pos(), valueOf.Pkg()
	}
	if pv.inAnalysedModule(pkg, declared) {
		what := "the method " + key
		if valueOf != nil {
			what = "the function type " + key
		}
		fn.defect("%s is declared in the module of this package; write its contract in the doc comment where it is declared", what)
	}
	pv.readEntry(fn, entry)
	// What a call through the value is handed is refused when it can
	// carry code nobody has seen, so nothing is left for runs or calls to
	// say.
	if len(entry.runs) > 0 {
		fn.defect("it lists runs, which a contract of a type cannot have: a call through a value of the type is never handed code nobody has seen")
	}
	if len(entry.calls) > 0 {
		fn.defect("it has calls, which a contract of a type cannot have")
	}
	pv.readVouches(fn, entry, false)
	pv.checkValueContract(fn)
	// A contract that cannot be used makes every use of it an error, so
	// no proof rests on it.
	if !fn.broken {
		pv.noteUse(fn, token.NoPos)
	}
	return fn
}

// funcTypeKey is the key of the entry for a function type, as Go prints the
// type: context.CancelFunc.
func funcTypeKey(name *types.TypeName) string {
	return name.Pkg().Path() + "." + name.Name()
}

// entryMethod returns the contract an entry gives a method of a defined
// interface type declared at package level without type parameters, the
// only interfaces a contract can be written on.
func (pv *pkgVerifier) entryMethod(method *types.Func) *funcInfo {
	recv := method.Type().(*types.Signature).Recv()
	if recv == nil || method.Pkg() == nil {
		return nil
	}
	named, ok := types.Unalias(recv.Type()).(*types.Named)
	if !ok || named.TypeParams() != nil || named.Obj().Parent() != method.Pkg().Scope() {
		return nil
	}
	return pv.typeEntry(method.FullName(), withoutReceiver(method), method, nil)
}

// entryFuncType returns the contract an entry gives a defined function type
// declared at package level without type parameters.
func (pv *pkgVerifier) entryFuncType(name *types.TypeName) *funcInfo {
	named, ok := name.Type().(*types.Named)
	if !ok || name.IsAlias() || name.Pkg() == nil || named.TypeParams() != nil || name.Parent() != name.Pkg().Scope() {
		return nil
	}
	sig := name.Type().Underlying().(*types.Signature)
	return pv.typeEntry(funcTypeKey(name), types.NewFunc(name.Pos(), name.Pkg(), name.Name(), sig), nil, name)
}

// typeKeyProblem looks at the key of a project entry that may name a method
// of an interface type, as in (io.Writer).Write, or a function type, as in
// context.CancelFunc. It reports whether the key names a type at all, and
// what is wrong with it, or "".
func (pv *pkgVerifier) typeKeyProblem(pkg *types.Package, key, name string) (isType bool, problem string) {
	receiver, method, isMethod := strings.Cut(strings.TrimPrefix(name, "("), ").")
	if !isMethod {
		typeName, ok := pkg.Scope().Lookup(name).(*types.TypeName)
		if !ok {
			return false, ""
		}
		named, isNamed := typeName.Type().(*types.Named)
		_, isFunc := typeName.Type().Underlying().(*types.Signature)
		switch {
		case !isFunc && types.IsInterface(typeName.Type()):
			return true, fmt.Sprintf("the trusted contract names %s, an interface type; give the contract to each of its methods, as in (%s).M", key, key)
		case !isFunc:
			return true, fmt.Sprintf("the trusted contract names %s, a type that is not a function type, which cannot have a contract", key)
		case typeName.IsAlias() || !isNamed:
			return true, fmt.Sprintf("the trusted contract names %s, an alias; key the entry by the defined function type", key)
		case named.TypeParams() != nil:
			return true, fmt.Sprintf("the trusted contract names %s, a function type with type parameters, which cannot have a contract yet", key)
		case pv.inAnalysedModule(pkg, typeName.Pos()):
			return true, fmt.Sprintf("the trusted contract names %s, a function type of the module of this package; "+
				"write its contract in the doc comment where it is declared", key)
		}
		return true, ""
	}
	typeName, ok := pkg.Scope().Lookup(receiver).(*types.TypeName)
	if !ok || !types.IsInterface(typeName.Type()) {
		return false, ""
	}
	found, _, _ := types.LookupFieldOrMethod(typeName.Type(), false, pkg, method)
	declared, ok := found.(*types.Func)
	named, isNamed := types.Unalias(typeName.Type()).(*types.Named)
	switch {
	case !ok:
		return true, fmt.Sprintf("the trusted contract names %s, but %s has no method %s", key, receiver, method)
	case isNamed && named.TypeParams() != nil:
		return true, fmt.Sprintf("the trusted contract names %s, a method of an interface type with type parameters, which cannot have a contract yet", key)
	case declared.FullName() != key:
		// An alias, an interface that embeds another, and a type defined
		// from another all have the method of the declaration, whose key
		// is the only one looked up.
		return true, fmt.Sprintf("the trusted contract names %s, but %s has %s from %s; key the entry %s", key, receiver, method, declared.FullName(), declared.FullName())
	case pv.inAnalysedModule(pkg, typeName.Pos()):
		return true, fmt.Sprintf("the trusted contract names %s, a method of an interface type of the module of this package; "+
			"write its contract in the doc comment of the method where the interface is declared", key)
	}
	return true, ""
}

// inAnalysedModule reports whether a package, declared at a position,
// belongs to the module of the analysed package. A module is the tree under
// its go.mod, apart from nested modules, which have a go.mod of their own.
// A vendored package lies under the go.mod of the module that vendors it,
// since go mod vendor copies no go.mod, so the module path decides as well
// where the driver knows it: a package is in the module when its import
// path is the module path or lies under it.
func (pv *pkgVerifier) inAnalysedModule(pkg *types.Package, declared token.Pos) bool {
	if pkg == pv.pass.Pkg {
		return true
	}
	if pkg == nil || len(pv.pass.Files) == 0 {
		return false
	}
	module := ""
	if pv.pass.Module != nil {
		module = pv.pass.Module.Path
	}
	goMod := nearestGoMod(pv.pass.Fset.Position(declared).Filename)
	path := pkg.Path()
	return goMod != "" && goMod == nearestGoMod(pv.pass.Fset.Position(pv.pass.Files[0].Pos()).Filename) &&
		(module == "" || path == module || strings.HasPrefix(path, module+"/"))
}

// nearestGoMod returns the go.mod nearest above a source file, or "".
func nearestGoMod(file string) string {
	if file == "" {
		return ""
	}
	for dir := filepath.Dir(file); ; dir = filepath.Dir(dir) {
		if _, err := os.Stat(filepath.Join(dir, "go.mod")); err == nil {
			return filepath.Join(dir, "go.mod")
		}
		if dir == filepath.Dir(dir) {
			return ""
		}
	}
}

// usable reports the defects of the contract of a type or of a method of an
// interface where it is used, and stops the verification when it cannot be
// used. A contract that a trust file gives a type of another package is
// named as its entry, and its use is recorded for the trust report.
func (v *fnVerifier) usable(pos token.Pos, fn *funcInfo, title string) {
	for _, defect := range fn.defects {
		if fn.trust != nil {
			v.report(pos, "the trusted contract of %s (%s:%d) cannot be used: %s", fn.trust.key, filepath.Base(fn.trust.file.path), fn.trust.line, defect)
			continue
		}
		v.report(pos, "the contract of %s cannot be used: %s", title, defect)
	}
	if fn.broken {
		v.unsupported(pos, fmt.Sprintf("the contract of %s could not be understood", title))
	}
	if fn.trust != nil {
		v.noteUse(fn, pos)
	}
}

// entryHint tells, in a message about a method of an interface or a
// function type without a contract, how a type of another module gets one:
// by an entry of the trust file with the key given.
func (pv *pkgVerifier) entryHint(pkg *types.Package, declared token.Pos, key string) string {
	if pkg == nil || pv.inAnalysedModule(pkg, declared) {
		return ""
	}
	return fmt.Sprintf("; for a type of another module, give it an entry %s in %s", key, TrustFileName)
}

// funcTypeHint is entryHint for a function type, which must be a defined
// type at package level.
func (pv *pkgVerifier) funcTypeHint(t types.Type) string {
	named, ok := t.(*types.Named)
	if !ok || named.Obj().Pkg() == nil || named.Obj().Parent() != named.Obj().Pkg().Scope() || named.TypeParams() != nil {
		return ""
	}
	return pv.entryHint(named.Obj().Pkg(), named.Obj().Pos(), funcTypeKey(named.Obj()))
}

// noteEntriesIn records that a proof rests on the entries that give
// contracts to the types a value of type t can hold, however deep: a value
// handed on there is believed to meet them.
func (v *fnVerifier) noteEntriesIn(t types.Type, at token.Pos) {
	seen := map[types.Type]bool{}
	var visit func(t types.Type)
	visit = func(t types.Type) {
		if t == nil || seen[t] {
			return
		}
		seen[t] = true
		switch u := t.Underlying().(type) {
		case *types.Interface:
			if isIface(t) {
				for method := range u.Methods() {
					if fn := v.methodContract(method); fn != nil && fn.trust != nil && !fn.broken {
						v.noteUse(fn, at)
					}
				}
			}
		case *types.Signature:
			if fn := v.valueContract(t); fn != nil && fn.trust != nil && !fn.broken {
				v.noteUse(fn, at)
			}
		case *types.Pointer:
			visit(u.Elem())
		case *types.Slice:
			visit(u.Elem())
		case *types.Array:
			visit(u.Elem())
		case *types.Map:
			visit(u.Key())
			visit(u.Elem())
		case *types.Struct:
			for field := range u.Fields() {
				visit(field.Type())
			}
		}
	}
	visit(t)
}

// fingerprint is what an entry says, in a form two entries that say the
// same share.
func (entry *trustEntry) fingerprint() string {
	var parts []string
	list := func(kind string, formulas []trustFormula) {
		for _, formula := range formulas {
			parts = append(parts, kind+" "+formula.text)
		}
	}
	list("requires", entry.requires)
	list("ensures", entry.ensures)
	list("modifies", entry.modifies)
	list("vouches", entry.vouches)
	list("runs", entry.runs)
	for _, call := range entry.calls {
		parts = append(parts, fmt.Sprintf("calls %s(%s) %v", call.name, strings.Join(call.params, ", "), call.deterministic))
		list("calls requires", call.requires)
	}
	return strings.Join(parts, "\n")
}

// reportTwoEntries reports every type to which the trust files of the
// packages built together give two different contracts. A value that
// verified code of one module checked against its entry can reach, through
// code that is not verified, verified code of another module that relies on
// another entry, so that what one proof checked is not what the other
// assumed. Every package compares the entries its proofs and those of the
// packages it is built with used, so a package that imports two such
// modules reports it even when it has no proofs of its own.
func (pv *pkgVerifier) reportTwoEntries(total *Usage) {
	seen := map[string]*EntryUse{}
	var keys []string
	reported := map[string]bool{}
	for _, use := range total.Entries {
		if use.Every == "" {
			continue
		}
		first, ok := seen[use.Key]
		if !ok {
			seen[use.Key] = use
			keys = append(keys, use.Key)
			continue
		}
		if first.Fingerprint == use.Fingerprint || reported[use.Key] {
			continue
		}
		reported[use.Key] = true
		a, b := fmt.Sprintf("%s:%d", first.File, first.Line), fmt.Sprintf("%s:%d", use.File, use.Line)
		if b < a {
			a, b = b, a
		}
		pv.report(pv.pass.Files[0].Package, "the trust files of this build give %s two contracts, at %s and at %s; a value that verified code checked "+
			"against one can reach verified code that relies on the other. Make the entries the same, or run laas with -vego.trusted naming one file",
			use.Key, a, b)
	}
}
