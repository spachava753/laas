package vego

import (
	"fmt"
	"go/token"
	"go/types"
	"maps"
	"os"
	"path/filepath"
	"slices"
	"strings"

	"github.com/spachava753/laas/vego/internal/logic"
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
// found (see the check of fingerprints), whatever made the proof look, and
// so does finding none: a proof that rests on a type having no contract
// waives what a contract would have asked for, such as vouches on the
// trusted functions that return a value of the type. An entry that cannot
// be used is not recorded: every use of it is an error.
func (pv *pkgVerifier) typeEntry(key string, obj *types.Func, methodOf *types.Func, valueOf *types.TypeName) *funcInfo {
	if fn, done := pv.typeEntries[key]; done {
		return fn
	}
	pv.typeEntries[key] = nil
	entry := pv.entryFor(key)
	declared, pkg := obj.Pos(), obj.Pkg()
	if valueOf != nil {
		declared, pkg = valueOf.Pos(), valueOf.Pkg()
	}
	if entry == nil {
		pv.unentered[key] = pv.inAnalysedModule(pkg, declared)
		return nil
	}
	fn := newFuncInfo(obj)
	fn.trust, fn.methodOf, fn.valueOf = entry, methodOf, valueOf
	nameUnnamed(fn, entry)
	pv.typeEntries[key] = fn
	if pv.inAnalysedModule(pkg, declared) {
		what := "the method " + key
		if valueOf != nil {
			what = "the function type " + key
		}
		fn.defect("%s is declared in the module of this package; write its contract in the doc comment where it is declared", what)
	}
	if text := entry.receiver.text; text != "" {
		switch {
		case methodOf == nil:
			fn.defect("it names a receiver, which only an entry for a method of an interface can do")
		default:
			if problem := fn.setReceiver(text, methodOf); problem != "" {
				fn.defect("its receiver: %s", problem)
			}
		}
	}
	pv.readEntry(fn, entry)
	// A contract names its receiver to speak of its states, to say that
	// the method writes behind it, or to place a result within it, as one
	// in source does (checkReceivers).
	if fn.receiver != nil && !pv.hasStates(fn.receiver.Type()) && !writesBehind(fn) && !placesWithin(fn) {
		fn.defect("it names the receiver %s, but %s has no states, and the entry neither lists %s under modifies nor places a result within it",
			fn.receiver.Name(), declaringInterface(methodOf).Name(), fn.receiver.Name())
	}
	// What a call through the value is handed is refused when it can
	// carry code nobody has seen, so nothing is left for runs or calls to
	// say.
	if len(entry.runs) > 0 {
		fn.defect("it lists runs, which a contract of a type cannot have: a call through a value of the type is never handed code nobody has seen")
	}
	if len(entry.encodes) > 0 || len(entry.decodes) > 0 {
		fn.defect("it lists encodes, which a contract of a type cannot have: only the entries that come with vego list it")
	}
	if len(entry.formats) > 0 {
		fn.defect("it lists formats, which a contract of a type cannot have: a call through a value of the type is never handed values whose formatting runs code")
	}
	if len(entry.calls) > 0 {
		fn.defect("it has calls, which a contract of a type cannot have")
	}
	if len(entry.stores) > 0 {
		fn.defect("it lists stores, which a contract of a type cannot have: a value of the type is any implementation, and what one stores no entry can see")
	}
	if len(entry.keeps) > 0 {
		fn.defect("it lists keeps, which a contract of a type cannot have: a call through a value of the type is never handed code nobody has seen")
	}
	// What an implementation may find on what a call hands it may be
	// claimed, as for a function; see asserts.go.
	var sig *types.Signature
	var from *types.Package
	switch {
	case methodOf != nil:
		sig, from = methodOf.Type().(*types.Signature), methodOf.Pkg()
	case valueOf != nil:
		sig, from = signatureOf(valueOf.Type()), valueOf.Pkg()
	}
	if _, problem := pv.assertsClaim(entry, sig, from); problem != "" {
		fn.defect("%s", problem)
	}
	pv.readVouches(fn, entry, false)
	pv.checkValueContract(fn)
	// A contract that cannot be used makes every use of it an error, so
	// no proof rests on it.
	if !fn.broken {
		pv.lookedUp = append(pv.lookedUp, fn)
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
// interface where it is used. A contract that cannot be used ends the path
// there, under guard, and what is returned in its place promises and
// writes nothing; see viewOf. A contract that a trust file gives a type of
// another package is named as its entry, and its use is recorded for the
// trust report.
//
// A use that calls through a value of the type may rely on part of a
// contract; any other use, a check of a value against it, cannot.
func (v *fnVerifier) usable(pos token.Pos, fn *funcInfo, title string, st *state, guard []*logic.Term, forCall bool) *funcInfo {
	view := v.viewOf(fn)
	v.reportUnusable(pos, view, title)
	if view.cut || (view.partial && !forCall) {
		v.cut(st, guard)
		return blank(fn)
	}
	if fn.trust != nil {
		v.noteUse(fn, pos)
	}
	return view.fn
}

// entryHint tells, in a message about a method of an interface or a
// function type without a contract, how a type of another module gets one:
// by an entry of the trust file with the key given.
func (pv *pkgVerifier) entryHint(pkg *types.Package, declared token.Pos, key string) string {
	if pkg == nil || pv.inAnalysedModule(pkg, declared) {
		return ""
	}
	if problem := pv.trustProblem(); problem != "" {
		return fmt.Sprintf("; %s, so an entry %s there may not have been read: fix the file first", problem, key)
	}
	return fmt.Sprintf("; for a type of another module, give it an entry %s in %s", key, TrustFileName)
}

// trustProblem describes the first problem of the project's trust file, or
// returns "" when it has none. Entries of a file with a problem may not have
// been read, so no message advises adding one to it without saying so.
func (pv *pkgVerifier) trustProblem() string {
	if pv.projectTrust == nil || len(pv.projectTrust.problems) == 0 {
		return ""
	}
	first := pv.projectTrust.problems[0]
	return fmt.Sprintf("the trust file %s has problems, the first at line %d (%s)", filepath.Base(pv.projectTrust.path), first.line, first.msg)
}

// addEntryAdvice is the end of a message about a function without a
// contract: add a trusted contract for it, or, when the project's trust
// file has problems, fix the file, where the entry may already be.
func (pv *pkgVerifier) addEntryAdvice(key string) string {
	if problem := pv.trustProblem(); problem != "" {
		return fmt.Sprintf("or, since %s, fix the file first: an entry for %s there may not have been read", problem, key)
	}
	return fmt.Sprintf("or add a trusted contract for %s to %s", key, TrustFileName)
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
		if held, replaced := heldAs(t); replaced {
			visit(held)
			return
		}
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
	if entry.receiver.text != "" {
		parts = append(parts, "receiver "+entry.receiver.text)
	}
	list("requires", entry.requires)
	list("ensures", entry.ensures)
	list("modifies", entry.modifies)
	list("vouches", entry.vouches)
	list("runs", entry.runs)
	list("formats", entry.formats)
	if entry.isIsolated() {
		parts = append(parts, "isolated")
	}
	if entry.initialiserOnly {
		parts = append(parts, "initialiserOnly")
	}
	for _, call := range entry.calls {
		parts = append(parts, fmt.Sprintf("calls %s(%s) %v", call.name, strings.Join(call.params, ", "), call.deterministic))
		list("calls requires", call.requires)
	}
	for _, kept := range keepsDescribed(entry) {
		parts = append(parts, "keeps "+kept)
	}
	// Every other field an entry reads, so that two entries that differ in
	// any claim are told apart (F35, S0).
	lists := func(kind string, items []trustKeep) {
		for _, item := range items {
			var dests []string
			for _, dest := range item.dests {
				dests = append(dests, dest.text)
			}
			parts = append(parts, fmt.Sprintf("%s %s: [%s]", kind, item.name, strings.Join(dests, ", ")))
		}
	}
	lists("asserts", entry.asserts)
	lists("prints", entry.prints)
	list("stores", entry.stores)
	list("encodes", entry.encodes)
	list("decodes", entry.decodes)
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
		if owner, isState := strings.CutPrefix(use.Key, "states of "); isState {
			pv.report(pv.pass.Files[0].Package, "the trust files of this build declare the states of %s differently, at %s and at %s; "+
				"a value whose states one proof changed can reach a proof that reads them otherwise. Make the declarations the same, "+
				"or run laas with -vego.trusted naming one file", owner, a, b)
			continue
		}
		pv.report(pv.pass.Files[0].Package, "the trust files of this build give %s two contracts, at %s and at %s; a value that verified code checked "+
			"against one can reach verified code that relies on the other. Make the entries the same, or run laas with -vego.trusted naming one file",
			use.Key, a, b)
	}
	// A proof made with no entry for a type waived what an entry asks
	// for, such as vouches on a trusted function that returns a value of
	// it, and a value it lets through can reach a proof that relies on
	// an entry.
	none := slices.Clone(total.Unentered)
	slices.SortFunc(none, func(a, b Unentered) int { return strings.Compare(a.Key+" "+a.Package, b.Key+" "+b.Package) })
	for _, missing := range none {
		use := seen[missing.Key]
		if use == nil || reported[missing.Key+" "+missing.Package] {
			continue
		}
		reported[missing.Key+" "+missing.Package] = true
		if owner, isState := strings.CutPrefix(missing.Key, "states of "); isState {
			remedy := "declare the same states in the trust file of its module, or run laas with -vego.trusted naming one file"
			if missing.Own {
				remedy = "the type is declared in its module, so declare the states with @State in its doc comment and remove the declaration"
			}
			pv.report(pv.pass.Files[0].Package, "the trust files of this build declare states of %s at %s:%d, and the proofs of package %s were made with none; "+
				"a value whose states one proof changed can reach a proof that reads them otherwise: %s", owner, use.File, use.Line, missing.Package, remedy)
			continue
		}
		remedy := "add the same entry to the trust file of its module, or run laas with -vego.trusted naming one file"
		if missing.Own {
			remedy = "the type is declared in its module, so write the contract in source where the type is declared and remove the entry"
		}
		pv.report(pv.pass.Files[0].Package, "the trust files of this build give %s a contract at %s:%d, and the proofs of package %s were made with none; "+
			"what they let through can reach verified code that relies on the entry: %s", missing.Key, use.File, use.Line, missing.Package, remedy)
	}
}

// noteLookups records, once the package has been verified, the entries it
// looked up and the keys it found none for, if it has proofs: a package
// without annotated functions relies on nothing, whatever it looked up
// while its declarations were read.
func (pv *pkgVerifier) noteLookups() {
	if !slices.ContainsFunc(pv.order, (*funcInfo).annotated) {
		return
	}
	for _, fn := range pv.lookedUp {
		pv.noteUse(fn, token.NoPos)
	}
	for _, use := range pv.stateUses {
		use.Relied = []string{pv.pass.Pkg.Path()}
		pv.usage.Entries = append(pv.usage.Entries, use)
	}
	for _, key := range slices.Sorted(maps.Keys(pv.unentered)) {
		pv.usage.Unentered = append(pv.usage.Unentered, Unentered{Key: key, Package: pv.pass.Pkg.Path(), Own: pv.unentered[key]})
	}
}
