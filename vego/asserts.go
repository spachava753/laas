package vego

import (
	"fmt"
	"go/token"
	"go/types"
	"slices"
	"strings"

	"gopkg.in/yaml.v3"
)

// An entry of a trust file may claim, under asserts, what a function finds
// on what a parameter holds, the receiver of a method included:
//
//	asserts:
//	  err: [interface{ Timeout() bool }]
//
// An entry that lists a parameter under runs or keeps claims: while the
// call lasts, and when what the function returns or keeps is called later
// through the entries of the methods of what it returns, it calls through
// an interface value or a function value nothing that the parameter holds,
// at any depth, but the methods of the interfaces and the function types
// that the parameter's type reaches through fields, elements, and
// pointers, and those that the types listed under asserts reach, which it
// may find by a type assertion. It uses no reflection to call what the
// parameter holds. An entry with no asserts for the parameter, or an empty
// list, claims that it finds nothing more. Static calls of methods of a
// concrete type on what the parameter holds, one listed or one of its own
// package, are the function's own code, which its contract covers.
// Verified code answers for the methods that can be called through the
// parameter's type, each of which is checked where the value is made; the
// author of the entry answers for everything else, which only the
// function's source shows, as it shows what the function keeps.
//
// Nothing checks a value converted to an interface against another
// interface it is later asserted to, and the list does not say which
// interface value reached from the parameter the function asserts. So
// over a parameter that is not of type error, listing an interface with a
// method that one of the interface types the parameter reaches lacks, or a
// function type it does not reach, is a defect (beyondStatic; the runs
// step of F33): a function that calls what it finds that way can have no
// true entry. Over an error any type may be listed: each method of a value
// converted to error is checked where it is converted, and such a value
// holds no interface value other than an error, and its methods return
// none (checkedMethods). This holds until optional interfaces are checked
// where values are converted to an interface.
//
// The call graph does not lean on the claim that an entry without asserts
// makes: it counts every method with an exported name and every function
// value of the package as reachable from an interface value handed over,
// as for a function with no entry; see callgraph.go. An asserts key
// narrows it to what the claim names.
//
// For a generic function, a key may also name a type parameter, with the
// empty list only, as in asserts: {E: []}. The claim: the function runs no
// method of a value of type E or *E, or of anything such a value holds,
// directly or through what it calls (fmt and reflect included), neither
// while the call lasts nor later through anything it returns, keeps, or
// registers. Without it, a type argument whose values reach a method makes
// a verified call refused, and in the call graph it reaches the methods of
// the package that such a value reaches; see checkTypeArgs and handedCode.

// addAsserts reads the asserts of an entry: a mapping from a parameter to
// the types the function may assert what it holds to.
func (f *trustFile) addAsserts(entry *trustEntry, node *yaml.Node) {
	if node.Kind != yaml.MappingNode {
		f.problem(node.Line, "asserts of %s must map a parameter to the types it may be asserted to, as in r: [io.WriterTo], or r: [] for none", entry.key)
		return
	}
	for i := 0; i+1 < len(node.Content); i += 2 {
		key, body := node.Content[i], node.Content[i+1]
		if key.Kind != yaml.ScalarNode {
			f.problem(key.Line, "asserts of %s must map a parameter to the types it may be asserted to, as in r: [io.WriterTo]", entry.key)
			continue
		}
		item := trustKeep{name: key.Value, line: key.Line, col: key.Column}
		if body.Kind != yaml.SequenceNode {
			f.problem(body.Line, "asserts of %s: %s must map to a list of types, as in [io.WriterTo], or [] for none", entry.key, key.Value)
			continue
		}
		for _, t := range body.Content {
			if t.Kind != yaml.ScalarNode {
				f.problem(t.Line, "asserts of %s: %s must map to a list of names of types", entry.key, key.Value)
				continue
			}
			item.dests = append(item.dests, trustFormula{text: t.Value, line: t.Line, col: t.Column})
		}
		entry.asserts = append(entry.asserts, item)
	}
}

// assertsClaim reads what an entry claims a function asserts its
// parameters to: for each parameter with the key, the types listed, which
// it resolves among the packages the function's package imports, at any
// depth. A key that names no parameter that can hold code, or a type that
// does not resolve or holds no code, makes the whole claim one that is not
// read, so the call keeps the rule for nothing claimed; checkAsserts
// reports it as a defect where the entry is used.
func (pv *pkgVerifier) assertsClaim(entry *trustEntry, sig *types.Signature, from *types.Package) (map[*types.Var][]types.Type, string) {
	if entry == nil || len(entry.asserts) == 0 || sig == nil {
		return nil, ""
	}
	params := map[string]*types.Var{}
	if recv := sig.Recv(); recv != nil {
		params[recv.Name()] = recv
	}
	for param := range sig.Params().Variables() {
		params[param.Name()] = param
	}
	claim := map[*types.Var][]types.Type{}
	typeParams := map[string]bool{}
	if generic := genericOfEntry(entry, from); generic != nil {
		for param := range generic.Type().(*types.Signature).TypeParams().TypeParams() {
			typeParams[param.Obj().Name()] = true
		}
	}
	for _, item := range entry.asserts {
		param, ok := params[item.name]
		switch {
		case typeParams[item.name] && len(item.dests) > 0:
			return nil, "its asserts lists types for " + item.name + ", a type parameter; for a type parameter only [] can be claimed yet, " +
				"that the function runs no method of a value of its type"
		case typeParams[item.name]:
			// What this claims is read by typeParamClaims.
			continue
		}
		switch {
		case !ok:
			return nil, "its asserts " + quote(item.name) + ": " + item.name + " is not a parameter"
		case !holdsCode(param.Type(), map[types.Type]bool{}):
			return nil, "its asserts lists " + item.name + ", whose type " + param.Type().String() +
				" can hold no error, interface value, function value, channel, or unsafe.Pointer, so the claim says nothing"
		}
		listed := []types.Type{}
		for _, name := range item.dests {
			t, problem := resolveListed(from, name.text)
			switch {
			case problem != "":
				return nil, "its asserts lists " + quote(name.text) + " for " + item.name + ", " + problem
			case !holdsCode(t, map[types.Type]bool{}):
				return nil, "its asserts lists " + name.text + " for " + item.name + ", a type that can hold no code, so listing it says nothing"
			}
			listed = append(listed, t)
		}
		if !isError(param.Type()) {
			if i, beyond := pv.beyondStatic(param.Type(), listed); beyond != "" {
				return nil, "its asserts lists " + item.dests[i].text + " for " + item.name + ", " + beyond +
					": nothing checks a value converted to an interface against another interface it is later asserted to, " +
					"so a function that calls what it finds that way runs code nobody checked, and no entry can claim it; " +
					"only over an error, each method of which is checked where the error is made, may asserts list more"
			}
		}
		claim[param] = listed
	}
	return claim, ""
}

// beyondStatic describes why a type listed under asserts over a parameter
// would let the function call, through an interface value or a function
// value, code that nobody checked, or returns "". The interface values that
// the function can reach from what the parameter holds are those of the
// interface types that the parameter's type, and each concrete type
// listed, reach (reachedCode): a value of each was checked where it was
// converted against the methods of its type only. The function may assert
// any of them to a listed interface, so a listed interface must have no
// method that one of those types lacks. A listed function type must be one
// that they reach. A listed concrete type adds what it reaches, since the
// function's own code may call its methods.
func (pv *pkgVerifier) beyondStatic(param types.Type, listed []types.Type) (int, string) {
	var r reachedTypes
	seen := map[types.Type]bool{}
	r.walk(param, seen)
	for _, t := range listed {
		switch t.Underlying().(type) {
		case *types.Interface, *types.Signature:
		default:
			r.walk(t, seen)
		}
	}
	for i, t := range listed {
		switch u := t.Underlying().(type) {
		case *types.Interface:
			for _, from := range r.ifaces {
				for method := range u.Methods() {
					found, _, _ := types.LookupFieldOrMethod(from, false, method.Pkg(), method.Name())
					if own, ok := found.(*types.Func); ok && types.Identical(own.Type(), method.Type()) {
						continue
					}
					// A value of an O-typed type was checked against the
					// interfaces of its O where it was converted (F35).
					// Over an entry, where nothing can be proved, only a
					// type O-typed by declaration counts (F14).
					if pv.oTypedByDeclaration(from) && pv.optionalMember(from, method) != nil {
						continue
					}
					return i, fmt.Sprintf("an interface with the method %s, and what it holds may hold a value of %s, which lacks it", method.Name(), from)
				}
			}
		case *types.Signature:
			if !slices.ContainsFunc(r.funcs, func(sig *types.Signature) bool { return types.Identical(sig, withoutRecv(u)) }) {
				return i, "a function type that nothing it holds has"
			}
		}
	}
	return 0, ""
}

// reachedTypes collects the interface types other than error, and the function
// types, that a type reaches.
type reachedTypes struct {
	ifaces []types.Type
	funcs  []*types.Signature
	// others are the rest of the types reached, in the order reached.
	others []types.Type
}

// walk collects what a value of type t can lead code to: the interfaces
// and the function types that t reaches through fields, elements, and
// pointers, and through the results of the methods of the types it
// reaches, concrete or not, and of the function types. An error leads to
// nothing more: each method of a value converted to error is checked where
// it is converted, and what it holds and returns has no interface value
// but errors (checkedMethods).
func (r *reachedTypes) walk(t types.Type, seen map[types.Type]bool) {
	if t == nil || seen[t] || isError(t) {
		return
	}
	seen[t] = true
	if held, replaced := heldAs(t); replaced {
		r.walk(held, seen)
		return
	}
	results := func(sig *types.Signature) {
		for result := range sig.Results().Variables() {
			r.walk(result.Type(), seen)
		}
	}
	if _, isIface := t.Underlying().(*types.Interface); !isIface {
		if _, isSig := t.Underlying().(*types.Signature); !isSig {
			r.others = append(r.others, t)
		}
		for _, set := range []*types.MethodSet{types.NewMethodSet(t), types.NewMethodSet(types.NewPointer(t))} {
			for selection := range set.Methods() {
				results(selection.Obj().Type().(*types.Signature))
			}
		}
	}
	switch u := t.Underlying().(type) {
	case *types.Signature:
		r.funcs = append(r.funcs, withoutRecv(u))
		results(u)
	case *types.Interface:
		r.ifaces = append(r.ifaces, t)
		for method := range u.Methods() {
			results(method.Type().(*types.Signature))
		}
	case *types.Pointer:
		r.walk(u.Elem(), seen)
	case *types.Slice:
		r.walk(u.Elem(), seen)
	case *types.Array:
		r.walk(u.Elem(), seen)
	case *types.Chan:
		r.walk(u.Elem(), seen)
	case *types.Map:
		r.walk(u.Key(), seen)
		r.walk(u.Elem(), seen)
	case *types.Struct:
		for field := range u.Fields() {
			r.walk(field.Type(), seen)
		}
	}
}

// assertsDescribed describes the claims under asserts for the trust report.
func assertsDescribed(entry *trustEntry) []string {
	var described []string
	for _, item := range entry.asserts {
		var listed []string
		for _, t := range item.dests {
			listed = append(listed, t.text)
		}
		what := "nothing"
		if len(listed) > 0 {
			what = strings.Join(listed, ", ")
		}
		described = append(described, item.name+": "+what)
	}
	return described
}

// quote writes a name between double quotes.
func quote(s string) string { return "\"" + s + "\"" }

// resolveListed reads a type an entry lists under asserts: a qualified name
// of a type of the package of the function or of one it imports at any
// depth, as io.WriterTo or *bufio.Writer, or an interface written by its
// methods, as interface{ Timeout() bool }, or error, which are read in the
// universe scope and so may use only predeclared types.
func resolveListed(from *types.Package, text string) (types.Type, string) {
	if strings.HasPrefix(strings.TrimSpace(text), "interface") || strings.TrimSpace(text) == "error" {
		tv, err := types.Eval(token.NewFileSet(), nil, token.NoPos, text)
		if err != nil || !tv.IsType() {
			return nil, "which is not an interface type written with predeclared types only (" + fmt.Sprint(err) + "); an interface whose methods use other types must be named"
		}
		return tv.Type, ""
	}
	t := resolveTypeName(from, text)
	if t == nil {
		path := "its package"
		if from != nil {
			path = from.Path()
		}
		return nil, "which names no type that " + path + " or what it imports declares"
	}
	return t, ""
}

// resolveTypeName finds a type written as a qualified name, as in
// io.WriterTo or *bufio.Writer, in a package or in what it imports at any
// depth.
func resolveTypeName(pkg *types.Package, text string) types.Type {
	pointer := strings.HasPrefix(text, "*")
	text = strings.TrimPrefix(text, "*")
	dot := strings.LastIndex(text, ".")
	if pkg == nil || dot <= 0 {
		return nil
	}
	path, name := text[:dot], text[dot+1:]
	seen := map[*types.Package]bool{}
	var find func(p *types.Package) *types.Package
	find = func(p *types.Package) *types.Package {
		if seen[p] {
			return nil
		}
		seen[p] = true
		if p.Path() == path {
			return p
		}
		for _, imported := range p.Imports() {
			if found := find(imported); found != nil {
				return found
			}
		}
		return nil
	}
	found := find(pkg)
	if found == nil {
		return nil
	}
	obj, ok := found.Scope().Lookup(name).(*types.TypeName)
	if !ok {
		return nil
	}
	if pointer {
		return types.NewPointer(obj.Type())
	}
	return obj.Type()
}

// checkAsserts records as a defect of a trusted contract a claim under
// asserts that cannot be read, or that is about a parameter whose code the
// function does not run, keep, or format.
func (pv *pkgVerifier) checkAsserts(fn *funcInfo, entry *trustEntry) {
	claim, problem := pv.assertsClaim(entry, fn.obj.Type().(*types.Signature), fn.obj.Pkg())
	if problem != "" {
		fn.defect("%s", problem)
		return
	}
	for param := range claim {
		switch {
		case param == fn.formatted:
			fn.defect("its asserts lists %s, which its formats lists; formats already says what the function runs of it", param.Name())
		case !fn.runs.get(param) && fn.keeps.get(param) == nil:
			fn.defect("its asserts lists %s, which its runs and keeps do not list; the function may then run no code it holds at all",
				param.Name())
		}
	}
}

// claimedTargets returns what a call of a function of another package may
// run of what a parameter is given under its claim: the methods of the
// interfaces and the function values of the function types that the
// parameter's type and the listed types reach.
func (pv *pkgVerifier) claimedTargets(param *types.Var, listed []types.Type) []*callNode {
	seen := map[types.Type]bool{}
	found := pv.staticTargets(param.Type(), seen)
	for _, t := range listed {
		found = append(found, pv.staticTargets(t, seen)...)
	}
	return found
}

// staticTargets returns the methods by name and signature of the interface
// types, and the function values by signature of the function types, that
// a type reaches through fields, elements, and pointers.
func (pv *pkgVerifier) staticTargets(t types.Type, seen map[types.Type]bool) []*callNode {
	if t == nil || seen[t] {
		return nil
	}
	seen[t] = true
	if held, replaced := heldAs(t); replaced {
		return pv.staticTargets(held, seen)
	}
	switch u := t.Underlying().(type) {
	case *types.Signature:
		return pv.valuesMatching(withoutRecv(u))
	case *types.Interface:
		var found []*callNode
		for method := range u.Methods() {
			found = append(found, pv.methodsMatching(method.Name(), withoutRecv(method.Type().(*types.Signature)))...)
		}
		return found
	case *types.Pointer:
		return pv.staticTargets(u.Elem(), seen)
	case *types.Slice:
		return pv.staticTargets(u.Elem(), seen)
	case *types.Array:
		return pv.staticTargets(u.Elem(), seen)
	case *types.Chan:
		return pv.staticTargets(u.Elem(), seen)
	case *types.Map:
		return append(pv.staticTargets(u.Key(), seen), pv.staticTargets(u.Elem(), seen)...)
	case *types.Struct:
		var found []*callNode
		for field := range u.Fields() {
			found = append(found, pv.staticTargets(field.Type(), seen)...)
		}
		return found
	}
	return nil
}

// genericOfEntry returns the generic function an entry is for, from the
// package of the function, or nil when it is for no generic function.
func genericOfEntry(entry *trustEntry, from *types.Package) *types.Func {
	if from == nil {
		return nil
	}
	_, name, ok := splitFuncName(entry.key)
	if !ok {
		return nil
	}
	f, ok := from.Scope().Lookup(name).(*types.Func)
	if ok && sortSliceViews[f.FullName()] {
		return newSliceView(f)
	}
	if !ok || f.Type().(*types.Signature).TypeParams() == nil {
		return nil
	}
	return f
}
