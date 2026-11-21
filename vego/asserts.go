package vego

import (
	"fmt"
	"go/token"
	"go/types"
	"strings"

	"gopkg.in/yaml.v3"
)

// An entry of a trust file may claim, under asserts, what a function finds
// on what a parameter holds, the receiver of a method included:
//
//	asserts:
//	  r: [io.WriterTo]
//
// The claim: while the call lasts, and when what the function returns or
// keeps is called later through the entries of the methods of what it
// returns, it calls nothing that the parameter holds, at any depth, but
// the methods of the interface types and the function values of the
// function types that the parameter's type reaches through fields,
// elements, and pointers, and those that the listed types reach, which it
// may find by a type assertion. It uses no reflection to call what the
// parameter holds. An empty list claims that it asserts the value to
// nothing. Without the key nothing is claimed, and the call graph counts
// every method with an exported name and every function value of the
// package as reachable from an interface value handed over; see
// callgraph.go. The claim narrows only the call graph.

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
		claim[param] = listed
	}
	return claim, ""
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
// methods, as interface{ Timeout() bool }, which is read in the universe
// scope and so may use only predeclared types.
func resolveListed(from *types.Package, text string) (types.Type, string) {
	if strings.HasPrefix(strings.TrimSpace(text), "interface") {
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
		case !fn.runs[param] && fn.keeps[param] == nil:
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
	if !ok || f.Type().(*types.Signature).TypeParams() == nil {
		return nil
	}
	return f
}
