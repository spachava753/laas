package vego

import (
	"fmt"
	"go/ast"
	"go/types"
	"os"
	"slices"
	"strings"
)

// What a function runs of code it does not see (F43). A call of a function
// of another package can run code of the calling package only through a call
// that does not name its target: a call of an interface method, or a call
// through a function value, made somewhere in what the call runs, on a value
// that holds code of the caller (Go dispatches an interface method by name
// and signature, and a function value by signature), or by reflection, which
// runs code only through such calls or through functions without a body.
//
// The summary of a function says which such calls running it may make: the
// keys, an interface method by its exported name and canonical signature
// (sigs.go), a function value by its canonical signature, and formatting,
// which runs String, Error, Format, and GoString; or top, when it hands what
// may hold code to code it cannot follow. ambient is set when what it runs
// may read a package-level variable that code other than its package's
// initialisers may set to code (holdsSetCode): the code it calls through
// values may then be code no operand of the call holds.
//
// It is computed from the call graph of the function's package, by the
// graph's own rules: each node records in out what its own body runs of code
// from outside the package, and the summary of a function is the join of out
// over every node its node reaches by any edge. A summary is a fact about
// the code, so it is computed for every function with a body of a package
// that builds its graph, verified or not, and published for those another
// package can call or reach through a value.

// runsSet is a summary, or the out of a node.
type runsSet struct {
	top, ambient, format bool
	methods, funcs       map[string]bool
}

func newRunsSet() *runsSet { return &runsSet{methods: map[string]bool{}, funcs: map[string]bool{}} }

// join adds o to s and reports whether s changed.
func (s *runsSet) join(o *runsSet) bool {
	if o == nil {
		return false
	}
	changed := false
	set := func(b *bool, v bool) {
		if v && !*b {
			*b, changed = true, true
		}
	}
	set(&s.top, o.top)
	set(&s.ambient, o.ambient)
	set(&s.format, o.format)
	for k := range o.methods {
		if !s.methods[k] {
			s.methods[k], changed = true, true
		}
	}
	for k := range o.funcs {
		if !s.funcs[k] {
			s.funcs[k], changed = true, true
		}
	}
	return changed
}

// empty reports whether a summary runs nothing of code from outside.
func (s *runsSet) empty() bool {
	return !s.top && !s.ambient && !s.format && len(s.methods) == 0 && len(s.funcs) == 0
}

// addMethod adds a call of an interface method. A method with a name that is
// not exported can be declared only in the package that declares the name,
// which another package's call cannot be.
func (s *runsSet) addMethod(m *types.Func) {
	if m.Exported() {
		s.methods[m.Name()+"|"+canonSig(withoutRecv(m.Type().(*types.Signature)))] = true
	}
}

// addFunc adds a call through a function value of a signature; one whose
// signature is not known is top.
func (s *runsSet) addFunc(sig *types.Signature) {
	if sig == nil {
		s.top = true
		return
	}
	s.funcs[canonSig(sig)] = true
}

// addClaimed adds what the claim of an entry over a type allows: the methods
// of the interfaces and the function values of the function types it
// reaches through fields, elements, and pointers.
func (s *runsSet) addClaimed(t types.Type, seen map[types.Type]bool) {
	if t == nil || seen[t] {
		return
	}
	seen[t] = true
	if held, replaced := heldAs(t); replaced {
		s.addClaimed(held, seen)
		return
	}
	switch u := t.Underlying().(type) {
	case *types.Signature:
		s.addFunc(withoutRecv(u))
	case *types.Interface:
		for m := range u.Methods() {
			s.addMethod(m)
		}
	case *types.Pointer:
		s.addClaimed(u.Elem(), seen)
	case *types.Slice:
		s.addClaimed(u.Elem(), seen)
	case *types.Array:
		s.addClaimed(u.Elem(), seen)
	case *types.Chan:
		s.addClaimed(u.Elem(), seen)
	case *types.Map:
		s.addClaimed(u.Key(), seen)
		s.addClaimed(u.Elem(), seen)
	case *types.Struct:
		for f := range u.Fields() {
			s.addClaimed(f.Type(), seen)
		}
	}
}

// describe writes a summary for a message.
func (s *runsSet) describe() string {
	var parts []string
	var names []string
	for k := range s.methods {
		name, _, _ := strings.Cut(k, "|")
		if !slices.Contains(names, name) {
			names = append(names, name)
		}
	}
	slices.Sort(names)
	if len(names) > 0 {
		parts = append(parts, "the methods named "+strings.Join(names, ", "))
	}
	if len(s.funcs) > 0 {
		parts = append(parts, "function values")
	}
	if s.format {
		parts = append(parts, "the methods that formatting runs")
	}
	if s.ambient {
		parts = append(parts, "code it holds that the call does not hand it")
	}
	if len(parts) == 0 {
		return "nothing"
	}
	return strings.Join(parts, ", ")
}

// runsData is a summary as it travels in a fact.
type runsData struct {
	Top, Ambient, Format bool
	Methods, Funcs       []string
}

func (s *runsSet) data() runsData {
	return runsData{Top: s.top, Ambient: s.ambient, Format: s.format,
		Methods: slices.Sorted(mapKeysOf(s.methods)), Funcs: slices.Sorted(mapKeysOf(s.funcs))}
}

func (d runsData) set() *runsSet {
	s := newRunsSet()
	s.top, s.ambient, s.format = d.Top, d.Ambient, d.Format
	for _, k := range d.Methods {
		s.methods[k] = true
	}
	for _, k := range d.Funcs {
		s.funcs[k] = true
	}
	return s
}

// runsFact is the summary of a function, published for every function and
// method with an exported name that has a body.
type runsFact struct{ Runs runsData }

func (*runsFact) AFact() {}

func (f *runsFact) String() string { return "runs(" + f.Runs.set().describe() + ")" }

// runsIndexFact holds, for a package, the join of the summaries of its
// implementations by key: its methods with an exported name by name and
// signature, and its functions, method values, and literals used as values,
// and exported functions, by signature. A call through a value in a package
// that imports it may reach any of them.
type runsIndexFact struct {
	Methods map[string]runsData
	Funcs   map[string]runsData
	// Ambient is the join of the summaries of the functions and methods
	// with an exported name of the package that run code no call hands
	// them, which code that cannot be followed may call (F14 of the review
	// of step 1 of F43).
	Ambient runsData
}

func (*runsIndexFact) AFact() {}

func (f *runsIndexFact) String() string {
	return fmt.Sprintf("runsindex(%d methods, %d functions)", len(f.Methods), len(f.Funcs))
}

// outOf returns the out of a node.
func (g *callGraph) outOf(n *callNode) *runsSet {
	if g.outs == nil {
		g.outs = map[*callNode]*runsSet{}
	}
	s := g.outs[n]
	if s == nil {
		s = newRunsSet()
		g.outs[n] = s
	}
	return s
}

// summaryOf returns the summary of a node of the package: the join of out
// over every node it reaches.
func (pv *pkgVerifier) summaryOf(start *callNode) *runsSet {
	g := pv.callGraph()
	if g.summaries == nil {
		g.summaries = map[*callNode]*runsSet{}
	}
	if s := g.summaries[start]; s != nil {
		return s
	}
	pv.noteReadsHeld()
	s := newRunsSet()
	seen := map[*callNode]bool{start: true}
	queue := []*callNode{start}
	for len(queue) > 0 {
		n := queue[0]
		queue = queue[1:]
		s.join(g.outs[n])
		if pv.readsHeld[n] {
			s.ambient = true
		}
		for _, e := range n.edges {
			if !seen[e.to] {
				seen[e.to] = true
				queue = append(queue, e.to)
			}
		}
	}
	g.summaries[start] = s
	return s
}

// noteReadsHeld decides, once, which nodes read a package-level variable
// that other code may set to code.
func (pv *pkgVerifier) noteReadsHeld() {
	if pv.readsHeld != nil {
		return
	}
	g := pv.callGraph()
	pv.readsHeld = map[*callNode]bool{}
	for _, node := range g.byObj {
		pv.readsHeld[node] = pv.readsHeldLocally(node.fn.decl.Body)
	}
	for _, node := range g.lits {
		pv.readsHeld[node] = pv.readsHeldLocally(node.lit.Body)
	}
}

// exportRuns publishes the summaries of the package: of every function and
// method with an exported name that has a body, and the index of its
// implementations.
func (pv *pkgVerifier) exportRuns() {
	g := pv.callGraph()
	index := &runsIndexFact{Methods: map[string]runsData{}, Funcs: map[string]runsData{}}
	methods, funcs := map[string]*runsSet{}, map[string]*runsSet{}
	joinAt := func(m map[string]*runsSet, key string, s *runsSet) {
		if m[key] == nil {
			m[key] = newRunsSet()
		}
		m[key].join(s)
	}
	for _, fn := range pv.order {
		node := g.byObj[fn.obj]
		if node == nil || fn.closure != nil {
			continue
		}
		s := pv.summaryOf(node)
		sig := fn.obj.Type().(*types.Signature)
		if fn.obj.Exported() {
			pv.pass.ExportObjectFact(fn.obj, &runsFact{Runs: s.data()})
			if sig.Recv() != nil {
				joinAt(methods, fn.obj.Name()+"|"+canonSig(withoutRecv(sig)), s)
			}
		}
	}
	for _, escape := range g.escapes {
		if sig := signatureOf(escape.t); sig != nil {
			joinAt(funcs, canonSig(sig), pv.summaryOf(escape.node))
		}
	}
	ambient := newRunsSet()
	for _, fn := range pv.order {
		if node := g.byObj[fn.obj]; node != nil && fn.closure == nil && fn.obj.Exported() {
			if s := pv.summaryOf(node); s.ambient {
				ambient.join(s)
			}
		}
	}
	index.Ambient = ambient.data()
	for k, s := range methods {
		if !s.empty() {
			index.Methods[k] = s.data()
		}
	}
	for k, s := range funcs {
		if !s.empty() {
			index.Funcs[k] = s.data()
		}
	}
	pv.pass.ExportPackageFact(index)
}

// importedRuns returns the summary that another package published for a
// function, or nil.
func (pv *pkgVerifier) importedRuns(fn *types.Func) *runsSet {
	if fn == nil || fn.Pkg() == nil || fn.Pkg() == pv.pass.Pkg {
		return nil
	}
	fact := &runsFact{}
	if !pv.pass.ImportObjectFact(fn.Origin(), fact) {
		return nil
	}
	return fact.Runs.set()
}

// visibleIndex returns the index of the implementations of every package
// this one imports, at any depth, joined by key.
func (pv *pkgVerifier) visibleIndex() (methods, funcs map[string]*runsSet) {
	if pv.indexMethods == nil {
		pv.indexMethods, pv.indexFuncs = map[string]*runsSet{}, map[string]*runsSet{}
		for _, published := range pv.pass.AllPackageFacts() {
			fact, ok := published.Fact.(*runsIndexFact)
			if !ok || published.Package == pv.pass.Pkg {
				continue
			}
			for k, d := range fact.Methods {
				if pv.indexMethods[k] == nil {
					pv.indexMethods[k] = newRunsSet()
				}
				pv.indexMethods[k].join(d.set())
			}
			for k, d := range fact.Funcs {
				if pv.indexFuncs[k] == nil {
					pv.indexFuncs[k] = newRunsSet()
				}
				pv.indexFuncs[k].join(d.set())
			}
		}
	}
	return pv.indexMethods, pv.indexFuncs
}

// visibleAmbient returns what the functions of the packages this one
// imports may run of code no call hands them, closed over the
// implementations this package can see: code that cannot be followed may
// call any of them, at any call that may enter such code. The functions of
// this package are not counted: code that is not verified calls them only
// when it is handed them, as "What a proof assumes" says, and a call of one
// that this package makes is in its graph.
func (pv *pkgVerifier) visibleAmbient() *runsSet {
	if pv.ambientKeys == nil {
		s := newRunsSet()
		if os.Getenv("VEGO_F43_AK") == "off" {
			// TEMPORARY, for the measure of what following F14 costs.
			pv.ambientKeys = s
			return s
		}
		for _, published := range pv.pass.AllPackageFacts() {
			if fact, ok := published.Fact.(*runsIndexFact); ok && published.Package != pv.pass.Pkg {
				s.join(fact.Ambient.set())
			}
		}
		pv.ambientKeys = pv.closed(s)
	}
	return pv.ambientKeys
}

// ambientAt adds, at a call that may enter code that cannot be followed,
// what a function of another package that runs code no call hands it may
// run of this package, since that code may call it.
func (pv *pkgVerifier) ambientAt(call *ast.CallExpr, text string, unresolved func(*ast.CallExpr, string, string, []*callNode)) {
	if ak := pv.visibleAmbient(); !ak.empty() {
		unresolved(call, text, fmt.Sprintf("code that cannot be followed may run there, and may call a function of a package this one imports "+
			"that runs code it holds that no call hands it, and may run %s", ak.describe()), pv.targetsOf(ak))
	}
}

// keyMeets reports whether a key written as prefix and signature meets one of
// the keys of a set: the same, or either signature "*".
func keyMeets(keys map[string]bool, prefix, sig string) bool {
	if keys[prefix+sig] || keys[prefix+"*"] {
		return true
	}
	if sig == "*" {
		for k := range keys {
			if strings.HasPrefix(k, prefix) {
				return true
			}
		}
	}
	return false
}

// implsOf returns the join of the summaries of the implementations of a
// method key or a function key that this package can see in the packages it
// imports, or nil when it sees none that runs anything.
func (pv *pkgVerifier) implsOf(methodKey, funcKey string) *runsSet {
	methods, funcs := pv.visibleIndex()
	var found *runsSet
	add := func(m map[string]*runsSet, key string) {
		prefix, sig := "", key
		if i := strings.Index(key, "|"); i >= 0 {
			prefix, sig = key[:i+1], key[i+1:]
		}
		for k, s := range m {
			kp, ks := "", k
			if i := strings.Index(k, "|"); i >= 0 {
				kp, ks = k[:i+1], k[i+1:]
			}
			if kp == prefix && (ks == sig || ks == "*" || sig == "*") {
				if found == nil {
					found = newRunsSet()
				}
				found.join(s)
			}
		}
	}
	if methodKey != "" {
		add(methods, methodKey)
	}
	if funcKey != "" {
		add(funcs, funcKey)
	}
	return found
}

// closed returns a summary joined with the summaries of the implementations
// of its keys that this package can see, and of theirs, until nothing
// changes: an implementation that another package cannot see may be what a
// call of a key there runs.
func (pv *pkgVerifier) closed(s *runsSet) *runsSet {
	c := newRunsSet()
	c.join(s)
	done := map[string]bool{}
	for changed := true; changed; {
		changed = false
		for k := range c.methods {
			if !done["m"+k] {
				done["m"+k] = true
				changed = c.join(pv.implsOf(k, "")) || changed
			}
		}
		for k := range c.funcs {
			if !done["f"+k] {
				done["f"+k] = true
				changed = c.join(pv.implsOf("", k)) || changed
			}
		}
	}
	return c
}

// targetsOf returns the nodes of this package that the keys of a summary may
// reach: its methods of a key's name and signature, its values of a key's
// signature, and the methods formatting runs.
func (pv *pkgVerifier) targetsOf(s *runsSet) []*callNode {
	var found []*callNode
	seen := map[*callNode]bool{}
	add := func(n *callNode) {
		if !seen[n] {
			seen[n] = true
			found = append(found, n)
		}
	}
	for _, fn := range pv.order {
		node := pv.graph.byObj[fn.obj]
		sig := fn.obj.Type().(*types.Signature)
		if node == nil || sig.Recv() == nil {
			continue
		}
		key := canonSig(withoutRecv(sig))
		if sig.RecvTypeParams().Len() > 0 {
			key = "*"
		}
		if keyMeets(s.methods, fn.obj.Name()+"|", key) ||
			s.format && slices.Contains([]string{"String", "Error", "Format", "GoString"}, fn.obj.Name()) {
			add(node)
		}
	}
	for _, escape := range pv.graph.escapes {
		if sig := signatureOf(escape.t); sig == nil || keyMeets(s.funcs, "", canonSig(sig)) {
			add(escape.node)
		}
	}
	for _, method := range pv.graph.ifaceValues {
		msig := withoutRecv(method.Type().(*types.Signature))
		if keyMeets(s.funcs, "", canonSig(msig)) {
			for _, n := range pv.methodsMatching(method.Name(), msig) {
				add(n)
			}
		}
	}
	return found
}

// nodeVerified reports whether a node is a function whose verification is
// attempted, or a literal written in one.
func (pv *pkgVerifier) nodeVerified(node *callNode) bool {
	if node == nil {
		return false
	}
	if node.fn != nil {
		return node.fn.annotated() && pv.entryFor(node.fn.obj.FullName()) == nil
	}
	for _, fn := range pv.order {
		if fn.decl != nil && fn.decl.Body != nil && fn.decl.Pos() <= node.lit.Pos() && node.lit.End() <= fn.decl.End() {
			return fn.annotated() && pv.entryFor(fn.obj.FullName()) == nil
		}
	}
	return false
}

// keyOfFunc returns the key of a function value of a signature.
func keyOfFunc(sig *types.Signature) string {
	if sig == nil {
		return "*"
	}
	return canonSig(sig)
}

// implsAt adds what the implementations that this package can see in the
// packages it imports may run, at a call through a value of a method key or
// a function key: their summaries join the node's out, and the call reaches
// what they may run of this package.
func (pv *pkgVerifier) implsAt(call *ast.CallExpr, node *callNode, out *runsSet, methodKey, funcKey, text, why string,
	unresolved func(*ast.CallExpr, string, string, []*callNode)) {
	if methodKey == "" && funcKey == "" {
		return
	}
	impls := pv.implsOf(methodKey, funcKey)
	if impls == nil {
		return
	}
	out.join(impls)
	// A summary that is top adds no edge here unless it is ambient too.
	// That is sound because a verified implementation whose summary is top
	// is refused in its own package: top there reaches every exported
	// method of that package, the implementation itself among them, so its
	// own graph has the cycle (cycles/held/t1b). What remains is an
	// implementation that is not verified, which runs what it holds under
	// the assumption about code that is not verified.
	reach := pv.closed(impls)
	unresolved(call, text, fmt.Sprintf("%s, which may run %s", why, reach.describe()), pv.targetsOf(reach))
	if impls.top && impls.ambient {
		unresolved(call, text, why+", which hands code it holds that the call does not hand it to code that cannot be followed", pv.anythingTargets())
	}
}

// methodValueTaken adds what a method value runs, where it is taken and not
// called: of an interface method, the key, since a call of the value calls
// it; of a method of another package's type, what a call of it with the
// receiver would run, since the value holds the receiver. Verified code is
// refused the second (madeAs), but a body that is not verified may take it.
func (pv *pkgVerifier) methodValueTaken(sel *ast.SelectorExpr, out *runsSet, unresolved func(*ast.CallExpr, string, string, []*callNode)) {
	selection := pv.info.Selections[sel]
	if selection == nil || selection.Kind() != types.MethodVal {
		return
	}
	method, _ := selection.Obj().(*types.Func)
	if method == nil {
		return
	}
	if isIfaceMethod(method) {
		out.addMethod(method)
		return
	}
	if method.Pkg() == nil || method.Pkg() == pv.pass.Pkg {
		return
	}
	origin := pv.originOf(method)
	call := &ast.CallExpr{Fun: sel, Lparen: sel.End(), Rparen: sel.End()}
	pv.handedCode(call, method.Type().(*types.Signature), pv.entryFor(origin.FullName()), origin.Pkg(), false, true, origin.FullName(), false,
		"the method value "+types.ExprString(sel), unresolved)
}

// outWithoutBody adds what a call of a function of the package without a
// body may run: anything it is handed, since its code is assembly or another
// package's, and anything at all when a //go:linkname directive pulls it
// from a package that this one does not import, whose code may call any
// function of this package by its symbol.
func (pv *pkgVerifier) outWithoutBody(call *ast.CallExpr, callee *types.Func, out *runsSet) {
	// Assembly of a package that holds some (hasForeignCode) is assumed
	// to call Go code only through what it is handed, as "What a proof
	// assumes" says; what it is handed is the rule below.
	if target := pv.linknameOf(callee.Name()); target != "" {
		at := strings.LastIndex(target, ".")
		if at < 0 || !pv.imports(target[:at]) {
			out.top = true
			return
		}
	}
	operands := slices.Clone(call.Args)
	if sel, ok := ast.Unparen(call.Fun).(*ast.SelectorExpr); ok && pv.info.Selections[sel] != nil {
		operands = append(operands, sel.X)
	}
	for _, arg := range operands {
		if holdsCode(pv.info.TypeOf(arg), map[types.Type]bool{}) {
			out.top = true
		}
	}
}

// linknameOf returns the target of a //go:linkname directive of the package
// for a local name, or "".
func (pv *pkgVerifier) linknameOf(name string) string {
	if pv.linkTargets == nil {
		pv.linkTargets = map[string]string{}
		for _, file := range pv.pass.Files {
			for _, group := range file.Comments {
				for _, c := range group.List {
					fields := strings.Fields(strings.TrimPrefix(c.Text, "//go:linkname "))
					if strings.HasPrefix(c.Text, "//go:linkname ") && len(fields) == 2 {
						pv.linkTargets[fields[0]] = fields[1]
					}
				}
			}
		}
	}
	return pv.linkTargets[name]
}

// imports reports whether a package path is this package's or one it
// imports, at any depth.
func (pv *pkgVerifier) imports(path string) bool {
	seen := map[*types.Package]bool{}
	var visit func(p *types.Package) bool
	visit = func(p *types.Package) bool {
		if seen[p] {
			return false
		}
		seen[p] = true
		if p.Path() == path {
			return true
		}
		return slices.ContainsFunc(p.Imports(), visit)
	}
	return visit(pv.pass.Pkg)
}

// resultHeld reports whether a function of another package whose body this
// package cannot follow, a trusted function or one without a summary, may
// return code it kept from an earlier call: one of its results can hold a
// value that can be called, and its entry does not say that it keeps a
// parameter there, which a caller would have handed it.
func (pv *pkgVerifier) resultHeld(callee *types.Func) bool {
	origin := pv.originOf(callee)
	if pv.importedRuns(origin) != nil {
		return false
	}
	sig := origin.Type().(*types.Signature)
	entry := pv.entryFor(origin.FullName())
	callable := false
	for i := range sig.Results().Len() {
		v := sig.Results().At(i)
		// An error the entry vouches for has a known origin: a type of
		// the standard library, or one vouched for, which holds no code of
		// the caller.
		vouched := entry != nil && isError(v.Type()) && slices.ContainsFunc(entry.vouches, func(f trustFormula) bool {
			return f.text == v.Name() || f.text == "result" || f.text == fmt.Sprintf("result%d", i+1)
		})
		callable = callable || !vouched && holdsCallable(pv, v.Type(), map[types.Type]bool{})
	}
	if !callable {
		return false
	}
	if entry == nil {
		return true
	}
	for _, keep := range entry.keeps {
		for _, dest := range keep.dests {
			if dest.text == "result" || slices.ContainsFunc(slices.Collect(sig.Results().Variables()), func(v *types.Var) bool { return v.Name() == dest.text }) {
				return false
			}
		}
	}
	return true
}
