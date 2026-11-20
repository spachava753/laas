package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"slices"

	"golang.org/x/tools/go/cfg"
	"golang.org/x/tools/go/types/typeutil"
)

// An error may be formatted only when it is known where it comes from.
// Formatting runs the error's methods and, for some verbs, methods of what
// the error contains; an error from outside could use them to write memory
// the function reasons about. An error of known origin cannot. It is one of
// two kinds:
//
//   - made: errors.New or fmt.Errorf made it, here, in a verified function
//     this one called, or in the initialiser of a sentinel, and nothing but
//     plain values and other made errors went into it. Its methods, and
//     those of every error in its tree, are those of the standard library.
//   - vouched: a trusted function returned it in a result its contract
//     lists under vouches, or it holds such an error in its tree, or a
//     verified function returned it. Nothing is known of its type. The author of the contract claims that every method of it,
//     of every error in its tree, and of every value these hold returns
//     without panicking and writes nothing a caller can see, whatever it
//     is passed; that == on these errors cannot panic and is identity, so
//     that errors.Is answers the same for errors and for targets that ==
//     reports equal; and that what errors.Is reports for it never changes.
//
// What is concluded from a known origin needs only what both kinds give:
// formatting it, the first argument of errors.Is, the safe side of ==, and
// handing it to a trusted function without runs all rest on its methods
// and its == alone. What needs a made error is not drawn from knownError:
// that an error is not nil and differs from others, and what errors.Is finds
// in it, are noted where errors.New and fmt.Errorf are called and for
// sentinels; see noteError and noteTree.
//
// Origin is decided where an error is used, from what was assigned to its
// variable on the paths that reach the use. Go reuses err for every call of
// a function, so a rule over every assignment in the function would refuse
// the wrapping of an error that only a vouched call can have put there.
// The paths are those of the control-flow graph of the body, which has
// every path Go can take and more; each use takes what every one of them
// brings, so one assignment of unknown origin on any path to it makes the
// use unknown. A variable is followed along the paths, tracked, when it is
// a local error variable of the function or of a literal, its home, and
// every assignment to it is in its home or in a literal deferred there
// (see tracked). Anything else is decided as before this was built, from
// every assignment to it in the function, and so is every use inside a
// function literal: a literal may run after any assignment of the function
// around it. What the origin at a use is never lives in the state of the
// verifier, so nothing that rewrites the state can leave it stale.

// origins holds, for one function body, what each error variable is assigned.
// A variable that is assigned in a way that is not understood is unknown.
type origins struct {
	sources map[*types.Var][]source
	unknown map[*types.Var]bool
	// bound holds the variables of the body bound to literals used in
	// place; see literalUses.
	bound map[*types.Var]*ast.FuncLit

	info *types.Info
	// body is the body of the declared function, and sig its signature, or
	// nil when the function is not one the package verifies.
	body *ast.BlockStmt
	sig  *types.Signature
	// lits holds every function literal of the body, and deferred those
	// that are the function of a defer statement as written.
	lits     []*ast.FuncLit
	deferred map[*ast.FuncLit]bool
	// sites holds where each variable is assigned with =, :=, or var, and
	// args the arguments given to each parameter of a literal used in
	// place, at all its calls. open holds the parameters of literals that
	// are not used in place, which could be given anything.
	sites map[*types.Var][]token.Pos
	args  map[*types.Var][]source
	open  map[*types.Var]bool
	// ranged holds the range keys and values, which go/cfg puts once
	// before the loop; see defsOf.
	ranged map[ast.Expr]bool
	// isTracked caches tracked, flows the flow of each home, and found
	// what is known of each definition; see knownDef.
	isTracked map[*types.Var]bool
	flows     map[*ast.BlockStmt]*flow
	found     map[*def]bool
}

// source is something assigned to an error variable: an expression, or the
// result with the given index of a call that returns several values.
type source struct {
	expr  ast.Expr
	index int
}

// emptyOrigins returns the origins of a function without a body.
func emptyOrigins(info *types.Info) *origins {
	return &origins{
		sources: map[*types.Var][]source{}, unknown: map[*types.Var]bool{}, info: info,
		deferred: map[*ast.FuncLit]bool{}, sites: map[*types.Var][]token.Pos{}, args: map[*types.Var][]source{},
		open: map[*types.Var]bool{}, ranged: map[ast.Expr]bool{}, isTracked: map[*types.Var]bool{},
		flows: map[*ast.BlockStmt]*flow{}, found: map[*def]bool{},
	}
}

// originsOf collects the assignments to variables in a function body.
func (pv *pkgVerifier) originsOf(body *ast.BlockStmt) *origins {
	if known, ok := pv.origins[body]; ok {
		return known
	}
	o := emptyOrigins(pv.info)
	o.body = body
	pv.origins[body] = o
	variable := func(e ast.Expr) *types.Var {
		id, ok := ast.Unparen(e).(*ast.Ident)
		if !ok {
			return nil
		}
		found, _ := pv.info.ObjectOf(id).(*types.Var)
		return found
	}
	assign := func(targets, values []ast.Expr) {
		for i, target := range targets {
			to := variable(target)
			if to != nil {
				o.sites[to] = append(o.sites[to], target.Pos())
			}
			switch {
			case to == nil:
			case len(values) == len(targets):
				o.sources[to] = append(o.sources[to], source{values[i], -1})
			case len(values) == 1:
				o.sources[to] = append(o.sources[to], source{values[0], i})
			default:
				o.unknown[to] = true
			}
		}
	}
	ast.Inspect(body, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.FuncLit:
			o.lits = append(o.lits, n)
		case *ast.DeferStmt:
			if lit, ok := ast.Unparen(n.Call.Fun).(*ast.FuncLit); ok {
				o.deferred[lit] = true
			}
		case *ast.AssignStmt:
			if n.Tok != token.ASSIGN && n.Tok != token.DEFINE {
				for _, target := range n.Lhs {
					o.unknown[variable(target)] = true
				}
				break
			}
			assign(n.Lhs, n.Rhs)
		case *ast.ValueSpec:
			targets := make([]ast.Expr, len(n.Names))
			for i, name := range n.Names {
				targets[i] = name
			}
			// Without a value the variable starts as nil.
			if len(n.Values) > 0 {
				assign(targets, n.Values)
			} else {
				for _, name := range n.Names {
					if to := variable(name); to != nil {
						o.sites[to] = append(o.sites[to], name.Pos())
					}
				}
			}
		case *ast.RangeStmt:
			for _, target := range []ast.Expr{n.Key, n.Value} {
				if target != nil {
					o.unknown[variable(target)] = true
					o.ranged[target] = true
				}
			}
		case *ast.TypeSwitchStmt:
			// The variable of each clause holds the operand, converted;
			// nothing above records that, so it is unknown.
			for _, clause := range n.Body.List {
				if implicit, ok := pv.info.Implicits[clause].(*types.Var); ok {
					o.unknown[implicit] = true
				}
			}
		case *ast.UnaryExpr:
			if n.Op == token.AND {
				o.unknown[variable(n.X)] = true
			}
		}
		return true
	})
	// A return assigns what it returns to the named results of its frame,
	// the function or the literal it is written in. A deferred literal can
	// read them after that.
	var frame func(root ast.Node, results *types.Tuple)
	frame = func(root ast.Node, results *types.Tuple) {
		ast.Inspect(root, func(n ast.Node) bool {
			switch n := n.(type) {
			case *ast.FuncLit:
				frame(n.Body, pv.info.TypeOf(n).(*types.Signature).Results())
				return false
			case *ast.ReturnStmt:
				if results == nil || len(n.Results) == 0 {
					break
				}
				for i := range results.Len() {
					result := results.At(i)
					switch {
					case result.Name() == "" || result.Name() == "_":
					case len(n.Results) == results.Len():
						o.sources[result] = append(o.sources[result], source{n.Results[i], -1})
					case len(n.Results) == 1:
						o.sources[result] = append(o.sources[result], source{n.Results[0], i})
					}
				}
			}
			return true
		})
	}
	for _, fn := range pv.order {
		if fn.decl != nil && fn.decl.Body == body {
			o.sig = fn.obj.Type().(*types.Signature)
		}
	}
	var results *types.Tuple
	if o.sig != nil {
		results = o.sig.Results()
	}
	frame(body, results)
	// The parameters of a literal used in place are assigned the arguments
	// of its calls, which are all in the body. Those of any other literal
	// could be given anything.
	bound, _ := literalUses(pv.info, body)
	o.bound = bound
	inPlace := map[*ast.FuncLit]bool{}
	for _, lit := range bound {
		inPlace[lit] = true
	}
	ast.Inspect(body, func(n ast.Node) bool {
		call, ok := n.(*ast.CallExpr)
		if !ok {
			return true
		}
		var lit *ast.FuncLit
		switch fun := ast.Unparen(call.Fun).(type) {
		case *ast.FuncLit:
			lit = fun
		case *ast.Ident:
			lit = bound[variable(fun)]
		}
		if lit == nil {
			return true
		}
		inPlace[lit] = true
		sig := pv.info.TypeOf(lit).(*types.Signature)
		bound, ok := bindArgs(pv.info, call, paramsOf(sig), sig.Variadic())
		for i, param := range paramsOf(sig) {
			// A pack is a slice, whose elements have no origin of their
			// own here.
			if !ok || bound[i].packed {
				o.unknown[param] = true
				continue
			}
			o.sources[param] = append(o.sources[param], source{bound[i].expr, -1})
			o.args[param] = append(o.args[param], source{bound[i].expr, -1})
		}
		return true
	})
	ast.Inspect(body, func(n ast.Node) bool {
		if lit, ok := n.(*ast.FuncLit); ok && !inPlace[lit] {
			for param := range pv.info.TypeOf(lit).(*types.Signature).Params().Variables() {
				o.open[param] = true
			}
		}
		return true
	})
	return o
}

// literalAt returns the innermost function literal of the body whose text
// holds a position, or nil.
func (o *origins) literalAt(pos token.Pos) *ast.FuncLit {
	var inner *ast.FuncLit
	for _, lit := range o.lits {
		if lit.Pos() <= pos && pos < lit.End() && (inner == nil || lit.Pos() > inner.Pos()) {
			inner = lit
		}
	}
	return inner
}

// frameAt returns the body of the function or literal whose own code holds
// a position, outside the literals written in it.
func (o *origins) frameAt(pos token.Pos) *ast.BlockStmt {
	if lit := o.literalAt(pos); lit != nil {
		return lit.Body
	}
	return o.body
}

// homeOf returns the body that declares a variable: the declared function's
// for its parameters, results, and locals, a literal's for its own.
func (o *origins) homeOf(variable *types.Var) *ast.BlockStmt {
	return o.frameAt(variable.Pos())
}

// outermostIn returns the outermost function literal written inside home
// whose text holds a position, or nil when the position is in home's own
// code.
func (o *origins) outermostIn(home *ast.BlockStmt, pos token.Pos) *ast.FuncLit {
	var outer *ast.FuncLit
	for _, lit := range o.lits {
		if home.Pos() <= lit.Pos() && lit.End() <= home.End() && lit.Pos() <= pos && pos < lit.End() &&
			(outer == nil || lit.Pos() < outer.Pos()) {
			outer = lit
		}
	}
	return outer
}

// tracked reports whether the origin of a variable is followed along the
// paths of its home: a local error variable that is never assigned in a
// way the collection does not understand, and is assigned only in its home
// or in a literal deferred there. A literal deferred where it is written
// runs when its frame returns, after every use in the frame's own code on
// that path, and so does everything made inside it; what it assigns
// reaches no such use. Any other literal may run between two statements
// of its home, and so a variable it assigns is decided from every
// assignment.
func (o *origins) tracked(variable *types.Var) bool {
	if known, ok := o.isTracked[variable]; ok {
		return known
	}
	home := o.homeOf(variable)
	tracked := isError(variable.Type()) && home != nil && !o.unknown[variable] &&
		(variable.Pkg() == nil || variable.Parent() != variable.Pkg().Scope()) &&
		!slices.ContainsFunc(o.sites[variable], func(at token.Pos) bool {
			lit := o.outermostIn(home, at)
			return lit != nil && !o.deferred[lit]
		})
	o.isTracked[variable] = tracked
	return tracked
}

// alongPath reports whether a use of a variable at a position is decided
// along the paths: the variable is tracked and the use is in the own code
// of its home.
func (o *origins) alongPath(variable *types.Var, pos token.Pos) bool {
	return o.tracked(variable) && o.frameAt(pos) == o.homeOf(variable)
}

// defKind says what a definition assigns.
type defKind int

const (
	// defExpr assigns src.
	defExpr defKind = iota
	// defNil assigns nil: a var without a value, or a named result on
	// entry.
	defNil
	// defParam is a parameter of the declared function on entry.
	defParam
	// defArgs is a parameter of a literal used in place on entry, which
	// holds one of the arguments of its calls; see origins.args.
	defArgs
	// defOpen is a parameter of a literal that is not used in place, which
	// could be given anything.
	defOpen
)

// def is one definition of a tracked variable: an assignment, or what the
// variable holds on entry to its home.
type def struct {
	variable *types.Var
	kind     defKind
	src      source
	pos      token.Pos
}

// flow holds the reaching definitions of the tracked variables of one home,
// computed over the control-flow graph of its body.
type flow struct {
	defs  []*def
	byVar map[*types.Var][]int
	// made holds the definitions each node of the graph makes, in order.
	made map[ast.Node][]int
	in   map[*cfg.Block]bitset
	// nodes holds every node of the graph with its block and its index
	// there.
	nodes []placed
}

type placed struct {
	node  ast.Node
	block *cfg.Block
	index int
}

// bitset is a set of definitions by index.
type bitset []uint64

func (b bitset) add(i int)     { b[i/64] |= 1 << (i % 64) }
func (b bitset) clone() bitset { return slices.Clone(b) }
func (b bitset) union(c bitset) (changed bool) {
	for i := range b {
		if b[i]|c[i] != b[i] {
			b[i] |= c[i]
			changed = true
		}
	}
	return changed
}

// apply makes the definitions a node makes on a set: each kills the other
// definitions of its variable.
func (f *flow) apply(set bitset, node ast.Node) {
	for _, i := range f.made[node] {
		for _, other := range f.byVar[f.defs[i].variable] {
			set[other/64] &^= 1 << (other % 64)
		}
		set.add(i)
	}
}

// flowOf returns the flow of a home, built on first use.
func (pv *pkgVerifier) flowOf(o *origins, home *ast.BlockStmt) *flow {
	if f, ok := o.flows[home]; ok {
		return f
	}
	f := &flow{byVar: map[*types.Var][]int{}, made: map[ast.Node][]int{}, in: map[*cfg.Block]bitset{}}
	o.flows[home] = f
	define := func(d *def) int {
		f.defs = append(f.defs, d)
		i := len(f.defs) - 1
		f.byVar[d.variable] = append(f.byVar[d.variable], i)
		return i
	}
	ours := func(variable *types.Var) bool {
		return variable != nil && o.tracked(variable) && o.homeOf(variable) == home
	}
	// What each variable of the home holds on entry.
	var entry []int
	var sig *types.Signature
	lit := o.literalAt(home.Pos())
	if lit != nil && lit.Body == home {
		sig = pv.info.TypeOf(lit).(*types.Signature)
	} else {
		sig = o.sig
	}
	if sig != nil {
		var params []*types.Var
		if sig.Recv() != nil {
			params = append(params, sig.Recv())
		}
		params = append(params, paramsOf(sig)...)
		for _, param := range params {
			if !ours(param) {
				continue
			}
			kind := defParam
			switch {
			case lit == nil || lit.Body != home:
			case o.open[param]:
				kind = defOpen
			default:
				kind = defArgs
			}
			entry = append(entry, define(&def{variable: param, kind: kind, pos: home.Pos()}))
		}
		for result := range sig.Results().Variables() {
			if ours(result) {
				entry = append(entry, define(&def{variable: result, kind: defNil, pos: home.Pos()}))
			}
		}
	}
	// Without a signature, a variable declared before the body is a
	// parameter or a result whose kind is not known, and holds anything.
	graph := cfg.New(home, func(*ast.CallExpr) bool { return true })
	for _, block := range graph.Blocks {
		for index, node := range block.Nodes {
			f.nodes = append(f.nodes, placed{node, block, index})
			f.made[node] = pv.defsOf(o, node, ours, define)
		}
	}
	if sig == nil {
		seen := map[*types.Var]bool{}
		for _, d := range f.defs {
			seen[d.variable] = true
		}
		ast.Inspect(home, func(n ast.Node) bool {
			if id, ok := n.(*ast.Ident); ok {
				if variable, isVar := pv.info.Uses[id].(*types.Var); isVar && !seen[variable] && ours(variable) && variable.Pos() < home.Pos() {
					seen[variable] = true
					entry = append(entry, define(&def{variable: variable, kind: defParam, pos: home.Pos()}))
				}
			}
			return true
		})
	}
	// The definitions that reach the start of each block: the least fixed
	// point of the union over the edges into it.
	n := len(f.defs)
	for _, block := range graph.Blocks {
		f.in[block] = make(bitset, (n+63)/64)
	}
	start := graph.Blocks[0]
	for _, i := range entry {
		f.in[start].add(i)
	}
	work := slices.Clone(graph.Blocks)
	for len(work) > 0 {
		block := work[len(work)-1]
		work = work[:len(work)-1]
		out := f.in[block].clone()
		for _, node := range block.Nodes {
			f.apply(out, node)
		}
		for _, succ := range block.Succs {
			if f.in[succ].union(out) && !slices.Contains(work, succ) {
				work = append(work, succ)
			}
		}
	}
	return f
}

// defsOf returns the definitions of tracked variables of a home that a node
// of its control-flow graph makes. go/cfg makes a node of every simple
// statement, every ValueSpec, and every condition, tag, and case, so none
// assigns a variable after it reads one. Nothing inside a function literal
// is part of the node.
func (pv *pkgVerifier) defsOf(o *origins, node ast.Node, ours func(*types.Var) bool, define func(*def) int) []int {
	var made []int
	if expr, ok := node.(ast.Expr); ok && o.ranged[expr] {
		// go/cfg puts the key and the value of a range once before the
		// loop, not at each iteration, which would be wrong for a tracked
		// variable. A range target is unknown, so none is tracked.
		if id, isIdent := ast.Unparen(expr).(*ast.Ident); isIdent {
			if variable, isVar := pv.info.ObjectOf(id).(*types.Var); isVar && o.tracked(variable) {
				panic(fmt.Sprintf("vego: internal error: %s is assigned by a range and followed along the paths", id.Name))
			}
		}
	}
	targetOf := func(e ast.Expr) *types.Var {
		id, ok := ast.Unparen(e).(*ast.Ident)
		if !ok {
			return nil
		}
		variable, _ := pv.info.ObjectOf(id).(*types.Var)
		if !ours(variable) {
			return nil
		}
		return variable
	}
	ast.Inspect(node, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.FuncLit:
			return false
		case *ast.AssignStmt:
			if n.Tok != token.ASSIGN && n.Tok != token.DEFINE {
				break
			}
			for i, target := range n.Lhs {
				variable := targetOf(target)
				switch {
				case variable == nil:
				case len(n.Rhs) == len(n.Lhs):
					made = append(made, define(&def{variable: variable, src: source{n.Rhs[i], -1}, pos: target.Pos()}))
				case len(n.Rhs) == 1:
					made = append(made, define(&def{variable: variable, src: source{n.Rhs[0], i}, pos: target.Pos()}))
				default:
					panic("vego: internal error: an assignment of several values to a tracked variable has neither one value nor one for each")
				}
			}
		case *ast.ValueSpec:
			for i, name := range n.Names {
				variable := targetOf(name)
				switch {
				case variable == nil:
				case len(n.Values) == 0:
					made = append(made, define(&def{variable: variable, kind: defNil, pos: name.Pos()}))
				case len(n.Values) == len(n.Names):
					made = append(made, define(&def{variable: variable, src: source{n.Values[i], -1}, pos: name.Pos()}))
				default:
					made = append(made, define(&def{variable: variable, src: source{n.Values[0], i}, pos: name.Pos()}))
				}
			}
		}
		return true
	})
	return made
}

// reaching returns the definitions of a tracked variable that reach a use
// at a position in the own code of its home. ok is false when the use is in
// code the graph finds unreachable, where the use is decided from every
// assignment. Every position in the own code of a body is in some node,
// and the declaration of a variable is on every path to its uses, so
// anything else is a fault of the analysis and panics.
func (pv *pkgVerifier) reaching(o *origins, variable *types.Var, pos token.Pos) (defs []*def, ok bool) {
	f := pv.flowOf(o, o.homeOf(variable))
	var at *placed
	for i := range f.nodes {
		p := &f.nodes[i]
		if p.node.Pos() <= pos && pos < p.node.End() && (at == nil || p.node.End()-p.node.Pos() < at.node.End()-at.node.Pos()) {
			at = p
		}
	}
	if at == nil {
		panic(fmt.Sprintf("vego: internal error: no node of the control-flow graph holds the use of %s at %s", variable.Name(), pv.pass.Fset.Position(pos)))
	}
	if !at.block.Live {
		return nil, false
	}
	set := f.in[at.block].clone()
	for _, node := range at.block.Nodes[:at.index] {
		f.apply(set, node)
	}
	for _, i := range f.byVar[variable] {
		if set[i/64]&(1<<(i%64)) != 0 {
			defs = append(defs, f.defs[i])
		}
	}
	if len(defs) == 0 {
		panic(fmt.Sprintf("vego: internal error: no definition of %s reaches its use at %s", variable.Name(), pv.pass.Fset.Position(pos)))
	}
	return defs, true
}

// search holds what is being decided, which settles a definition or a
// variable that depends on itself: it then brings nothing unknown of its
// own, and the answer rests on what else it depends on.
type search struct {
	vars map[*types.Var]bool
	defs map[*def]bool
}

func newSearch() *search { return &search{vars: map[*types.Var]bool{}, defs: map[*def]bool{}} }

// knownError reports whether an error expression in a function body has a
// known origin where it is written: nil, a new error, an error variable of
// this package or of another that always holds a new error into which
// nothing of unknown origin went, the result of a function that only
// returns such errors, or a local variable of which every definition that
// can reach the expression gives it a known origin.
func (pv *pkgVerifier) knownError(o *origins, e ast.Expr, index int) bool {
	return pv.knownErrorIn(o, e, index, newSearch())
}

// knownErrorIn is knownError within a search. nil and a call of errors.New
// or fmt.Errorf are known. Another call is known by what its callee
// publishes or its contract vouches for, a call through a value by the
// contract of the value's type, and a call of a literal is not known. A
// local variable is known by the definitions that reach the expression,
// or by every assignment to it, and a package-level one by its sentinel.
func (pv *pkgVerifier) knownErrorIn(o *origins, e ast.Expr, index int, s *search) bool {
	e = ast.Unparen(e)
	if pv.info.Types[e].IsNil() {
		return true
	}
	switch e := e.(type) {
	case *ast.CallExpr:
		callee := typeutil.StaticCallee(pv.info, e)
		if errorConstructor(callee) {
			return true
		}
		// What a function is known for is the errors it returns, not
		// whatever else it returns that happens to be assigned to an error.
		result := pv.info.TypeOf(e)
		at := 0
		if tuple, ok := result.(*types.Tuple); ok && index >= 0 && index < tuple.Len() {
			result, at = tuple.At(index).Type(), index
		}
		// A call of a literal runs its body, whose returns are not judged
		// here; it is no call through a value, whatever its type says.
		if calledLiteral(pv.info, o.bound, e) != nil {
			return false
		}
		if callee == nil && isError(result) {
			return pv.vouchedThroughValue(e, at)
		}
		return callee != nil && isError(result) && (pv.returnsKnownErrors(callee) || pv.vouchedResult(callee, at))
	case *ast.Ident:
		variable, ok := pv.info.ObjectOf(e).(*types.Var)
		return ok && index < 0 && isError(variable.Type()) && pv.knownAt(o, variable, e.Pos(), s)
	case *ast.SelectorExpr:
		variable := pv.namedVariable(e)
		return variable != nil && index < 0 && isError(variable.Type()) && pv.knownVariable(o, variable, s)
	}
	return false
}

// knownAt reports whether an error variable has a known origin at a use:
// along the paths when it is tracked and used in its home's own code, and
// otherwise from every assignment to it.
func (pv *pkgVerifier) knownAt(o *origins, variable *types.Var, pos token.Pos, s *search) bool {
	if r, ok := pv.homemadeValue(variable); ok {
		pv.rely(r.keys)
		return true
	}
	if o.alongPath(variable, pos) {
		if defs, ok := pv.reaching(o, variable, pos); ok {
			for _, d := range defs {
				if !pv.knownDef(o, d, s) {
					return false
				}
			}
			return true
		}
	}
	return pv.knownVariable(o, variable, s)
}

// knownDef reports whether a definition gives its variable a known origin.
// One found unknown stays so until findKnownReturns finds another function
// that returns only errors of known origin; one found known is kept only
// when the answer rested on nothing being decided, since a definition being
// decided counts as known meanwhile.
func (pv *pkgVerifier) knownDef(o *origins, d *def, s *search) bool {
	if known, ok := o.found[d]; ok {
		return known
	}
	if s.defs[d] {
		return true
	}
	// An answer found when nothing is being decided rests on no assumption.
	idle := len(s.vars) == 0 && len(s.defs) == 0
	s.defs[d] = true
	defer delete(s.defs, d)
	var known bool
	switch d.kind {
	case defNil:
		known = true
	case defParam, defOpen:
		known = false
	case defArgs:
		known = !slices.ContainsFunc(o.args[d.variable], func(arg source) bool {
			return !pv.knownErrorIn(o, arg.expr, arg.index, s)
		})
	case defExpr:
		known = pv.knownErrorIn(o, d.src.expr, d.src.index, s)
	}
	if !known || idle {
		o.found[d] = known
	}
	return known
}

// knownVariable reports whether an error variable only ever holds errors of
// known origin, from every assignment to it in the function.
func (pv *pkgVerifier) knownVariable(o *origins, variable *types.Var, s *search) bool {
	if r, ok := pv.homemadeValue(variable); ok {
		pv.rely(r.keys)
		return true
	}
	switch {
	case s.vars[variable]:
		return true
	case o.unknown[variable] || o.open[variable] || (variable.Pkg() != nil && variable.Parent() == variable.Pkg().Scope()) || pv.isParameter[variable]:
		return false
	}
	s.vars[variable] = true
	defer delete(s.vars, variable)
	for _, from := range o.sources[variable] {
		if !pv.knownErrorIn(o, from.expr, from.index, s) {
			return false
		}
	}
	return true
}

// vouchedThroughValue reports whether a call through an interface value or
// a function value returns errors of known origin in the result with the
// given index: whether the contract it is called under vouches for them,
// an entry of a trust file or a contract in source with a Vouches
// annotation. Every value that code which is not verified hands over is
// claimed to meet that contract, and every value that verified code makes
// is checked against it where it is made.
func (pv *pkgVerifier) vouchedThroughValue(call *ast.CallExpr, index int) bool {
	var fn *funcInfo
	switch method, value := throughValue(pv.info, call); {
	case method != nil:
		fn = pv.methodContract(method)
	case value:
		fn = pv.valueContract(pv.info.TypeOf(call.Fun))
	}
	return fn != nil && fn.vouches[index]
}

// returnsKnownErrors reports whether every error a function returns has a
// known origin. Only verified functions qualify: for one of this package the
// answer is computed from its body, for one of another package it was
// published with its contract.
func (pv *pkgVerifier) returnsKnownErrors(callee *types.Func) bool {
	if fn := pv.funcs[callee]; fn != nil {
		return pv.knownReturns[fn]
	}
	imported := pv.importedContract(callee)
	return imported != nil && imported.imported.KnownErrors
}

// vouchedResult reports whether a function is trusted and its contract
// vouches for the errors of the result with the given index. A contract that
// cannot be used makes the call itself an error, so its claim is read here
// as written.
func (pv *pkgVerifier) vouchedResult(callee *types.Func, index int) bool {
	if own := pv.funcs[callee]; (own != nil && own.annotated()) || pv.importedContract(callee) != nil {
		return false
	}
	fn := pv.trustedContract(callee)
	return fn != nil && fn.vouches[index]
}

// findKnownReturns decides for every annotated function of the package
// whether all errors it returns have a known origin. A function qualifies
// only through functions that qualify, so the answer is the least fixed
// point: functions that only return each other's errors do not qualify.
func (pv *pkgVerifier) findKnownReturns() {
	for _, fn := range pv.order {
		for _, param := range fn.params {
			pv.isParameter[param] = true
		}
	}
	for changed := true; changed; {
		changed = false
		for _, fn := range pv.order {
			if pv.knownReturns[fn] || !fn.annotated() || fn.decl.Body == nil || !pv.returnsKnown(pv.originsOf(fn.decl.Body), fn.decl.Body, fn.results) {
				continue
			}
			pv.knownReturns[fn], changed = true, true
			// A definition found unknown may have been a call of fn, so
			// nothing found before this holds now.
			for _, o := range pv.origins {
				clear(o.found)
			}
		}
	}
}

// returnsKnown reports whether every return statement of a body, of a
// function or of a literal, returns errors of known origin in its results,
// given the origins o of the function the body is part of. Each return is
// judged by the origins where it stands. A function can return in no other
// way with values it chose: a panic recovered by a deferred call would
// return what the named results hold where it panicked, but recover is
// not supported, and in a function that verifies nothing panics.
func (pv *pkgVerifier) returnsKnown(o *origins, body *ast.BlockStmt, results []*types.Var) bool {
	known := true
	check := func(e ast.Expr, index int) {
		known = known && pv.knownError(o, e, index)
	}
	// A deferred literal may assign a named result after a return has set
	// it, so a result that a literal assigns returns whatever it may be
	// assigned anywhere: the variable decides, not the returned value. Any
	// literal counts, not only one deferred by the function, which can
	// only make fewer functions qualify.
	late := map[*types.Var]bool{}
	ast.Inspect(body, func(n ast.Node) bool {
		if lit, ok := n.(*ast.FuncLit); ok {
			ast.Inspect(lit.Body, func(inner ast.Node) bool {
				if assign, ok := inner.(*ast.AssignStmt); ok {
					for _, lhs := range assign.Lhs {
						if id, ok := ast.Unparen(lhs).(*ast.Ident); ok {
							if variable, ok := pv.info.ObjectOf(id).(*types.Var); ok && slices.Contains(results, variable) {
								late[variable] = true
							}
						}
					}
				}
				return true
			})
		}
		return true
	})
	ast.Inspect(body, func(n ast.Node) bool {
		if _, isLiteral := n.(*ast.FuncLit); isLiteral {
			return false
		}
		ret, ok := n.(*ast.ReturnStmt)
		if !ok {
			return true
		}
		for i, result := range results {
			switch {
			case !isError(result.Type()):
			case late[result]:
				known = known && pv.knownVariable(o, result, newSearch())
			case len(ret.Results) == 0:
				// A bare return yields the named result as it is there.
				known = known && pv.knownAt(o, result, ret.Pos(), newSearch())
			case len(ret.Results) == len(results):
				check(ret.Results[i], -1)
			default:
				check(ret.Results[0], i)
			}
		}
		return true
	})
	return known
}
