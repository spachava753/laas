package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"maps"
	"slices"
	"strings"

	"golang.org/x/tools/go/cfg"
	"golang.org/x/tools/go/types/typeutil"

	"github.com/spachava753/laas/vego/internal/logic"
)

// The ownership invariant HI (F27, step 3; ROADMAP, Ownership in source):
// every reference to memory an owner owns that is stored in memory lies in
// the owned cell that holds it, and no two owned fields refer to
// overlapping memory. Every verified function keeps it by refusing, where
// it stands, the operation that would break it; that is what this analysis
// decides, without Z3, over the control-flow graph of the body.
//
// Each value a local or a parameter holds has a kind, a set of these:
//
//   - a parameter p: the value refers to memory of p (p itself, a slice of
//     it, an address in it), reached other than through an owned field;
//   - a tag: memory this function made at an allocation site, or that a
//     call returned as new and not escaped; a site has two tags, its most
//     recent execution and every earlier one;
//   - inside a root: memory an owner owns, read through an owned field of
//     what the root refers to (a parameter or a tag), or new memory that was
//     stored into an owned field;
//   - unknown, with why.
//
// A value with none of these is outside. A read of a cell that is not
// owned (an element, a map value, a field that is not owned, the struct a
// pointer points to) gives an outside value: by HI no such cell holds a
// reference to a part. Each tag has a status, new, owned (by a root), or
// escaped; a value that holds an owned tag is inside that tag's root.
//
// The rules (R1 to R5 of the design):
//
//   - R1: a store into an owned field may take new memory, under the case
//     of checkOwnedStore that admits memory made since entry, only when the
//     value is made of tags that are all new (madeHere); its tags are then
//     owned by the owner's root.
//   - R2: an inside value is never stored into memory but by R1's store
//     back into its own cell, never captured by a literal that may outlive
//     the call, and handed to a callee only for a parameter the callee
//     keeps nothing of.
//   - R3: a tag stored into memory, captured by such a literal, or handed
//     to a parameter that is kept, has escaped.
//   - R4: a function keeps a parameter when it stores, captures, or hands
//     to a kept parameter a value of the parameter's kind or inside it; a
//     result flows from the parameters whose kinds it has, and is new when
//     it holds only tags that are new.
//   - R5: a result inside a parameter is allowed when the contract says so
//     with within(r, p); a result inside a tag when that tag is still new
//     and no other result holds it (F12).

// ownTag is an allocation site, or a call that returns new memory, at its
// most recent execution or at every earlier one.
type ownTag struct {
	site ast.Node
	old  bool
}

// ownRoot is what an inside value is owned through: a parameter, or a tag.
type ownRoot struct {
	param *types.Var
	tag   ownTag
	// expr is the owner as written, for a message, when it is neither:
	// one read from memory.
	expr ast.Expr
}

// ownKind is the kind of a value.
type ownKind struct {
	params  map[*types.Var]bool
	tags    map[ownTag]bool
	inside  map[ownRoot]bool
	unknown string
	// scoped, when set, says that the value is, holds, or was converted
	// from a value of a scoped type (scoped.go), which verified code never
	// keeps: it names the value as written, and decl is the declaration.
	scoped string
	decl   *scopedDecl
	// throughCall holds the roots of inside that an error holds only
	// because a call made on what the owner owns returned it, on every
	// path: the error of fmt.Fprint(r.out, ...) may hold what r.out holds.
	// A root that verified code put into an error, by a conversion, a
	// literal, or errors.New and fmt.Errorf, also through a verified call
	// that hands its argument back, is not one (F19 of the reviews of S3
	// and S4 of F33).
	throughCall map[ownRoot]bool
}

func (k ownKind) holds() bool {
	return len(k.params) > 0 || len(k.tags) > 0 || len(k.inside) > 0 || k.unknown != ""
}

// union returns the kind of a value that may be either.
func (k ownKind) union(o ownKind) ownKind {
	out := ownKind{params: maps.Clone(k.params), tags: maps.Clone(k.tags), inside: maps.Clone(k.inside), unknown: firstReason(k.unknown, o.unknown),
		scoped: k.scoped, decl: k.decl}
	if out.scoped == "" {
		out.scoped, out.decl = o.scoped, o.decl
	}
	add := func(m *map[*types.Var]bool, from map[*types.Var]bool) {
		for key := range from {
			if *m == nil {
				*m = map[*types.Var]bool{}
			}
			(*m)[key] = true
		}
	}
	add(&out.params, o.params)
	for t := range o.tags {
		if out.tags == nil {
			out.tags = map[ownTag]bool{}
		}
		out.tags[t] = true
	}
	for r := range o.inside {
		if out.inside == nil {
			out.inside = map[ownRoot]bool{}
		}
		out.inside[r] = true
	}
	// A root is through a call in the union only when it is on each side
	// that holds it.
	for r := range out.inside {
		if (!k.inside[r] || k.throughCall[r]) && (!o.inside[r] || o.throughCall[r]) {
			if out.throughCall == nil {
				out.throughCall = map[ownRoot]bool{}
			}
			out.throughCall[r] = true
		}
	}
	return out
}

func (k ownKind) equal(o ownKind) bool {
	return maps.Equal(k.params, o.params) && maps.Equal(k.tags, o.tags) && maps.Equal(k.inside, o.inside) && k.unknown == o.unknown && k.scoped == o.scoped &&
		maps.Equal(k.throughCall, o.throughCall)
}

// The statuses of a tag, in the order a join takes the worse.
const (
	tagNew = iota
	tagOwned
	tagEscaped
)

type tagStatus struct {
	state int
	root  ownRoot
	why   string
}

// ownFact is what holds at a point.
type ownFact struct {
	vars   map[*types.Var]ownKind
	status map[ownTag]tagStatus
}

func (f ownFact) clone() ownFact {
	return ownFact{vars: maps.Clone(f.vars), status: maps.Clone(f.status)}
}

// join adds what another fact says, and reports whether that changed f.
func (f *ownFact) join(g ownFact) bool {
	changed := false
	for variable, kind := range g.vars {
		joined := f.vars[variable].union(kind)
		if !joined.equal(f.vars[variable]) {
			f.vars[variable] = joined
			changed = true
		}
	}
	for tag, s := range g.status {
		if was, ok := f.status[tag]; !ok || s.state > was.state {
			f.status[tag] = s
			changed = true
		}
	}
	return changed
}

// ownRefusal is an operation the analysis refuses.
type ownRefusal struct {
	pos   token.Pos
	class refusal
	msg   string
}

// ownResult is what the summary says of a result.
type ownResult struct {
	fresh   bool
	from    map[*types.Var]bool
	inside  map[*types.Var]bool
	unknown bool
}

// ownFlow is the analysis of one body.
type ownFlow struct {
	// made holds the right-hand sides of stores into owned fields that are
	// made of tags that are all new where the store stands.
	made map[ast.Expr]bool
	why  map[ast.Expr]string
	// operands holds, for each call, its operands with their kinds where
	// the call stands, for R6 (checkOwnArguments).
	operands  map[*ast.CallExpr][]ownOperand
	refusals  []ownRefusal
	keeps     map[*types.Var]bool
	results   []ownResult
	reported  map[string]bool
	emitting  bool
	deferred  []*ast.FuncLit
	litAssign map[*types.Var]bool
}

func (fl *ownFlow) refuse(pos token.Pos, class refusal, format string, args ...any) {
	if !fl.emitting {
		return
	}
	msg := fmt.Sprintf(format, args...)
	key := fmt.Sprintf("%d %s", pos, msg)
	if fl.reported[key] {
		return
	}
	fl.reported[key] = true
	fl.refusals = append(fl.refusals, ownRefusal{pos: pos, class: class, msg: msg})
}

// ownsAnything reports whether the analysis has anything to decide in a
// body: whether any expression of it has a type that reaches an owner of
// the project. A function that meets none pays nothing.
func (v *fnVerifier) ownsAnything(body ast.Node) bool {
	found := false
	ast.Inspect(body, func(n ast.Node) bool {
		if found {
			return false
		}
		if e, ok := n.(ast.Expr); ok {
			if t := v.info.TypeOf(e); t != nil && (reachesSourceOwner(t, map[types.Type]bool{}) != nil || holdsScoped(t) != nil) {
				found = true
			}
		}
		return true
	})
	if !found && v.fn != nil {
		for _, param := range slices.Concat(v.fn.params, v.fn.results) {
			if reachesSourceOwner(param.Type(), map[types.Type]bool{}) != nil || holdsScoped(param.Type()) != nil {
				found = true
			}
		}
	}
	return found
}

// ownOrigins returns the analysis of the declared function being verified,
// or nil when it meets no owner of the project.
func (v *fnVerifier) ownOrigins() *ownFlow {
	if v.ownFlowDone != nil || v.ownFlowNone {
		return v.ownFlowDone
	}
	body := v.bodyOrigin()
	if body == nil || !v.ownForce && !v.ownsAnything(body) {
		v.ownFlowNone = true
		return nil
	}
	fl := &ownFlow{made: map[ast.Expr]bool{}, why: map[ast.Expr]string{}, operands: map[*ast.CallExpr][]ownOperand{}, keeps: map[*types.Var]bool{}, reported: map[string]bool{}, litAssign: map[*types.Var]bool{}}
	v.ownFlowDone = fl
	entry := ownFact{vars: map[*types.Var]ownKind{}, status: map[ownTag]tagStatus{}}
	if v.fn != nil {
		for _, param := range v.fn.params {
			entry.vars[param] = ownKind{params: map[*types.Var]bool{param: true}}
		}
	}
	ast.Inspect(body, func(n ast.Node) bool {
		if d, ok := n.(*ast.DeferStmt); ok {
			if lit, isLit := ast.Unparen(d.Call.Fun).(*ast.FuncLit); isLit {
				fl.deferred = append(fl.deferred, lit)
			}
		}
		return true
	})
	graph := cfg.New(body, func(*ast.CallExpr) bool { return true })
	in := map[*cfg.Block]*ownFact{}
	for _, block := range graph.Blocks {
		empty := ownFact{vars: map[*types.Var]ownKind{}, status: map[ownTag]tagStatus{}}
		in[block] = &empty
	}
	if len(graph.Blocks) > 0 {
		in[graph.Blocks[0]].join(entry)
	}
	run := func() {
		work := slices.Clone(graph.Blocks)
		for len(work) > 0 {
			block := work[0]
			work = work[1:]
			out := in[block].clone()
			for _, node := range block.Nodes {
				v.ownTransfer(fl, node, &out)
			}
			for _, succ := range block.Succs {
				if in[succ].join(out) && !slices.Contains(work, succ) {
					work = append(work, succ)
				}
			}
		}
	}
	run()
	// Once the facts are fixed, each node is run once more from its fact,
	// to record what is decided where it stands and what is refused.
	fl.emitting = true
	for _, block := range graph.Blocks {
		fact := in[block].clone()
		for _, node := range block.Nodes {
			v.ownTransfer(fl, node, &fact)
		}
	}
	return fl
}

// ownTransfer applies what one node of the graph does.
func (v *fnVerifier) ownTransfer(fl *ownFlow, n ast.Node, f *ownFact) {
	if vars, operand := v.switchVars(n); vars != nil {
		// The variable of each clause of a type switch holds the operand,
		// or what it holds: what the operand is.
		kind := v.ownKindOf(fl, operand, f)
		for _, variable := range vars {
			f.vars[variable] = kind
		}
		return
	}
	switch n := n.(type) {
	case *ast.AssignStmt:
		if len(n.Lhs) == len(n.Rhs) {
			kinds := make([]ownKind, len(n.Rhs))
			for i, rhs := range n.Rhs {
				kinds[i] = v.ownKindOf(fl, rhs, f)
			}
			for i, lhs := range n.Lhs {
				v.ownAssign(fl, lhs, n.Rhs[i], kinds[i], f)
			}
			return
		}
		if len(n.Rhs) == 1 {
			kinds := v.ownResults(fl, n.Rhs[0], len(n.Lhs), f)
			for i, lhs := range n.Lhs {
				v.ownAssign(fl, lhs, n.Rhs[0], kinds[i], f)
			}
		}
	case *ast.ValueSpec:
		v.ownSpec(fl, n, f)
	case *ast.DeclStmt:
		if decl, ok := n.Decl.(*ast.GenDecl); ok {
			for _, spec := range decl.Specs {
				if value, ok := spec.(*ast.ValueSpec); ok {
					v.ownSpec(fl, value, f)
				}
			}
		}
	case *ast.ReturnStmt:
		v.ownReturn(fl, n, f)
	case *ast.DeferStmt:
		v.ownKindOf(fl, n.Call, f)
	case *ast.GoStmt:
		v.ownKindOf(fl, n.Call, f)
	case *ast.ExprStmt:
		v.ownKindOf(fl, n.X, f)
	case *ast.IncDecStmt, *ast.BranchStmt, *ast.LabeledStmt, *ast.EmptyStmt:
	case *ast.SendStmt:
		v.ownStoreMemory(fl, n.Value, v.ownKindOf(fl, n.Value, f), f, "sent on a channel")
	case ast.Expr:
		// A condition, or the ranged expression of a range statement, where
		// go/cfg puts the key and the value once before the loop: they are
		// read from what is ranged over, an outside value.
		kind := v.ownKindOf(fl, n, f)
		if rs := v.rangeOf(n); rs != nil {
			ranged := v.info.TypeOf(rs.X)
			for _, e := range []ast.Expr{rs.Key, rs.Value} {
				if id, ok := e.(*ast.Ident); ok && id.Name != "_" {
					if variable, isVar := v.info.ObjectOf(id).(*types.Var); isVar {
						f.vars[variable] = ownKind{}
						// Ranging over a string or an integer yields no
						// memory; over an inside slice by index, nothing.
						_ = ranged
					}
				}
			}
			_ = kind
		}
	}
}

// ownSpec is a var declaration.
func (v *fnVerifier) ownSpec(fl *ownFlow, s *ast.ValueSpec, f *ownFact) {
	switch {
	case len(s.Values) == len(s.Names):
		for i, name := range s.Names {
			v.ownAssign(fl, name, s.Values[i], v.ownKindOf(fl, s.Values[i], f), f)
		}
	case len(s.Values) == 1:
		kinds := v.ownResults(fl, s.Values[0], len(s.Names), f)
		for i, name := range s.Names {
			v.ownAssign(fl, name, s.Values[0], kinds[i], f)
		}
	default:
		for _, name := range s.Names {
			if variable, ok := v.info.ObjectOf(name).(*types.Var); ok {
				f.vars[variable] = ownKind{}
			}
		}
	}
}

// ownAssign applies an assignment of a value of a kind to a target.
func (v *fnVerifier) ownAssign(fl *ownFlow, lhs, rhs ast.Expr, kind ownKind, f *ownFact) {
	lhs = ast.Unparen(lhs)
	switch target := lhs.(type) {
	case *ast.Ident:
		if target.Name == "_" {
			return
		}
		variable, ok := v.info.ObjectOf(target).(*types.Var)
		if !ok {
			return
		}
		if v.boxed[variable] || variable.Parent() == v.pass.Pkg.Scope() {
			v.ownStoreMemory(fl, rhs, kind, f, "stored into "+target.Name+", which lives in memory")
			return
		}
		f.vars[variable] = kind
		return
	case *ast.SelectorExpr:
		selection := v.info.Selections[target]
		if selection != nil && selection.Kind() == types.FieldVal {
			holder := v.info.TypeOf(target.X)
			object, viaPointer := pointee(holder)
			if !viaPointer {
				object = holder
			}
			index := selection.Index()
			// The struct that declares the field, through promotions.
			declaring := object
			for _, i := range index[:len(index)-1] {
				if u, isStruct := declaring.Underlying().(*types.Struct); isStruct {
					declaring = u.Field(i).Type()
				}
			}
			if _, isPointer := pointee(declaring); !isPointer && ownedFieldAt(declaring, index[len(index)-1]) {
				v.ownStoreOwned(fl, target, rhs, kind, f)
				return
			}
			if !viaPointer && len(index) == 1 {
				// A field of a struct held in a local: part of its value.
				if variable := v.localVar(target.X); variable != nil && !v.boxed[variable] {
					f.vars[variable] = f.vars[variable].union(kind)
					return
				}
			}
		}
	}
	v.ownStoreMemory(fl, rhs, kind, f, "stored into memory at "+v.placeOf(lhs.Pos()))
}

// ownStoreMemory applies a store of a value into memory that is not an
// owned field: R2 refuses an inside value, and R3 makes its tags escape.
func (v *fnVerifier) ownStoreMemory(fl *ownFlow, at ast.Expr, kind ownKind, f *ownFact, where string) {
	kind = v.ownResolve(kind, f)
	pos := token.NoPos
	if at != nil {
		pos = at.Pos()
	}
	for root := range kind.inside {
		spelled := "it"
		if at != nil {
			spelled = types.ExprString(at)
		}
		fl.refuse(pos, rOwnsKept, "%s is memory that %s owns, %s; it may be read and written here, but not kept elsewhere: copy it, or do not declare the field owned",
			spelled, v.rootName(root), where)
		break
	}
	spelled := ""
	if lit, isLit := at.(*ast.CompositeLit); at != nil && (!isLit || lit.Type != nil) {
		spelled = types.ExprString(at)
	}
	v.refuseScoped(fl, pos, kind, where, spelled)
	v.ownKeep(fl, kind)
	v.ownEscape(kind, f, where)
}

// ownKeep records the parameters a kept value is of.
func (v *fnVerifier) ownKeep(fl *ownFlow, kind ownKind) {
	for param := range kind.params {
		fl.keeps[param] = true
	}
	for root := range kind.inside {
		if root.param != nil {
			fl.keeps[root.param] = true
		}
	}
}

// ownEscape makes the tags of a value escape.
func (v *fnVerifier) ownEscape(kind ownKind, f *ownFact, why string) {
	for tag := range kind.tags {
		if f.status[tag].state < tagEscaped {
			f.status[tag] = tagStatus{state: tagEscaped, why: why}
		}
	}
}

// ownStoreOwned applies a store into an owned field (R1).
func (v *fnVerifier) ownStoreOwned(fl *ownFlow, target *ast.SelectorExpr, rhs ast.Expr, kind ownKind, f *ownFact) {
	kind = v.ownResolve(kind, f)
	base := v.ownResolve(v.ownKindOf(fl, target.X, f), f)
	// Whatever is new and nothing else refers to may come to be owned.
	made := len(kind.tags) > 0 && len(kind.params) == 0 && len(kind.inside) == 0 && kind.unknown == ""
	for tag := range kind.tags {
		if f.status[tag].state != tagNew {
			made = false
		}
	}
	// Keyed by the target: the right-hand side of a tuple is one call for
	// every target.
	if fl.emitting {
		fl.made[target] = made
		fl.why[target] = v.ownWhyKind(kind, f)
	}
	root := v.rootOf(base)
	if root == (ownRoot{}) {
		root.expr = target.X
	}
	// An owner stored into its own owned field, or into one of what it
	// owns, would own itself: the row of an owner converted there holds
	// its own struct (the reviewer's program of step 4).
	for tag := range kind.tags {
		if base.tags[tag] || root.tag == tag {
			fl.refuse(target.Pos(), rOwnsSelf, "%s may come to hold %s itself, whose footprint would then lie in what it owns; an owner cannot own itself",
				types.ExprString(target), types.ExprString(rhs))
		}
	}
	for p := range kind.params {
		if base.params[p] || root.param == p {
			fl.refuse(target.Pos(), rOwnsSelf, "%s may come to hold %s itself, whose footprint would then lie in what it owns; an owner cannot own itself",
				types.ExprString(target), types.ExprString(rhs))
		}
	}
	// Every tag stored there is owned by the owner from now on, also one
	// beside what the field held, as the new array of an append.
	for tag := range kind.tags {
		f.status[tag] = tagStatus{state: tagOwned, root: root}
	}
	if made {
		return
	}
	// Anything else must lie within what the field holds, which Z3
	// decides; a value of another owner or of a parameter, which it cannot,
	// is kept by the function that stores it, as an owned field of
	// another root.
	sameRoot := false
	for r := range kind.inside {
		sameRoot = sameRoot || r == root
	}
	if !sameRoot {
		v.ownKeep(fl, kind)
	}
}

// rootOf returns the root an owner reached by a value of a kind is owned
// through: what it is inside, or the parameter or tag it is.
func (v *fnVerifier) rootOf(kind ownKind) ownRoot {
	for r := range kind.inside {
		return r
	}
	for p := range kind.params {
		return ownRoot{param: p}
	}
	for t := range kind.tags {
		return ownRoot{tag: t}
	}
	return ownRoot{}
}

// ownResolve turns the owned tags of a kind into inside of their roots.
func (v *fnVerifier) ownResolve(kind ownKind, f *ownFact) ownKind {
	out := ownKind{params: kind.params, inside: kind.inside, unknown: kind.unknown, scoped: kind.scoped, decl: kind.decl, throughCall: kind.throughCall}
	for tag := range kind.tags {
		if s := f.status[tag]; s.state == tagOwned {
			inside := maps.Clone(out.inside)
			if inside == nil {
				inside = map[ownRoot]bool{}
			}
			inside[s.root] = true
			out.inside = inside
			continue
		}
		if out.tags == nil {
			out.tags = map[ownTag]bool{}
		}
		out.tags[tag] = true
	}
	return out
}

// rootName names a root in a message.
func (v *fnVerifier) rootName(r ownRoot) string {
	if r.param != nil {
		return r.param.Name()
	}
	if r.tag.site != nil {
		made := "what is made"
		if e, ok := r.tag.site.(ast.Expr); ok {
			if t := v.info.TypeOf(e); t != nil {
				if object, isPointer := pointee(t); isPointer {
					t = object
				}
				made = "the " + types.TypeString(t, types.RelativeTo(v.pass.Pkg)) + " made"
			}
		}
		return made + " at " + v.placeOf(r.tag.site.Pos())
	}
	if r.expr != nil {
		return types.ExprString(r.expr)
	}
	return "an owner"
}

// ownSite gives the tag of a new execution of an allocation site: values
// that hold its most recent tag come to hold its earlier one.
func (v *fnVerifier) ownSite(site ast.Node, f *ownFact) ownKind {
	recent, earlier := ownTag{site: site}, ownTag{site: site, old: true}
	if s, ok := f.status[recent]; ok {
		if was := f.status[earlier]; s.state > was.state || f.status[earlier] == (tagStatus{}) {
			f.status[earlier] = s
		}
		for variable, kind := range f.vars {
			if kind.tags[recent] {
				next := ownKind{params: kind.params, inside: kind.inside, unknown: kind.unknown, tags: maps.Clone(kind.tags), scoped: kind.scoped, decl: kind.decl, throughCall: kind.throughCall}
				delete(next.tags, recent)
				next.tags[earlier] = true
				f.vars[variable] = next
			}
			for r := range kind.inside {
				if r.tag == recent {
					next := f.vars[variable]
					inside := maps.Clone(next.inside)
					delete(inside, r)
					inside[ownRoot{tag: earlier}] = true
					next.inside = inside
					f.vars[variable] = next
				}
			}
		}
		for tag, s := range f.status {
			if s.root.tag == recent {
				s.root.tag = earlier
				f.status[tag] = s
			}
		}
	}
	f.status[recent] = tagStatus{state: tagNew}
	return ownKind{tags: map[ownTag]bool{recent: true}}
}

// refersMemory reports whether a value of a type can refer to memory: it
// holds memory, or is an interface value or a function value.
func refersMemory(t types.Type) bool {
	if t == nil {
		return false
	}
	// An error may hold a value that a conversion made, as part of an
	// owner may be (F33): it refers to memory as any interface value does.
	if holdsMemory(t) || isIface(t) || isError(t) {
		return true
	}
	switch u := t.Underlying().(type) {
	case *types.Signature:
		return true
	case *types.Struct:
		// A struct that holds an interface value, an error, or a function
		// value by value refers to what that holds (S1 of F34, F6 of the
		// design review: a Holder{W: w} handed to a callee that stores
		// h.W kept the writer w without the callee counting as keeping h).
		for field := range u.Fields() {
			if refersMemory(field.Type()) {
				return true
			}
		}
	case *types.Array:
		return refersMemory(u.Elem())
	}
	return false
}

// ownKindOf returns the kind of the value of an expression, applying what
// its calls do.
func (v *fnVerifier) ownKindOf(fl *ownFlow, e ast.Expr, f *ownFact) ownKind {
	if e == nil {
		return ownKind{}
	}
	t := v.info.TypeOf(e)
	kind := v.ownKindOfAny(fl, e, f)
	// A value that is or holds a value of a scoped type, wherever it comes
	// from, a parameter, memory, or a call, as a struct that holds an
	// http.ResponseWriter and nothing else that refers to memory.
	scoped := holdsScoped(t)
	if t != nil && !refersMemory(t) && scoped == nil {
		return ownKind{}
	}
	if scoped != nil && kind.scoped == "" {
		kind.scoped, kind.decl = types.ExprString(e), scoped
	}
	return kind
}

// refuseScoped refuses keeping a value of a scoped kind: what was done
// with it says where.
func (v *fnVerifier) refuseScoped(fl *ownFlow, pos token.Pos, kind ownKind, where string, spelled ...string) {
	if kind.scoped == "" {
		return
	}
	what := kind.scoped
	if len(spelled) > 0 && spelled[0] != "" && spelled[0] != what {
		what = spelled[0] + ", which holds " + kind.scoped + ","
	}
	fl.refuse(pos, rScopedKept, "%s is or holds a %s.%s, which must not be used after the call that received it returns, and here it is %s, where a later call could use it; "+
		"pass it on only to calls that keep nothing of it", what, kind.decl.pkg, kind.decl.typ, where)
}

// ownKindOfAny is ownKindOf for an expression of any type. A variable has
// the kind its fact gives, unless it lives in memory or at package level,
// which is read from memory; a read through an owned field is inside its
// base's root, and any other read through a pointer, an element, a map
// value, or what a pointer points to is outside; slicing and a field of a
// value keep the kind of what they are taken from; & of a literal, a
// literal of a slice or a map, make, new, and append are sites; a literal
// used as a value keeps what it captures; a call is what its callee's
// summary or entry says; anything else is unknown.
func (v *fnVerifier) ownKindOfAny(fl *ownFlow, e ast.Expr, f *ownFact) ownKind {
	switch x := ast.Unparen(e).(type) {
	case *ast.Ident:
		variable, ok := v.info.ObjectOf(x).(*types.Var)
		if !ok || variable.Parent() == v.pass.Pkg.Scope() {
			return ownKind{}
		}
		if v.boxed[variable] {
			// A variable that lives in memory: what it holds was stored
			// there, and is read from memory.
			return ownKind{}
		}
		return f.vars[variable]
	case *ast.SelectorExpr:
		selection := v.info.Selections[x]
		if selection == nil {
			return ownKind{}
		}
		if selection.Kind() != types.FieldVal {
			base := v.ownKindOf(fl, x.X, f)
			if v.addressTaken(selection, x.X) {
				base = v.ownAddress(fl, x.X, f)
			}
			if len(v.ownResolve(base, f).inside) > 0 {
				fl.refuse(x.Pos(), rOwnsKept, "the method value %s holds memory that an owner owns, and a method value may keep it; call the method instead", types.ExprString(x))
			}
			// A method value of a scoped value holds it.
			return ownKind{unknown: "it is a method value", scoped: base.scoped, decl: base.decl}
		}
		base := v.ownResolve(v.ownKindOf(fl, x.X, f), f)
		holder := v.info.TypeOf(x.X)
		object, viaPointer := pointee(holder)
		if !viaPointer {
			object = holder
		}
		index := selection.Index()
		declaring := object
		for _, i := range index[:len(index)-1] {
			if u, isStruct := declaring.Underlying().(*types.Struct); isStruct {
				declaring = u.Field(i).Type()
			}
		}
		if ownedFieldAt(declaring, index[len(index)-1]) {
			// A read through an owned field is inside.
			if !base.holds() && !viaPointer {
				return ownKind{}
			}
			root := v.rootOf(base)
			if root == (ownRoot{}) {
				root.expr = x.X
			}
			return ownKind{inside: map[ownRoot]bool{root: true}}
		}
		if viaPointer {
			return ownKind{}
		}
		return base
	case *ast.IndexExpr:
		v.ownKindOf(fl, x.Index, f)
		if t := v.info.TypeOf(x.X); isSlice(t) || isMap(t) {
			v.ownKindOf(fl, x.X, f)
			return ownKind{}
		}
		return v.ownKindOf(fl, x.X, f)
	case *ast.SliceExpr:
		return v.ownKindOf(fl, x.X, f)
	case *ast.StarExpr:
		v.ownKindOf(fl, x.X, f)
		return ownKind{}
	case *ast.UnaryExpr:
		if x.Op == token.AND {
			if lit, ok := ast.Unparen(x.X).(*ast.CompositeLit); ok {
				v.ownLiteral(fl, lit, f, true)
				return v.ownSite(x, f)
			}
			return v.ownAddress(fl, x.X, f)
		}
		v.ownKindOf(fl, x.X, f)
		return ownKind{}
	case *ast.BinaryExpr:
		v.ownKindOf(fl, x.X, f)
		v.ownKindOf(fl, x.Y, f)
		return ownKind{}
	case *ast.CompositeLit:
		held := v.ownLiteral(fl, x, f, false)
		if t := v.info.TypeOf(x); isSlice(t) || isMap(t) {
			return v.ownSite(x, f)
		}
		// An owner held by value owns its owned fields' tags.
		if len(sourceOwnedFields(v.info.TypeOf(x))) > 0 {
			f.status[ownTag{site: x}] = tagStatus{state: tagNew}
			held = held.union(ownKind{tags: map[ownTag]bool{{site: x}: true}})
		}
		return held
	case *ast.FuncLit:
		// A literal bound to a variable that is only called runs where it
		// is called, which applies its body there (ownRunLiteral); it does
		// not outlive the call.
		for _, bound := range v.boundLits {
			if bound == x {
				return ownKind{}
			}
		}
		// A literal used as a value may run after the call: what it
		// captures is kept.
		v.ownCaptured(fl, x, f)
		return ownKind{unknown: "it is a function literal"}
	case *ast.TypeAssertExpr:
		// What an error holds is part of it: the result is what the
		// operand is, so a part of an owner taken out of an error is still
		// inside (F7 of the design review).
		return v.ownKindOf(fl, x.X, f)
	case *ast.CallExpr:
		return v.ownResults(fl, x, 1, f)[0]
	case *ast.BasicLit, *ast.KeyValueExpr:
		return ownKind{}
	}
	return ownKind{unknown: fmt.Sprintf("its origin at %s is not known", v.placeOf(e.Pos()))}
}

// ownLiteral applies the stores of a composite literal's elements into the
// memory or the value it makes; a struct literal's owned fields are stores
// into owned fields, decided where the literal stands (madeHere).
func (v *fnVerifier) ownLiteral(fl *ownFlow, lit *ast.CompositeLit, f *ownFact, inMemory bool) (held ownKind) {
	t := v.info.TypeOf(lit)
	object, _ := pointee(t)
	if object == nil {
		object = t
	}
	u, isStruct := object.Underlying().(*types.Struct)
	for i, element := range lit.Elts {
		value, index := element, i
		if pair, keyed := element.(*ast.KeyValueExpr); keyed {
			value = pair.Value
			if isStruct {
				name := pair.Key.(*ast.Ident).Name
				index = slices.IndexFunc(slices.Collect(u.Fields()), func(field *types.Var) bool { return field.Name() == name })
			} else {
				v.ownKindOf(fl, pair.Key, f)
			}
		}
		kind := v.ownResolve(v.ownKindOf(fl, value, f), f)
		if isStruct && ownedFieldAt(object, index) {
			made := len(kind.tags) > 0 && len(kind.params) == 0 && len(kind.inside) == 0 && kind.unknown == ""
			for tag := range kind.tags {
				if f.status[tag].state != tagNew {
					made = false
				}
			}
			if fl.emitting {
				fl.made[value] = made
				fl.why[value] = v.ownWhyKind(kind, f)
			}
			if made {
				for tag := range kind.tags {
					f.status[tag] = tagStatus{state: tagOwned, root: ownRoot{tag: ownTag{site: lit}}}
				}
			} else {
				v.ownKeep(fl, kind)
			}
			continue
		}
		if !isStruct {
			v.ownStoreMemory(fl, value, kind, f, "stored into what the literal at "+v.placeOf(lit.Pos())+" makes")
			continue
		}
		// A field that is not owned holds what it is given: in a struct
		// that &T{...} makes, a store into memory; in a value, part of
		// the value (F29 of the review of step 3a).
		if inMemory {
			v.ownStoreMemory(fl, value, kind, f, "stored into what the literal at "+v.placeOf(lit.Pos())+" makes")
			continue
		}
		held = held.union(kind)
	}
	return held
}

// ownCaptured applies what a function literal that may outlive the call
// does with what it captures: an inside value is refused, a tag escapes,
// and a parameter is kept.
func (v *fnVerifier) ownCaptured(fl *ownFlow, lit *ast.FuncLit, f *ownFact) {
	seen := map[*types.Var]bool{}
	ast.Inspect(lit.Body, func(n ast.Node) bool {
		id, ok := n.(*ast.Ident)
		if !ok {
			return true
		}
		variable, isVar := v.info.ObjectOf(id).(*types.Var)
		if !isVar || seen[variable] || variable.Pos() >= lit.Pos() && variable.Pos() < lit.End() {
			return true
		}
		seen[variable] = true
		kind := v.ownResolve(f.vars[variable], f)
		// A variable whose type is or holds a scoped value, as ownKindOf
		// marks an expression.
		if d := holdsScoped(variable.Type()); d != nil && kind.scoped == "" {
			kind.scoped, kind.decl = variable.Name(), d
		}
		for root := range kind.inside {
			fl.refuse(lit.Pos(), rOwnsKept, "the function literal at %s captures %s, which is memory that %s owns; read what the literal needs before it "+
				"and pass that in, or do not declare the field owned", v.placeOf(lit.Pos()), variable.Name(), v.rootName(root))
			break
		}
		v.refuseScoped(fl, lit.Pos(), kind, "captured by the function literal at "+v.placeOf(lit.Pos())+", which may run after the call")
		v.ownKeep(fl, kind)
		v.ownEscape(kind, f, "captured by the function literal at "+v.placeOf(lit.Pos()))
		return true
	})
}

// ownRunLiteral judges a literal's body where it runs, as a literal called
// in place, deferred, or handed to a trusted function that only runs it
// (F9 (c)): its statements are applied to the fact, each assignment adding
// to what a variable may hold, until nothing changes.
func (v *fnVerifier) ownRunLiteral(fl *ownFlow, lit *ast.FuncLit, f *ownFact) (returned ownKind) {
	for range 8 {
		before := f.clone()
		ast.Inspect(lit.Body, func(n ast.Node) bool {
			switch n := n.(type) {
			case *ast.FuncLit:
				return false
			case *ast.AssignStmt, *ast.DeclStmt, *ast.ExprStmt, *ast.DeferStmt, *ast.SendStmt:
				saved := f.clone()
				v.ownTransfer(fl, n.(ast.Node), f)
				// What the literal assigns may also be what it held.
				for variable, kind := range saved.vars {
					f.vars[variable] = f.vars[variable].union(kind)
				}
				return false
			case *ast.ReturnStmt:
				for _, r := range n.Results {
					returned = returned.union(v.ownKindOf(fl, r, f))
				}
				return false
			case *ast.RangeStmt:
				v.ownKindOf(fl, n.X, f)
				for _, e := range []ast.Expr{n.Key, n.Value} {
					if id, ok := e.(*ast.Ident); ok && id.Name != "_" {
						if variable, isVar := v.info.ObjectOf(id).(*types.Var); isVar {
							f.vars[variable] = ownKind{}
						}
					}
				}
			case ast.Expr:
				v.ownKindOf(fl, n, f)
				return false
			}
			return true
		})
		if !before.join(*f) && before.vars != nil {
			unchanged := true
			for variable, kind := range f.vars {
				if !kind.equal(before.vars[variable]) {
					unchanged = false
				}
			}
			if unchanged {
				return returned
			}
		}
	}
	return returned
}

// ownCallee is what the analysis knows of a callee: for each of its
// parameters, the receiver first, whether it may keep what it is handed,
// and for each result what it flows from.
type ownCallee struct {
	fn      *funcInfo
	name    string
	params  []*types.Var
	keeps   func(param *types.Var) bool
	results func(i int) ownResult
	// trusted is set for a trusted function, whose results may hold the
	// argument's memory below the top level only where its entry says
	// (F15), verified for a verified function, which assumes E.
	trusted  bool
	verified bool
	why      string
}

// callResultType returns the type of result i of a call, or nil.
func callResultType(info *types.Info, call *ast.CallExpr, i int) types.Type {
	t := info.TypeOf(call)
	if tuple, ok := t.(*types.Tuple); ok {
		if i < tuple.Len() {
			return tuple.At(i).Type()
		}
		return nil
	}
	if i == 0 {
		return t
	}
	return nil
}

// ownCalleeOf returns what is known of the callee of a call, or nil for a
// built-in, a conversion, or a literal called in place.
func (v *fnVerifier) ownCalleeOf(call *ast.CallExpr) *ownCallee {
	name := types.ExprString(call.Fun)
	method, value := throughValue(v.info, call)
	fn := v.memCallee(call)
	keepAll := func(*types.Var) bool { return true }
	unknown := func(int) ownResult { return ownResult{unknown: true} }
	if callee := typeutil.StaticCallee(v.info, call); errorConstructor(callee) {
		// errors.New and fmt.Errorf keep nothing but what %w wraps, which
		// the error they make holds: its kind is that of the operands
		// (F33).
		sig := callee.Type().(*types.Signature)
		var params []*types.Var
		for param := range sig.Params().Variables() {
			params = append(params, param)
		}
		return &ownCallee{name: name, params: params, keeps: func(*types.Var) bool { return false },
			results: func(int) ownResult {
				from := map[*types.Var]bool{}
				for _, p := range params {
					from[p] = true
				}
				return ownResult{fresh: true, from: from}
			}}
	}
	switch {
	case v.pkgVerifier.isEncoderInner(call):
		// The encoder lives for the one expression; see json.go.
		return &ownCallee{name: name, keeps: func(*types.Var) bool { return false }, results: unknown}
	case value:
		return &ownCallee{fn: fn, name: name, keeps: keepAll, results: unknown, why: "a function value may keep what it is handed"}
	case fn == nil:
		return &ownCallee{name: name, keeps: keepAll, results: unknown, why: "it has no contract"}
	case method != nil && fn.trust == nil:
		return &ownCallee{fn: fn, name: name, keeps: keepAll, results: unknown,
			why: "a method of an interface declared in source may keep what it is handed"}
	case fn.trust != nil:
		// A trusted entry keeps only what its keeps lists, as the shipped
		// interface methods document of their arguments.
		kept := map[string]bool{}
		for _, k := range fn.trust.keeps {
			kept[k.name] = true
		}
		c := &ownCallee{fn: fn, name: name, params: fn.params, trusted: true,
			keeps: func(param *types.Var) bool { return param != nil && kept[param.Name()] }}
		c.results = func(i int) ownResult {
			if arg := v.withinParam(fn, i); arg != nil {
				return ownResult{from: map[*types.Var]bool{arg: true}}
			}
			if promisesFresh(fn, i) && !v.targetsHoldReferences(fn) {
				return ownResult{fresh: true}
			}
			// A result the entry does not place may be any argument's
			// memory (F14).
			from := map[*types.Var]bool{}
			for _, p := range fn.params {
				from[p] = true
			}
			return ownResult{from: from}
		}
		if method != nil {
			c.why = "its entry lists it under keeps"
		}
		return c
	}
	summary := v.pkgVerifier.ownSummaryOf(fn)
	if summary == nil {
		return &ownCallee{fn: fn, name: name, keeps: keepAll, results: unknown, why: "nothing says what it keeps"}
	}
	return &ownCallee{fn: fn, name: name, params: fn.params, verified: true,
		keeps: func(param *types.Var) bool {
			// An operand with no parameter, as of g(f()), which bindArgs
			// cannot bind, counts as kept.
			i := slices.Index(fn.params, param)
			return i < 0 || summary.keeps[i]
		},
		results: func(i int) ownResult {
			if i >= len(summary.results) {
				return ownResult{unknown: true}
			}
			r := summary.results[i]
			out := ownResult{fresh: r.fresh, unknown: r.unknown, from: map[*types.Var]bool{}, inside: map[*types.Var]bool{}}
			for _, at := range r.from {
				if at < len(fn.params) {
					out.from[fn.params[at]] = true
				}
			}
			for _, at := range r.inside {
				if at < len(fn.params) {
					out.inside[fn.params[at]] = true
				}
			}
			return out
		},
		why: "it may keep what it is handed"}
}

// withinParam returns the parameter that a conjunct within(result, p) of a
// contract places a result in, or nil.
func (v *fnVerifier) withinParam(fn *funcInfo, index int) *types.Var {
	if sig, ok := fn.obj.Type().(*types.Signature); !ok || index >= sig.Results().Len() {
		return nil
	}
	name := spelledResult(fn, index)
	for _, c := range fn.ensures {
		if c.node == nil {
			continue
		}
		for _, conjunct := range c.node.Conjuncts() {
			if conjunct.Kind == logic.NBinary && conjunct.Op == "Or" {
				a, b := conjunct.Kids[0], conjunct.Kids[1]
				if b.Kind == logic.NCall && b.Name == "fresh" {
					a, b = b, a
				}
				if a.Kind == logic.NCall && a.Name == "fresh" && len(a.Kids) == 1 && a.Kids[0].Kind == logic.NIdent && a.Kids[0].Name == name {
					conjunct = b
				}
			}
			if conjunct.Kind == logic.NCall && conjunct.Name == "within" && len(conjunct.Kids) == 2 &&
				conjunct.Kids[0].Kind == logic.NIdent && conjunct.Kids[0].Name == name && conjunct.Kids[1].Kind == logic.NIdent {
				if param := fn.paramNames[conjunct.Kids[1].Name]; param != nil {
					return param
				}
			}
		}
	}
	return nil
}

// ownOperands pairs the operands of a call with the callee's parameters,
// the receiver first. An operand that is not paired is handed to nil. addr
// is set for a receiver whose address Go takes, for a pointer method on an
// addressable operand (F35 of the review of step 3b).
func (v *fnVerifier) ownOperands(call *ast.CallExpr, c *ownCallee) []struct {
	param *types.Var
	expr  ast.Expr
	addr  bool
} {
	var out []struct {
		param *types.Var
		expr  ast.Expr
		addr  bool
	}
	add := func(param *types.Var, e ast.Expr) {
		out = append(out, struct {
			param *types.Var
			expr  ast.Expr
			addr  bool
		}{param, e, false})
	}
	method, value := throughValue(v.info, call)
	sig, _ := v.info.TypeOf(call.Fun).(*types.Signature)
	if sel, ok := ast.Unparen(call.Fun).(*ast.SelectorExpr); ok && !value {
		if selection := v.info.Selections[sel]; selection != nil && selection.Kind() == types.MethodVal && method == nil {
			var recv *types.Var
			if c.fn != nil && len(c.fn.params) > 0 {
				recv = c.fn.params[0]
			}
			add(recv, sel.X)
			out[len(out)-1].addr = v.addressTaken(selection, sel.X)
		}
	}
	if sig == nil {
		for _, arg := range call.Args {
			add(nil, arg)
		}
		return out
	}
	bound, ok := bindArgs(v.info, call, paramsOf(sig), sig.Variadic())
	if !ok {
		for _, arg := range call.Args {
			add(nil, arg)
		}
		return out
	}
	byName := func(p *types.Var) *types.Var {
		if c.fn == nil {
			// errors.New and fmt.Errorf, whose parameters are their own.
			if slices.Contains(c.params, p) {
				return p
			}
			return nil
		}
		for _, q := range c.fn.params {
			if q.Name() == p.Name() && q.Pos() == p.Pos() || q == p {
				return q
			}
		}
		if c.fn.paramNames != nil {
			return c.fn.paramNames[p.Name()]
		}
		return nil
	}
	for _, b := range bound {
		param := byName(b.param)
		if b.packed {
			for _, e := range b.pack {
				add(param, e)
			}
			continue
		}
		add(param, b.expr)
	}
	return out
}

// ownResults returns the kinds of the results of a call, or of an
// expression of several values, applying what the call does with what it
// is handed.
func (v *fnVerifier) ownResults(fl *ownFlow, e ast.Expr, count int, f *ownFact) []ownKind {
	out := make([]ownKind, count)
	if assert, ok := ast.Unparen(e).(*ast.TypeAssertExpr); ok {
		// v, ok := x.(T): the value is what x is (F7 of the design
		// review).
		out[0] = v.ownKindOf(fl, assert.X, f)
		return out
	}
	if call, ok := ast.Unparen(e).(*ast.CallExpr); ok && isAsCall(typeutil.StaticCallee(v.info, call)) {
		// What errors.As and errors.AsType find in an error is part of it,
		// as what an assertion takes out is (F7 of the design review).
		kind := v.ownKindOf(fl, call.Args[0], f)
		if len(call.Args) < 2 {
			out[0] = kind
			return out
		}
		if addr, isAddr := ast.Unparen(call.Args[1]).(*ast.UnaryExpr); isAddr {
			if id, isIdent := ast.Unparen(addr.X).(*ast.Ident); isIdent {
				if variable, isVar := v.info.ObjectOf(id).(*types.Var); isVar {
					if v.boxed[variable] {
						v.ownStoreMemory(fl, call.Args[0], kind, f, "stored by errors.As into "+id.Name+", which lives in memory")
					} else {
						f.vars[variable] = f.vars[variable].union(kind)
					}
				}
			}
		}
		return out
	}
	call, ok := ast.Unparen(e).(*ast.CallExpr)
	if !ok {
		// A map read or a receive with its second result.
		out[0] = v.ownKindOf(fl, e, f)
		return out
	}
	if tv, ok := v.info.Types[call.Fun]; ok && tv.IsType() {
		if len(call.Args) == 1 {
			kind := v.ownKindOf(fl, call.Args[0], f)
			if isSlice(tv.Type) && isString(v.info.TypeOf(call.Args[0])) {
				kind = v.ownSite(call, f)
			}
			out[0] = kind
		}
		return out
	}
	if id, ok := ast.Unparen(call.Fun).(*ast.Ident); ok {
		if builtin, isBuiltin := v.info.Uses[id].(*types.Builtin); isBuiltin {
			kinds := make([]ownKind, len(call.Args))
			for i, arg := range call.Args {
				kinds[i] = v.ownKindOf(fl, arg, f)
			}
			switch builtin.Name() {
			case "make", "new":
				out[0] = v.ownSite(call, f)
			case "append":
				// In place it is the slice's own memory, moved it is new;
				// what is appended is stored into the array.
				for i, arg := range call.Args[1:] {
					v.ownStoreMemory(fl, arg, kinds[i+1], f, "appended to "+types.ExprString(call.Args[0]))
				}
				out[0] = kinds[0].union(v.ownSite(call, f))
			case "copy":
				// The elements are copied; a copied element that refers to
				// memory is stored.
				if len(call.Args) == 2 && isSlice(v.info.TypeOf(call.Args[1])) && refersMemory(elemType(v.info.TypeOf(call.Args[1]))) {
					v.ownStoreMemory(fl, call.Args[1], ownKind{unknown: kinds[1].unknown, scoped: kinds[1].scoped, decl: kinds[1].decl}, f, "copied")
				}
			}
			return out
		}
	}
	if lit := v.literalOf(call); lit != nil {
		for _, arg := range call.Args {
			v.ownKindOf(fl, arg, f)
		}
		returned := v.ownRunLiteral(fl, lit, f)
		for i := range out {
			// What the literal returns may be a scoped value it reaches.
			out[i] = ownKind{unknown: "it comes from a function literal", scoped: returned.scoped, decl: returned.decl}
		}
		return out
	}
	c := v.ownCalleeOf(call)
	operands := v.ownOperands(call, c)
	kinds := make([]ownKind, len(operands))
	for i, op := range operands {
		if lit, isLit := ast.Unparen(op.expr).(*ast.FuncLit); isLit && c.trusted {
			// A literal handed to a trusted function runs while it runs.
			v.ownRunLiteral(fl, lit, f)
			continue
		}
		if op.addr {
			kinds[i] = v.ownResolve(v.ownAddress(fl, op.expr, f), f)
			continue
		}
		kinds[i] = v.ownResolve(v.ownKindOf(fl, op.expr, f), f)
	}
	if fl.emitting {
		recorded := make([]ownOperand, len(operands))
		for i, op := range operands {
			k := kinds[i]
			fresh := len(k.tags) > 0 && len(k.params) == 0 && len(k.inside) == 0 && k.unknown == ""
			escaped := ""
			for tag := range k.tags {
				if st := f.status[tag]; st.state != tagNew {
					fresh = false
					if st.state == tagEscaped {
						escaped = st.why
					}
				}
			}
			recorded[i] = ownOperand{expr: op.expr, kind: k, addr: op.addr, fresh: fresh, escaped: escaped}
		}
		fl.operands[call] = recorded
	}
	for i, op := range operands {
		kind := kinds[i]
		if c.keeps(op.param) {
			for root := range kind.inside {
				fl.refuse(op.expr.Pos(), rOwnsKept, "what is handed to %s as %s is memory that %s owns, and %s; copy it, or do not declare the field owned",
					c.name, v.paramName(op.param), v.rootName(root), c.why)
				break
			}
			why := c.why
			if c.trusted && op.param != nil {
				for _, k := range c.fn.trust.keeps {
					if k.name == op.param.Name() {
						var dests []string
						for _, d := range k.dests {
							dests = append(dests, d.text)
						}
						why = "its entry keeps " + k.name + " in " + strings.Join(dests, " and ")
					}
				}
			}
			v.refuseScoped(fl, op.expr.Pos(), kind, "handed to "+c.name+" as "+v.paramName(op.param)+" ("+why+")", types.ExprString(op.expr))
			v.ownKeep(fl, kind)
			v.ownEscape(kind, f, "handed to "+c.name+", which may keep it")
			continue
		}
		// A trusted function's results may hold the argument's memory below
		// their top level only where its entry says (F15).
		if c.trusted && len(kind.inside) > 0 {
			for r := range len(c.fn.results) {
				if v.ownDeeper(c.fn.results[r].Type(), v.info.TypeOf(op.expr)) {
					fl.refuse(op.expr.Pos(), rOwnsKept, "what is handed to %s as %s is memory that %s owns, and what %s returns may hold parts of it that "+
						"its entry does not place; copy the memory first, as with bytes.Clone or slices.Clone", c.name, v.paramName(op.param),
						v.rootName(v.rootOf(kind)), c.name)
					break
				}
			}
		}
	}
	// One tag for the call, shared by every new result (F20).
	var tag ownKind
	for i := range out {
		r := c.results(i)
		var kind ownKind
		if r.unknown {
			kind.unknown = "it comes from the call of " + c.name + " at " + v.placeOf(call.Pos())
		}
		if r.fresh {
			if !tag.holds() {
				tag = v.ownSite(call, f)
			}
			kind = kind.union(tag)
		}
		for j, op := range operands {
			if op.param != nil && r.from[op.param] {
				from := kinds[j]
				// An error result of a call handed what an owner owns,
				// other than as an error, holds it only through the call,
				// when nothing says how the result relates to it: a
				// trusted function, an interface method, or a function
				// value. A verified callee's summary says that its result
				// flows from the argument, which its own code may have put
				// into the error, so that kind keeps no mark.
				if t := v.info.TypeOf(op.expr); !c.verified && isError(callResultType(v.info, call, i)) && t != nil && !isError(t) && v.concreteErrorType(op.expr, -1) == nil && len(from.inside) > 0 {
					from.throughCall = maps.Clone(from.inside)
				}
				kind = kind.union(from)
			}
			if op.param != nil && r.inside[op.param] {
				kind = kind.union(ownKind{inside: map[ownRoot]bool{v.rootOf(kinds[j]): true}})
			}
		}
		out[i] = kind
	}
	return out
}

// ownDeeper reports whether a value of type result can hold, below its
// top level, a reference into memory of type arg: an element, a field, or
// what a pointer points to that is of a type that refers to such memory,
// or an interface value: a value that can lie inside what arg refers to
// (mayLieIn), as a *Point does inside a []Item that holds Points (A10). A
// nested occurrence is tested before the walk passes over a type it has
// seen, so that a type that holds itself, as type List []List does, is
// found below its top (A11).
func (v *fnVerifier) ownDeeper(result, arg types.Type) bool {
	seen := map[types.Type]bool{}
	var walk func(t types.Type, top bool) bool
	walk = func(t types.Type, top bool) bool {
		if !top && (mayLieIn(arg, t) || isIface(t)) {
			return true
		}
		if seen[t] {
			return false
		}
		seen[t] = true
		if object, isPointer := pointee(t); isPointer {
			return walk(object, false)
		}
		switch u := t.Underlying().(type) {
		case *types.Slice:
			return walk(u.Elem(), false)
		case *types.Map:
			return walk(u.Key(), false) || walk(u.Elem(), false)
		case *types.Struct:
			for field := range u.Fields() {
				if walk(field.Type(), false) {
					return true
				}
			}
		}
		return false
	}
	return walk(result, true)
}

// paramName names a parameter in a message.
func (v *fnVerifier) paramName(p *types.Var) string {
	if p == nil {
		return "an argument"
	}
	return p.Name()
}

// ownReturn applies a return statement: what each result is, for the
// summary, and R5.
func (v *fnVerifier) ownReturn(fl *ownFlow, ret *ast.ReturnStmt, f *ownFact) {
	if v.fn == nil {
		return
	}
	var kinds []ownKind
	switch {
	case len(ret.Results) == 0:
		for _, result := range v.fn.results {
			kinds = append(kinds, f.vars[result])
		}
	case len(ret.Results) == 1 && len(v.fn.results) > 1:
		kinds = v.ownResults(fl, ret.Results[0], len(v.fn.results), f)
	default:
		for _, r := range ret.Results {
			kinds = append(kinds, v.ownKindOf(fl, r, f))
		}
	}
	// The results as the deferred calls leave them, which may assign
	// them (F30 of the review of step 3a).
	if len(fl.deferred) > 0 {
		for i, result := range v.fn.results {
			if i < len(kinds) && result.Name() != "" && result.Name() != "_" {
				f.vars[result] = kinds[i]
			}
		}
		for _, lit := range fl.deferred {
			v.ownRunLiteral(fl, lit, f)
		}
		for i, result := range v.fn.results {
			if i < len(kinds) && result.Name() != "" && result.Name() != "_" {
				kinds[i] = f.vars[result]
			}
		}
	}
	if fl.results == nil {
		fl.results = make([]ownResult, len(v.fn.results))
		for i := range fl.results {
			fl.results[i] = ownResult{fresh: true, from: map[*types.Var]bool{}, inside: map[*types.Var]bool{}}
		}
	}
	for i, kind := range kinds {
		if i >= len(fl.results) {
			break
		}
		kind = v.ownResolve(kind, f)
		r := &fl.results[i]
		pos := ret.Pos()
		if i < len(ret.Results) {
			pos = ret.Results[i].Pos()
		}
		resultText := ""
		if i < len(ret.Results) {
			resultText = types.ExprString(ret.Results[i])
		}
		v.refuseScoped(fl, pos, kind, "returned by "+v.fn.obj.Name(), resultText)
		if kind.unknown != "" {
			r.unknown = true
		}
		for p := range kind.params {
			r.from[p] = true
		}
		fresh := len(kind.tags) > 0 || len(kind.inside) > 0
		for tag := range kind.tags {
			if f.status[tag].state != tagNew {
				// New memory that something else refers to: to the caller
				// it is of no origin it can place.
				fresh = false
				r.unknown = true
			}
		}
		for root := range kind.inside {
			switch {
			case root.param != nil:
				fresh = false
				r.inside[root.param] = true
				// An error that holds a part of an owner is returned with
				// the summary saying so (r.inside): a verified caller that
				// asserts what it holds gets a part of the owner, which it
				// may not keep (F7 of the design review of F33), and only
				// an assertion reaches it. No contract can place an error.
				if isError(v.fn.results[i].Type()) && kind.throughCall[root] {
					continue
				}
				if v.withinParam(v.fn, i) != root.param {
					// within places a pointer, a slice, a map, or an
					// interface value; a struct value that holds the part
					// can only be a copy (F33 of the review of step 3a).
					rt := v.fn.results[i].Type()
					if _, isPointer := pointee(rt); isPointer || isSlice(rt) || isMap(rt) || isIface(rt) {
						fl.refuse(pos, rOwnsReturned, "%s returns memory that %s owns; say so with within(%s, %s) in an Ensures, or return a copy",
							v.fn.obj.Name(), root.param.Name(), spelledResult(v.fn, i), root.param.Name())
					} else {
						held := types.TypeString(rt, types.RelativeTo(v.pass.Pkg))
						fl.refuse(pos, rOwnsReturned, "%s returns memory that %s owns, held in %s %s, which no contract can place within %s; return a copy",
							v.fn.obj.Name(), root.param.Name(), article(held), held, root.param.Name())
					}
				}
			case root.tag.site != nil:
				// What a local owner owns may be returned while nothing
				// else refers to it (F9 (b), F12): the owner's own tag is
				// still new, and no other result holds it or what it owns.
				other := false
				for j, k := range kinds {
					k = v.ownResolve(k, f)
					if j != i && (k.tags[root.tag] || k.inside[root]) {
						other = true
					}
				}
				if s := f.status[root.tag]; s.state != tagNew || other || len(fl.deferred) > 0 {
					fl.refuse(pos, rOwnsReturned, "%s returns memory that %s owns, which something else may refer to; return a copy, or return the owner",
						v.fn.obj.Name(), v.rootName(root))
					fresh = false
				}
			default:
				fresh = false
				fl.refuse(pos, rOwnsReturned, "%s returns memory that an owner owns; return a copy", v.fn.obj.Name())
			}
		}
		if len(kind.params) > 0 || kind.unknown != "" {
			fresh = false
		}
		if !fresh {
			r.fresh = false
		}
	}
}

// ownSummary is what a verified function's body says of what it keeps and
// of what its results are, for its callers: for each parameter, the
// receiver first, whether it may keep it, and for each result whether it is
// new and not escaped, the parameters whose memory it may be, and those
// whose owned memory it may be. A body that uses Go the verifier refuses
// has none.
type ownSummary struct {
	keeps   []bool
	results []ownResultFact
}

// ownResultFact is ownResult with parameters by index, as it travels.
type ownResultFact struct {
	fresh   bool
	from    []int
	inside  []int
	unknown bool
}

// ownSummaryOf returns the summary of a verified function, of this package
// or of another, or nil. Those of the package are the greatest fixed point
// from "keeps nothing, returns new memory", as part 1's summaries are: a
// verified function ends, so what holds of every call it makes holds by
// induction on the depth of calls.
func (pv *pkgVerifier) ownSummaryOf(fn *funcInfo) *ownSummary {
	if fn == nil || fn.trust != nil || fn.valueOf != nil || fn.methodOf != nil {
		return nil
	}
	origin := pv.originOf(fn.obj)
	if pv.ownSummaries == nil {
		pv.ownSummaries = map[*types.Func]*ownSummary{}
		var local []*funcInfo
		for _, f := range pv.order {
			if f.annotated() && f.decl != nil && f.decl.Body != nil && f.trust == nil && !isGeneric(f.obj) {
				local = append(local, f)
				s := &ownSummary{keeps: make([]bool, len(f.params))}
				for range f.results {
					s.results = append(s.results, ownResultFact{fresh: true})
				}
				pv.ownSummaries[f.obj] = s
			}
		}
		// The summaries of a package that calls itself in a cycle can go
		// round without settling, since what a result is made of does not
		// only grow as its callees' do. After as many rounds as settle any
		// package that settles, each summary is joined with the one before
		// it, toward what a caller must assume more of, which ends: the
		// lattice is finite and a join only goes down it. A join keeps
		// more parameters and results that are not fresh, unknown, or from
		// or inside more parameters, which no caller can be harmed by.
		widen := 4*len(local) + 16
		for changed, round := true, 0; changed; round++ {
			changed = false
			for _, f := range local {
				summarize := pv.ownSummarize
				if testSummarize != nil {
					summarize = testSummarize
				}
				next, was := summarize(f), pv.ownSummaries[f.obj]
				if round >= widen {
					next = joinSummaries(was, next)
				}
				same := next != nil && was != nil && slices.Equal(next.keeps, was.keeps) &&
					slices.EqualFunc(next.results, was.results, func(a, b ownResultFact) bool {
						return a.fresh == b.fresh && a.unknown == b.unknown && slices.Equal(a.from, b.from) && slices.Equal(a.inside, b.inside)
					})
				if !same && (next != nil || was != nil) {
					pv.ownSummaries[f.obj] = next
					changed = true
				}
			}
		}
	}
	if s, known := pv.ownSummaries[origin]; known {
		return s
	}
	if fn.imported != nil && fn.imported.Verified && fn.imported.OwnKeeps != nil {
		s := &ownSummary{keeps: slices.Clone(fn.imported.OwnKeeps)}
		for _, r := range fn.imported.OwnResults {
			s.results = append(s.results, ownResultFact{fresh: r.Fresh, from: r.From, inside: r.Inside, unknown: r.Unknown})
		}
		return s
	}
	return nil
}

// ownSummarize decides the summary of one function from its body, with
// what is known now of its callees.
func (pv *pkgVerifier) ownSummarize(fn *funcInfo) (summary *ownSummary) {
	summary = &ownSummary{keeps: make([]bool, len(fn.params))}
	for range fn.results {
		summary.results = append(summary.results, ownResultFact{fresh: true})
	}
	defer func() {
		if r := recover(); r != nil {
			switch r.(type) {
			case unsupported, abort:
				summary = nil
			default:
				panic(r)
			}
		}
	}()
	sv := pv.newVerifier(fn)
	sv.boxed = sv.findBoxed(fn.decl.Body)
	sv.classifyLiterals()
	sv.ownForce = true
	fl := sv.ownOrigins()
	if fl == nil {
		// A body that is not there has no summary; a summary runs the
		// analysis on every body (ownForce).
		return nil
	}
	for i, p := range fn.params {
		summary.keeps[i] = fl.keeps[p]
	}
	for i := range summary.results {
		if i >= len(fl.results) {
			continue
		}
		r := fl.results[i]
		out := ownResultFact{fresh: r.fresh, unknown: r.unknown}
		for j, p := range fn.params {
			if r.from[p] {
				out.from = append(out.from, j)
			}
			if r.inside[p] {
				out.inside = append(out.inside, j)
			}
		}
		summary.results[i] = out
	}
	return summary
}

// testSummarize, set by a test, replaces ownSummarize in the iteration of
// ownSummaryOf, so that an iteration that does not settle can be made.
var testSummarize func(*funcInfo) *ownSummary

// joinSummaries returns the summary that says of a function what both say
// it may do: it keeps what either keeps, and a result is fresh only if both
// say so, unknown if either does, and from or inside what either names. A
// nil summary, of a body that refused, says nothing and is kept.
func joinSummaries(a, b *ownSummary) *ownSummary {
	if a == nil || b == nil {
		return nil
	}
	out := &ownSummary{keeps: slices.Clone(a.keeps)}
	for i := range out.keeps {
		out.keeps[i] = out.keeps[i] || i < len(b.keeps) && b.keeps[i]
	}
	for i, r := range a.results {
		if i >= len(b.results) {
			out.results = append(out.results, r)
			continue
		}
		s := b.results[i]
		from := slices.Compact(slices.Sorted(slices.Values(slices.Concat(r.from, s.from))))
		inside := slices.Compact(slices.Sorted(slices.Values(slices.Concat(r.inside, s.inside))))
		out.results = append(out.results, ownResultFact{fresh: r.fresh && s.fresh, unknown: r.unknown || s.unknown, from: from, inside: inside})
	}
	return out
}

// reportOwnOrigins reports what the analysis refuses in the function being
// verified.
func (v *fnVerifier) reportOwnOrigins() {
	fl := v.ownOrigins()
	if fl == nil {
		return
	}
	for _, r := range fl.refusals {
		v.report(r.pos, r.class, "%s", strings.TrimSpace(r.msg))
	}
}

// ownWhyKind says why a value of a kind is not memory that only an owner
// will refer to, for the message of a store, or "".
func (v *fnVerifier) ownWhyKind(kind ownKind, f *ownFact) string {
	for root := range kind.inside {
		return ": it is memory that " + v.rootName(root) + " owns"
	}
	for tag := range kind.tags {
		if s := f.status[tag]; s.state == tagEscaped {
			return ": it was " + s.why
		}
	}
	for p := range kind.params {
		return ": it is memory of the parameter " + p.Name()
	}
	if kind.unknown != "" {
		return ": " + kind.unknown
	}
	return ""
}

// ownAddress returns the kind of the address of an operand: an address in
// the memory the operand lies in. An element's address is in its slice's
// array, a field's in the struct the selection reads it from, and what a
// pointer points to is the pointer's memory; the address of a variable
// that lives in memory is of no origin the analysis follows.
func (v *fnVerifier) ownAddress(fl *ownFlow, e ast.Expr, f *ownFact) ownKind {
	switch x := ast.Unparen(e).(type) {
	case *ast.IndexExpr:
		v.ownKindOf(fl, x.Index, f)
		if t := v.info.TypeOf(x.X); isSlice(t) {
			return v.ownKindOf(fl, x.X, f)
		}
		return v.ownAddress(fl, x.X, f)
	case *ast.SelectorExpr:
		if selection := v.info.Selections[x]; selection != nil && selection.Kind() == types.FieldVal {
			if _, viaPointer := pointee(v.info.TypeOf(x.X)); viaPointer {
				return v.ownKindOf(fl, x.X, f)
			}
			return v.ownAddress(fl, x.X, f)
		}
	case *ast.StarExpr:
		return v.ownKindOf(fl, x.X, f)
	case *ast.CompositeLit:
		v.ownLiteral(fl, x, f, true)
		return v.ownSite(x, f)
	case *ast.Ident:
		// A variable that lives in memory is never a part: R1 refuses
		// its address in an owned field, which is no allocation where it
		// stands and no tag.
		if variable, ok := v.info.ObjectOf(x).(*types.Var); ok && v.boxed[variable] {
			return ownKind{}
		}
	}
	return ownKind{unknown: fmt.Sprintf("it is the address of %s", types.ExprString(e))}
}

// ownOperand is an operand of a call with its kind.
type ownOperand struct {
	expr ast.Expr
	kind ownKind
	// addr is set when Go hands the operand's address.
	addr bool
	// fresh is set when the operand is made of tags that are all new where
	// the call stands, and escaped says how a tag of it escaped.
	fresh   bool
	escaped string
}

// addressTaken reports whether Go takes the address of the operand of a
// method selection: a method with a pointer receiver selected on an
// operand that is not a pointer, as l.items[0].M() hands M &l.items[0].
func (v *fnVerifier) addressTaken(selection *types.Selection, operand ast.Expr) bool {
	method, ok := selection.Obj().(*types.Func)
	if !ok {
		return false
	}
	sig, _ := method.Type().(*types.Signature)
	if sig == nil || sig.Recv() == nil {
		return false
	}
	_, pointerRecv := sig.Recv().Type().(*types.Pointer)
	_, operandPointer := pointee(v.info.TypeOf(operand))
	return pointerRecv && !operandPointer
}
