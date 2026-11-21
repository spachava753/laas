package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"slices"

	"github.com/spachava753/laas/vego/internal/logic"
)

// A range over a map walks the positions of one order of the keys the map
// has when the loop starts. Go fixes no order, so the order is unknown: a
// sequence order from positions to keys and its inverse pos from keys to
// positions, of which only this is known (Bij):
//
//	Forall k : has0[k] -> 0 <= pos[k] < n0 And order[pos[k]] = k
//
// where has0 is which keys the map has at the start and n0 how many. The
// iteration at position i gets the key order[i], of which, while i < n0,
// has0[order[i]] and pos[order[i]] = i are known; keys of different
// iterations differ since pos is a function. This is true of every map Go
// can build: the keys present at the start are finitely many, n0 of them,
// and Go visits each exactly once in some order, which order is.
//
// A Visited annotation, "// @Visited done", names the keys the loop has
// passed before the current iteration: has(done, k) is has0[k] And
// (pos[k] < i Or n0 <= i), and |done| is i. The disjunct n0 <= i is what
// Bij gives when the loop has passed every position, so after a whole run
// done is exactly the keys of the start without the solver instantiating
// Bij.

// mapRange is what the verifier knows of one range over a map.
type mapRange struct {
	mapType types.Type
	ref     *logic.Term
	// has0 is the row of keys of the map at the start, n0 how many it has,
	// and pos and order the order of the walk.
	has0, n0, pos, order *logic.Term
	// at is where the range stands, for messages.
	at token.Pos
}

// visitedSet is the value of a Visited name in a state: the range and the
// position of the current iteration, a constant or a literal.
type visitedSet struct {
	r       *mapRange
	counter *logic.Term
}

// bijection states Bij, the order being a bijection from the keys the map
// has at the start into the positions of the walk.
func (v *fnVerifier) bijection(r *mapRange) *logic.Term {
	k := v.bound("key")
	at := logic.Select(r.pos, k)
	return logic.Forall(k, logic.Implies(logic.Select(r.has0, k),
		logic.And(logic.Le(logic.IntLit(0), at), logic.Lt(at, r.n0), logic.Eq(logic.Select(r.order, at), k))))
}

// startMapRange sets up the walk of a range over the map ref, once the
// range expression has been evaluated. Every fact the loop later assumes
// about the walk is an instance of Bij or of the surjection, which says
// that every position of the walk has a key the map has at the start,
// whose position it is. So whether
// they contradict what is known here is asked once, here: a state that no
// map can be in, such as one with fewer keys than its count says, would
// otherwise make everything after it provable without a word. Like the
// other contradiction checks, it reports only what Z3 shows: Z3 5.4.1
// finds no model of the order for many states that have one, a map with
// one key among them, since a model must make the keys finite, and an open
// answer reports nothing.
func (v *fnVerifier) startMapRange(st *state, t types.Type, ref *logic.Term, at token.Pos, what string) *mapRange {
	n0 := v.named(st, "keys", v.mapLen(st, st.mem, t, ref))
	r := &mapRange{
		mapType: t, ref: ref, n0: n0, at: at,
		has0:  v.row(st, st.mem, mapOwner(t)+hasLeaf.path, hasLeaf.sort, ref),
		pos:   v.fresh("pos", logic.IntSeq),
		order: v.fresh("order", logic.IntSeq),
	}
	probe := st.clone()
	probe.assume(v.bijection(r))
	i := v.bound("position")
	key := logic.Select(r.order, i)
	probe.assume(logic.Forall(i, logic.Implies(logic.And(logic.Le(logic.IntLit(0), i), logic.Lt(i, r.n0)),
		logic.And(logic.Select(r.has0, key), logic.Eq(logic.Select(r.pos, key), i)))))
	if v.quickly(probe, nil, logic.False()) && !v.quickly(st, nil, logic.False()) {
		v.report(at, "what is known here says that %s has a number of keys other than |%s|, which no map can; "+
			"check the clauses that say which keys it has", what, what)
	}
	return r
}

// enterPosition binds the key of the iteration at position counter, and
// returns it with its number in the map and the position as a term
// without operands that repeat. Every fact about the key holds only while
// the position is one the map has a key for: bind also runs at entry and
// after the last iteration, where there is none.
func (v *fnVerifier) enterPosition(st *state, r *mapRange, counter *logic.Term) (key, number, position *logic.Term) {
	position = v.named(st, "position", counter)
	keyType, _ := mapParts(r.mapType)
	number = logic.Select(r.order, position)
	key = number
	inside := logic.Lt(position, r.n0)
	if isString(keyType) {
		key = v.fresh("key", logic.IntSeq)
		st.assume(logic.Implies(inside, logic.Eq(logic.Key(key), number)))
	}
	st.assume(logic.Implies(inside, logic.And(
		logic.Select(r.has0, number),
		logic.Eq(logic.Select(r.pos, number), position),
		v.wellFormed(value{key}, keyType, st.brk))))
	return key, number, position
}

// visitedAt returns the Visited clause of the function that a name in an
// annotation at a position refers to, or nil. Inside a body the
// annotations of a loop are read at the start of its body, so the scope is
// the loop itself.
func (v *fnVerifier) visitedAt(name string, pos token.Pos) *clause {
	if v.fn.decl == nil || v.fn.decl.Body == nil {
		return nil
	}
	for _, c := range v.fn.body {
		if c.kind != "Visited" || c.node == nil || c.node.Name != name {
			continue
		}
		if loop, ok := v.pkgVerifier.statementAfter(v.fn, c).(*ast.RangeStmt); ok && loop.Pos() <= pos && pos < loop.End() {
			return c
		}
	}
	return nil
}

// visitedPath resolves a path that starts at a Visited name: |done| and
// has(done, k) are all a formula can ask of one, and a quantifier can range
// over it.
func (e *specEnv) visitedPath(c *clause, steps []logic.Step, when logic.When) (*logic.Term, error) {
	name := c.node.Name
	set := e.st.visited[c]
	switch {
	case when != logic.Now:
		return nil, fmt.Errorf("%s is the set of keys that the loop has visited, which has one value at each iteration; it cannot be primed or put in old()", name)
	case set == nil:
		panic(fmt.Sprintf("vego: internal error: the visited set %s is read outside its loop", name))
	case len(steps) == 1 && steps[0].Len:
		return set.counter, nil
	case len(steps) == 1 && steps[0].Has:
		return e.v.visitedHas(e.sink, set, steps[0].Index)
	}
	return nil, fmt.Errorf("%s is the set of keys that the loop has visited; a formula reads it only as |%s| and has(%s, k)", name, name, name)
}

// visitedHas states that the loop has passed a key. For a key without a
// bound variable it adds the instance of Bij at the key, and otherwise Bij
// itself, so that what has(done, k) says about the order is known.
func (v *fnVerifier) visitedHas(sink *state, set *visitedSet, key *logic.Term) (*logic.Term, error) {
	r := set.r
	keyType, _ := mapParts(r.mapType)
	if want := map[bool]logic.Sort{true: logic.IntSeq, false: logic.Int}[isString(keyType)]; key.Sort != want {
		return nil, fmt.Errorf("has(...): the key has type %s, which is not what the map the loop ranges over is indexed by", key.Sort)
	}
	number := mapKey(key)
	if sink != nil && !hasBound(number) {
		// The key goes into the formula more than once.
		number = v.named(sink, "visited", number)
	}
	at := logic.Select(r.pos, number)
	if sink != nil {
		// Bij holds a bound variable of its own each time it is built, so
		// it is noted by the walk it is of.
		fact, note := v.bijection(r), "visited order "+r.pos.Name
		if !hasBound(number) {
			fact = logic.Implies(logic.Select(r.has0, number),
				logic.And(logic.Le(logic.IntLit(0), at), logic.Lt(at, r.n0), logic.Eq(logic.Select(r.order, at), number)))
			note = "visited " + fact.String()
		}
		if !sink.noted[note] {
			sink.noted[note] = true
			sink.assume(fact)
		}
	}
	return logic.And(logic.Select(r.has0, number), logic.Or(logic.Lt(at, set.counter), logic.Le(r.n0, set.counter))), nil
}

// statementAfter returns the statement directly below an annotation of a
// body, in the list of statements that holds it, or nil.
func (pv *pkgVerifier) statementAfter(fn *funcInfo, c *clause) ast.Stmt {
	if found, ok := pv.below[c]; ok {
		return found
	}
	var found ast.Stmt
	look := func(from token.Pos, list []ast.Stmt) {
		for i, stmt := range list {
			start := from
			if i > 0 {
				start = list[i-1].End()
			}
			if start <= c.pos && c.pos < stmt.Pos() {
				found = stmt
			}
		}
	}
	ast.Inspect(fn.decl.Body, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.BlockStmt:
			look(n.Lbrace, n.List)
		case *ast.CaseClause:
			look(n.Colon, n.Body)
		case *ast.CommClause:
			look(n.Colon, n.Body)
		}
		return n != nil && found == nil
	})
	if pv.below == nil {
		pv.below = map[*clause]ast.Stmt{}
	}
	pv.below[c] = found
	return found
}

// checkVisited reports a Visited clause that is not directly above a range
// over a map, a second one on a loop, a name that could mean something
// else, one that nothing names, and one named where it has no value.
func (pv *pkgVerifier) checkVisited(fn *funcInfo) {
	onLoop := map[*ast.RangeStmt]*clause{}
	for _, c := range fn.body {
		if c.kind != "Visited" || c.node == nil {
			continue
		}
		name := c.node.Name
		fail := func(format string, args ...any) {
			pv.report(c.pos, "Visited %s: "+format, append([]any{name}, args...)...)
			fn.broken = true
		}
		stmt := pv.statementAfter(fn, c)
		loop, _ := stmt.(*ast.RangeStmt)
		_, isFor := stmt.(*ast.ForStmt)
		switch {
		case stmt == nil:
			fail("a Visited annotation names the keys that a range over a map has visited, and stands directly above one; there is no statement below it")
			continue
		case isFor:
			fail("a Visited annotation names the keys that a range over a map has visited; the loop below it is a for statement, which has no keys to visit")
			continue
		case loop == nil:
			fail("a Visited annotation names the keys that a range over a map has visited, and stands directly above one; the statement below it is no range")
			continue
		case !isMap(pv.info.TypeOf(loop.X)):
			fail("a Visited annotation names the keys that a range over a map has visited; this loop ranges over %s, which has no keys to visit",
				pv.info.TypeOf(loop.X))
			continue
		case onLoop[loop] != nil:
			fail("the loop already has the Visited annotation %s; give it at most one", onLoop[loop].node.Name)
			continue
		}
		onLoop[loop] = c
		if _, limit := pv.namedLimit(name); limit || slices.Contains(reservedStateNames, name) || name == "Z" {
			fail("%s is a word of the annotation language; choose another name", name)
			continue
		}
		if _, obj := pv.scopeAt(c.pos).LookupParent(name, c.pos); obj != nil {
			fail("%s already names %s here; choose a name that names nothing, so that a formula reads it one way", name, describeObject(obj))
			continue
		}
		// The loop's own annotations stand between the statement before it
		// and the loop, and are read in the loop.
		gap := c.pos
		for _, other := range fn.body {
			if other.pos < c.pos && pv.statementAfter(fn, other) == loop {
				gap = min(gap, other.pos)
			}
		}
		inside := func(pos token.Pos) bool { return loop.Pos() <= pos && pos < loop.End() }
		var again token.Pos
		ast.Inspect(loop, func(n ast.Node) bool {
			if id, ok := n.(*ast.Ident); ok && id.Name == name && pv.info.Defs[id] != nil && again == token.NoPos {
				again = id.Pos()
			}
			return n != nil
		})
		for _, other := range fn.body {
			declares := (other.kind == "Snapshot" && other.snapshot == name) || (other.kind == "Visited" && other != c && other.node != nil && other.node.Name == name)
			if declares && (inside(other.pos) || (gap <= other.pos && other.pos < loop.Pos())) && again == token.NoPos {
				again = other.pos
			}
		}
		if again != token.NoPos {
			fail("%s is declared again at %s, inside the loop of the Visited annotation; choose another name", name, pv.pass.Fset.Position(again))
			continue
		}
		used := false
		for _, other := range fn.body {
			if other == c || other.node == nil {
				continue
			}
			ofLoop := gap <= other.pos && other.pos < loop.Pos() && (other.kind == "Invariant" || other.kind == "Variant")
			names, bound := false, false
			other.node.Walk(func(n *logic.Node) {
				switch {
				case n.Kind == logic.NIdent && n.Name == name:
					names = true
				case n.Kind == logic.NQuant && slices.Contains(n.Vars, name):
					bound = true
				}
			})
			switch {
			case !inside(other.pos) && !ofLoop:
				if names && gap <= other.pos && other.pos < loop.Pos() {
					pv.report(other.pos, "%s annotation names %s, the keys that the loop below has visited, which have no value above the loop; "+
						"name it in the loop's Invariant or inside the loop", other.kind, name)
					fn.broken = true
				}
				continue
			case bound:
				pv.report(other.pos, "%s annotation binds %s, which is the name of the Visited annotation at %s; name the bound variable otherwise",
					other.kind, name, pv.pass.Fset.Position(c.pos))
				fn.broken = true
			case names && pv.inOtherLiteral(fn, loop.Pos(), other.pos):
				pv.report(other.pos, "%s annotation names %s, the keys that the loop at %s has visited, from inside a function literal; "+
					"a literal can name only what it declares or the function's own variables", other.kind, name, pv.pass.Fset.Position(loop.Pos()))
				fn.broken = true
			}
			used = used || names
		}
		if !used {
			fail("no annotation of the loop names %s, so it says nothing; remove it, or name it in an Invariant", name)
		}
	}
}
