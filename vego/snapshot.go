package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"maps"
	"slices"
	"strings"

	"github.com/spachava753/laas/vego/internal/logic"
)

// A Snapshot annotation, "// @Snapshot r0 = r", names the value a formula
// has where the annotation stands. From there to the end of the innermost
// block or case clause that holds it, the name in an annotation of the body
// is that value: an integer or a boolean, which nothing can change. It is
// how an annotation speaks of an earlier value, such as where an iteration
// began, without a variable that the code must keep alive.
//
// A name has one meaning: it may not name anything visible where the
// snapshot stands, be declared again in its scope, by Go or by another
// snapshot, or be bound by a quantifier there. It must be used, and only by
// annotations of the function itself, not of a function literal in it.

// snapshotScope returns where the scope of a snapshot ends: at the end of
// the innermost block, or the end of the case clause, that holds it.
func (pv *pkgVerifier) snapshotScope(fn *funcInfo, c *clause) token.Pos {
	if end, ok := pv.snapshotEnds[c]; ok {
		return end
	}
	if pv.snapshotEnds == nil {
		pv.snapshotEnds = map[*clause]token.Pos{}
	}
	end := pv.findSnapshotScope(fn, c)
	pv.snapshotEnds[c] = end
	return end
}

func (pv *pkgVerifier) findSnapshotScope(fn *funcInfo, c *clause) token.Pos {
	end := fn.decl.Body.End()
	if clause := pv.caseTails[c.pos]; clause != nil {
		return pv.caseEnd(fn, clause)
	}
	ast.Inspect(fn.decl.Body, func(n ast.Node) bool {
		if n == nil || c.pos < n.Pos() || c.pos >= n.End() {
			return false
		}
		switch n := n.(type) {
		case *ast.BlockStmt:
			end = n.End()
		case *ast.CaseClause:
			end = pv.caseEnd(fn, n)
		}
		return true
	})
	return end
}

// caseEnd returns where the annotations of a case clause end: at the next
// clause, or at the closing brace of the switch.
func (pv *pkgVerifier) caseEnd(fn *funcInfo, clause *ast.CaseClause) token.Pos {
	end := clause.End()
	ast.Inspect(fn.decl.Body, func(n ast.Node) bool {
		if body, ok := n.(*ast.BlockStmt); ok {
			for i, stmt := range body.List {
				if stmt == clause {
					end = clauseEnd(body, i)
				}
			}
		}
		return n != nil
	})
	return end
}

// checkSnapshots reports a snapshot whose name could mean something else,
// that nothing uses, or that an annotation names where it has no value.
func (pv *pkgVerifier) checkSnapshots(fn *funcInfo) {
	for _, c := range fn.body {
		if c.kind != "Snapshot" || c.node == nil {
			continue
		}
		name, end := c.snapshot, pv.snapshotScope(fn, c)
		within := func(pos token.Pos) bool { return c.pos < pos && pos < end }
		fail := func(format string, args ...any) {
			pv.report(c.pos, rAnnotationFault, "Snapshot %s: "+format, append([]any{name}, args...)...)
			fn.broken = true
		}
		if _, limit := pv.namedLimit(name); limit || slices.Contains(reservedStateNames, name) || name == "Z" {
			fail("%s is a word of the annotation language; choose another name", name)
			continue
		}
		if _, obj := pv.scopeAt(c.pos).LookupParent(name, c.pos); obj != nil {
			fail("%s already names %s here; choose a name that names nothing, so that a formula reads it one way", name, describeObject(obj))
			continue
		}
		var again token.Pos
		ast.Inspect(fn.decl.Body, func(n ast.Node) bool {
			if id, ok := n.(*ast.Ident); ok && id.Name == name && pv.info.Defs[id] != nil && within(id.Pos()) && again == token.NoPos {
				again = id.Pos()
			}
			return n != nil
		})
		for _, other := range fn.body {
			if other != c && other.kind == "Snapshot" && other.snapshot == name && within(other.pos) && again == token.NoPos {
				again = other.pos
			}
		}
		if again != token.NoPos {
			fail("%s is declared again at %s, inside the scope of the snapshot; choose another name", name, pv.pass.Fset.Position(again))
			continue
		}
		used := false
		for _, other := range fn.body {
			if other == c || other.node == nil || !within(other.pos) {
				continue
			}
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
			case bound:
				pv.report(other.pos, rAnnotationFault, "%s annotation binds %s, which is the name of the snapshot at %s; name the bound variable otherwise",
					other.kind, name, pv.pass.Fset.Position(c.pos))
				fn.broken = true
			case names && pv.inOtherLiteral(fn, c.pos, other.pos):
				pv.report(other.pos, rAnnotationFault, "%s annotation names the snapshot %s, which was taken outside the function literal it stands in; "+
					"take the snapshot inside the literal", other.kind, name)
				fn.broken = true
			}
			used = used || names
		}
		if !used {
			fail("no annotation after it, in the block that holds it, names %s, so it says nothing; remove it, or move it to where it is used", name)
		}
	}
	pv.checkSnapshotOrder(fn)
}

// checkSnapshotOrder reports a Snapshot that follows an Invariant or a
// Variant in one comment group. The annotations of a loop are read before
// the loop, but a Snapshot is taken where it stands, so one below them
// would be taken before the annotations above it that name it.
func (pv *pkgVerifier) checkSnapshotOrder(fn *funcInfo) {
	var comments []*ast.CommentGroup
	for _, file := range pv.pass.Files {
		if file.FileStart <= fn.decl.Pos() && fn.decl.Pos() < file.FileEnd {
			comments = file.Comments
		}
	}
	for _, group := range comments {
		if group.Pos() < fn.decl.Body.Pos() || group.End() > fn.decl.Body.End() {
			continue
		}
		loopAnnotation := false
		for _, c := range fn.body {
			if c.pos < group.Pos() || c.pos >= group.End() {
				continue
			}
			switch {
			case c.kind == "Invariant" || c.kind == "Variant":
				loopAnnotation = true
			case c.kind == "Snapshot" && loopAnnotation:
				pv.report(c.pos, rAnnotationFault, "Snapshot %s stands below an Invariant or Variant of the loop; put it above the annotations of the loop", c.snapshot)
				fn.broken = true
			}
		}
	}
}

// inOtherLiteral reports whether a position lies in a function literal of
// the body that another position does not.
func (pv *pkgVerifier) inOtherLiteral(fn *funcInfo, taken, used token.Pos) bool {
	other := false
	ast.Inspect(fn.decl.Body, func(n ast.Node) bool {
		if lit, ok := n.(*ast.FuncLit); ok && lit.Pos() <= used && used < lit.End() && !(lit.Pos() <= taken && taken < lit.End()) {
			other = true
		}
		return n != nil && !other
	})
	return other
}

// snapshotAt returns the Snapshot clause of the function that a name in an
// annotation at a position refers to, or nil.
func (v *fnVerifier) snapshotAt(name string, pos token.Pos) *clause {
	if v.fn.decl == nil || v.fn.decl.Body == nil {
		return nil
	}
	for _, c := range v.fn.body {
		if c.kind == "Snapshot" && c.snapshot == name && c.pos < pos && pos < v.pkgVerifier.snapshotScope(v.fn, c) {
			return c
		}
	}
	return nil
}

// takeSnapshot records the value of a Snapshot clause in the state where
// it stands. The value is the term itself, so that what is renamed in the
// state is renamed in it too.
func (v *fnVerifier) takeSnapshot(c *clause, st *state) {
	t, err := v.resolverOf(c).Value(c.node, v.bodyEnv(st, c.pos))
	switch {
	case err != nil:
		v.misread(c, err)
	case t.Sort != logic.Int && t.Sort != logic.Bool:
		_, written, _ := strings.Cut(c.text, "=")
		v.misread(c, fmt.Errorf("a snapshot holds an integer or a boolean, and %s is %s", strings.TrimSpace(written), describeSort(t.Sort)))
	}
	v.noteIs(st, t)
	st.snapshots = maps.Clone(st.snapshots)
	if st.snapshots == nil {
		st.snapshots = map[*clause]*logic.Term{}
	}
	st.snapshots[c] = t
}

// describeObject names what kind of thing a name stands for, for a message.
func describeObject(obj types.Object) string {
	switch obj.(type) {
	case *types.Var:
		return "a variable"
	case *types.Const:
		return "a constant"
	case *types.TypeName:
		return "a type"
	case *types.PkgName:
		return "a package"
	case *types.Func, *types.Builtin:
		return "a function"
	case *types.Nil:
		return "nil"
	}
	return "something"
}

// describeSort names what a term of a sort stands for in a message.
func describeSort(sort logic.Sort) string {
	switch {
	case sort == logic.Ref:
		return "a pointer, a map, a function value, or an interface value"
	case sort == logic.Err:
		return "an error"
	case sort.IsSeq():
		return "a slice or a string"
	}
	return "a " + sort.String()
}
