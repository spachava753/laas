package vego

import (
	"go/ast"
	"go/token"
	"go/types"

	"github.com/spachava753/laas/vego/internal/logic"
)

// Appends in a loop to a slice in memory (F42).
//
// A loop that assigns a local slice only as x = append(x, ...) knows at
// its head that x is still in the array it had where the loop was entered,
// with its offset and capacity, or in an array made since (forget). A
// slice in memory, a field reached through a pointer or what a pointer to
// a slice points to, gets the same fact, as an invariant the verifier adds
// itself: assumed at the head of the loop and proved at every back edge.
// Without it the loop forgot the slice's header, and an append into its
// spare capacity could have written anywhere, which no Modifies covers.
//
// The invariant is added only where nothing in the loop but its appends
// can write the place (condition 1 of the review of the note): the place is
// a field of the struct a pointer the loop does not assign points to, at
// any depth through struct fields held by value, or what such a pointer to
// a slice points to; the loop assigns nothing else of the place's type or of a type that holds one by value,
// calls nothing that may write, runs no function literal, and defers
// nothing. Then every write of the place is one of its appends, an append
// in place keeps the array, the offset, and the capacity, and one that
// moves makes a new array, so the invariant holds at every back edge and
// its check never fails; it is checked all the same. A loop that does not
// meet the condition is verified as before, with no message.

// appendedPlace is a slice in memory that a loop only appends to: the
// expression that names it, the pointer variable it is reached from, and
// the fields on the way.
type appendedPlace struct {
	expr ast.Expr
	root *types.Var
	// fields are the indices of the fields from the struct root points to,
	// or nil for *root.
	fields []int
	deref  bool
}

// appendedPlaces returns the slices in memory that the loop at pos with the
// given nodes only appends to, under the condition above. The pointer a
// place is reached from is declared before the loop: a variable of the
// body, or of a range clause, is another one at each iteration.
func (v *fnVerifier) appendedPlaces(eff *effects, pos token.Pos, nodes ...ast.Node) []appendedPlace {
	var places []appendedPlace
	appends := map[ast.Stmt]bool{}
	others := false
	var lhsTypes []types.Type
	visit := func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.FuncLit, *ast.DeferStmt, *ast.GoStmt:
			others = true
			return false
		case *ast.AssignStmt:
			if place, ok := v.appendPlace(n, eff); ok && place.root.Pos() < pos {
				places = append(places, place)
				appends[n] = true
			}
			if !appends[n] {
				for _, lhs := range n.Lhs {
					if t := v.info.TypeOf(lhs); t != nil {
						lhsTypes = append(lhsTypes, t)
					}
				}
			}
		case *ast.CallExpr:
			if !v.writesNothing(n) {
				others = true
			}
		}
		return true
	}
	for _, node := range nodes {
		if node != nil {
			ast.Inspect(node, visit)
		}
	}
	if others {
		return nil
	}
	var kept []appendedPlace
	for _, place := range places {
		t := v.info.TypeOf(place.expr)
		clash := false
		for _, other := range lhsTypes {
			if holdsType(other, t) {
				clash = true
			}
		}
		// Two appends to one place are one place.
		dup := false
		for _, k := range kept {
			if types.ExprString(k.expr) == types.ExprString(place.expr) {
				dup = true
			}
		}
		if !clash && !dup {
			kept = append(kept, place)
		}
	}
	return kept
}

// appendPlace reports whether an assignment is p = append(p, ...) of a slice
// in memory that a pointer the loop does not assign reaches, and returns it.
func (v *fnVerifier) appendPlace(n *ast.AssignStmt, eff *effects) (appendedPlace, bool) {
	if n.Tok != token.ASSIGN || len(n.Lhs) != 1 || len(n.Rhs) != 1 || !v.isAppend(n.Rhs[0]) {
		return appendedPlace{}, false
	}
	call := ast.Unparen(n.Rhs[0]).(*ast.CallExpr)
	lhs := ast.Unparen(n.Lhs[0])
	if types.ExprString(lhs) != types.ExprString(ast.Unparen(call.Args[0])) || !isSlice(v.info.TypeOf(lhs)) {
		return appendedPlace{}, false
	}
	place := appendedPlace{expr: lhs}
	switch e := lhs.(type) {
	case *ast.StarExpr:
		place.root, place.deref = v.localVar(e.X), true
	case *ast.SelectorExpr:
		// A chain of fields held by value from the struct a pointer
		// variable points to.
		var indices []int
		var cur ast.Expr = e
		for {
			sel, ok := ast.Unparen(cur).(*ast.SelectorExpr)
			if !ok {
				break
			}
			selection := v.info.Selections[sel]
			if selection == nil || selection.Kind() != types.FieldVal || len(selection.Index()) != 1 {
				return appendedPlace{}, false
			}
			indices = append([]int{selection.Index()[0]}, indices...)
			cur = sel.X
			if _, isPointer := pointee(v.info.TypeOf(cur)); isPointer {
				break
			}
		}
		root := v.localVar(cur)
		if root == nil {
			return appendedPlace{}, false
		}
		if _, isPointer := pointee(root.Type()); !isPointer {
			return appendedPlace{}, false
		}
		place.root, place.fields = root, indices
	default:
		return appendedPlace{}, false
	}
	if place.root == nil || eff.whole[place.root] || v.boxed[place.root] || place.root.Parent() == v.pass.Pkg.Scope() {
		return appendedPlace{}, false
	}
	if _, isPointer := pointee(place.root.Type()); !isPointer {
		return appendedPlace{}, false
	}
	return place, true
}

// writesNothing reports whether a call may write nothing a loop's places
// lie in: a built-in other than one that writes a map, or a call of a
// function whose contract lists nothing to modify and that runs, keeps,
// and formats nothing.
func (v *fnVerifier) writesNothing(call *ast.CallExpr) bool {
	if id, ok := ast.Unparen(call.Fun).(*ast.Ident); ok {
		if _, builtin := v.info.Uses[id].(*types.Builtin); builtin {
			return id.Name != "delete" && id.Name != "clear"
		}
	}
	if tv, ok := v.info.Types[call.Fun]; ok && tv.IsType() {
		// A conversion.
		return true
	}
	callee := v.pkgVerifier.calleeAt(call)
	if callee == nil {
		return false
	}
	fn := v.contractOf(callee)
	return fn != nil && len(fn.modifies) == 0 && len(fn.runs.m) == 0 && len(fn.keeps.m) == 0 && fn.formatted == nil
}

// readPlace reads the header of an appended place in a state, with no
// obligation: the reads are those the loop makes anyway.
func (v *fnVerifier) readPlace(st *state, place appendedPlace) value {
	var val value
	v.quietly(func() {
		cur := v.current(st, place.root)
		t := place.root.Type()
		if place.deref {
			object, _ := pointee(t)
			val = v.pointedIn(st, st.mem, object, cur)
			return
		}
		for _, index := range place.fields {
			cur, t, _ = v.member(st, st.mem, cur, t, index)
		}
		val = cur
	})
	return val
}

// keptInArray states that a slice header is that of entry with at least
// its length, in the same array at the same offset with the same capacity,
// or one in an array made since brk, at offset zero.
func (v *fnVerifier) keptInArray(now, before value, t types.Type, brk *logic.Term) *logic.Term {
	inOld := logic.And(logic.Eq(now[0], before[0]), logic.Eq(now[1], before[1]), logic.Eq(now[3], before[3]), logic.Le(before[2], now[2]))
	inNew := logic.And(logic.Le(brk, now[0]), logic.Eq(now[1], logic.IntLit(0)))
	if v.pass.TypesSizes.Sizeof(elemType(t)) == 0 {
		inNew = logic.Eq(now[1], logic.IntLit(0))
	}
	return logic.Or(inOld, inNew)
}

// holdsType reports whether a value of type held is, or holds by value in
// a field or an element of an array, a value of the underlying type of t,
// so that assigning it may write a place of type t.
func holdsType(held, t types.Type) bool {
	if types.IdenticalIgnoreTags(held.Underlying(), t.Underlying()) {
		return true
	}
	switch u := held.Underlying().(type) {
	case *types.Struct:
		for i := range u.NumFields() {
			if holdsType(u.Field(i).Type(), t) {
				return true
			}
		}
	case *types.Array:
		return holdsType(u.Elem(), t)
	}
	return false
}
