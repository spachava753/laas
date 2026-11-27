package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
)

// Labelled break and continue (F37, step 3).
//
// A loop is verified by induction in continuation style (loop in
// loops.go): continue is the continuation that ends an iteration, which
// checks the invariants and the variant, and break the one that leaves the
// loop. A label gives the continuations of the statement it labels a name:
// continue L ends an iteration of the loop L, wherever it stands inside it,
// so L's invariants must hold there and L's variant must have decreased
// from L's head; the loops inside L are left, so theirs need not hold.
// break L goes on after L. A label is in scope only inside the statement
// it labels, and a function literal cannot name it, so the table of labels
// is held for the time the statement is being verified.
//
// A range over a map is active while its body runs (v.ranges); a jump out
// of inner ranges runs its continuation with the ranges as they were where
// the continuation was made, as an unlabelled break or continue does.

// labelTarget is where break and continue with a label go.
type labelTarget struct {
	brk, cont func(*state)
	ranges    []*activeRange
}

// labeled verifies a labelled statement. The annotations of a labelled
// loop stand above its label; the scanner reports one between the label and
// its statement, which stands between no two statements.
func (v *fnVerifier) labeled(s *ast.LabeledStmt, spec *loopSpec, st *state, c ctrl, rest func(*state)) {
	label, _ := v.info.Defs[s.Label].(*types.Label)
	switch inner := s.Stmt.(type) {
	case *ast.ForStmt:
		spec.label = label
		v.forStmt(inner, spec, nil, st, v.logging(inner, rest))
	case *ast.RangeStmt:
		spec.label = label
		v.rangeStmt(inner, spec, st, v.logging(inner, rest))
	case *ast.SwitchStmt, *ast.TypeSwitchStmt:
		after := v.logging(inner, rest)
		defer v.withLabel(label, &labelTarget{brk: after, ranges: v.ranges})()
		v.stmt(inner, st, c, rest)
	default:
		// Only goto can name the label of another statement, and goto is
		// refused where it stands.
		v.stmt(inner, st, c, rest)
	}
}

// withLabel makes a label name its target until the returned function
// runs.
func (v *fnVerifier) withLabel(label *types.Label, target *labelTarget) func() {
	if v.labels == nil {
		v.labels = map[*types.Label]*labelTarget{}
	}
	saved, had := v.labels[label]
	v.labels[label] = target
	return func() {
		if had {
			v.labels[label] = saved
		} else {
			delete(v.labels, label)
		}
	}
}

// jump runs break L or continue L.
func (v *fnVerifier) jump(s *ast.BranchStmt, st *state) {
	label, _ := v.info.Uses[s.Label].(*types.Label)
	target := v.labels[label]
	var to func(*state)
	if target != nil {
		to = target.brk
		if s.Tok == token.CONTINUE {
			to = target.cont
		}
	}
	if to == nil {
		v.unsupported(s.Pos(), rSelect, fmt.Sprintf("%s %s is not supported: the label names a select statement or a statement that is not supported", s.Tok, s.Label.Name))
	}
	saved := v.ranges
	v.ranges = target.ranges
	defer func() { v.ranges = saved }()
	to(st)
}
