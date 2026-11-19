package vego

import (
	"fmt"
	"go/ast"
	"go/constant"
	"go/types"
	"unicode/utf8"

	"github.com/spachava753/laas/vego/internal/logic"
	"golang.org/x/tools/go/types/typeutil"
)

// What errors.Is finds in an error.
//
// errors.Is(err, target) walks the tree of err: err itself, then whatever
// its Unwrap method returns, and so on. At each error it reports true if
// the error equals the target, or if the error has an Is method that
// reports true. When err or target is nil it reports whether both are,
// and calls nothing.
//
// The errors that errors.New and fmt.Errorf return have no Is method, and
// only fmt.Errorf's have an Unwrap method: with one %w verb applied to an
// error, Unwrap returns that error, and with several it returns all of
// them. So the tree of such an error is the error itself and, for one %w,
// the tree of the error it wraps. Which operand a %w applies to is read
// from the format, below. A tree whose shape is not certain is not known:
// errors.Is on it is then an unknown boolean, never a guess.

// wrapping says what an error made by errors.New or fmt.Errorf wraps.
type wrapping int

const (
	// treeUnknown: the call may wrap something, and it is not known what.
	treeUnknown wrapping = iota
	// wrapsNothing: the tree is the error alone.
	wrapsNothing
	// wrapsOperand: the tree is the error and the tree of one operand.
	wrapsOperand
)

// maxFormatDigits is the most digits a width or precision may have for the
// format to be read. fmt stops reading the rest of a format at a number
// that has grown past a million, which takes at least eight digits; a
// format with seven or more is not read, which keeps a margin.
const maxFormatDigits = 6

// formatWraps reads a format of fmt.Errorf with the given operands and
// says what the result wraps: nothing, the operand at the returned index,
// or something not known. isError says which operands have type error,
// and format is nil when the format is not a constant.
//
// The rules are those of fmt's doPrintf for the formats it can read
// without doubt: after a %, flags, then an optional width and an optional
// precision, then the verb, which is any rune. A verb takes the next
// operand, except %, which prints a percent sign whatever stands between,
// and a % at the end of the format, which has no verb. A %w applied to an
// operand that is an error makes the result wrap it; applied to anything
// else, or to an operand that is missing, it wraps nothing. Explicit
// argument indexes, widths or precisions taken from operands, long
// numbers, and more than one %w are not read.
func formatWraps(format *string, isError []bool) (wrapping, int) {
	someError := false
	for _, e := range isError {
		someError = someError || e
	}
	if !someError {
		// Only an error can be wrapped, however the format reads.
		return wrapsNothing, -1
	}
	if format == nil {
		return treeUnknown, -1
	}
	text := *format
	operand, wrapped, verbs := 0, -1, 0
	for i := 0; i < len(text); {
		if text[i] != '%' {
			i++
			continue
		}
		i++
		for i < len(text) && (text[i] == '#' || text[i] == '0' || text[i] == '+' || text[i] == '-' || text[i] == ' ') {
			i++
		}
		digits := func() bool {
			start := i
			for i < len(text) && '0' <= text[i] && text[i] <= '9' {
				i++
			}
			return i-start <= maxFormatDigits
		}
		if i < len(text) && (text[i] == '[' || text[i] == '*') {
			return treeUnknown, -1
		}
		if !digits() {
			return treeUnknown, -1
		}
		if i < len(text) && text[i] == '.' {
			i++
			if i < len(text) && (text[i] == '[' || text[i] == '*') {
				return treeUnknown, -1
			}
			if !digits() {
				return treeUnknown, -1
			}
		}
		if i >= len(text) {
			// A % at the end has no verb and takes no operand.
			break
		}
		verb, size := utf8.DecodeRuneInString(text[i:])
		i += size
		switch verb {
		case '%':
			continue
		case '[':
			return treeUnknown, -1
		case 'w':
			verbs++
			if verbs > 1 {
				return treeUnknown, -1
			}
			if operand < len(isError) && isError[operand] {
				wrapped = operand
			}
		}
		operand++
	}
	if wrapped < 0 {
		return wrapsNothing, -1
	}
	return wrapsOperand, wrapped
}

// callWraps says what the error a call of errors.New or fmt.Errorf makes
// wraps, and which argument when it wraps one.
func (pv *pkgVerifier) callWraps(call *ast.CallExpr) (wrapping, ast.Expr) {
	callee := typeutil.StaticCallee(pv.info, call)
	if callee == nil || callee.Name() != "Errorf" || len(call.Args) == 0 {
		return wrapsNothing, nil
	}
	if call.Ellipsis.IsValid() {
		return treeUnknown, nil
	}
	var format *string
	if value := pv.info.Types[call.Args[0]].Value; value != nil && value.Kind() == constant.String {
		text := constant.StringVal(value)
		format = &text
	}
	operands := call.Args[1:]
	errs := make([]bool, len(operands))
	for i, operand := range operands {
		t := pv.info.TypeOf(operand)
		errs[i] = t != nil && isError(t)
	}
	tree, index := formatWraps(format, errs)
	if tree != wrapsOperand {
		return tree, nil
	}
	return tree, operands[index]
}

// errorTree is an error whose tree is known: the error, and the error it
// wraps, or nil when it wraps nothing.
type errorTree struct {
	err, wraps *logic.Term
}

// noteTree records an error whose tree is known, and states for every
// target met so far what errors.Is reports for the two.
func (v *fnVerifier) noteTree(sink *state, tree errorTree) {
	known := false
	for _, other := range v.trees {
		known = known || other.err.Name == tree.err.Name
	}
	if !known {
		v.trees = append(v.trees, tree)
	}
	if sink == nil {
		return
	}
	for _, target := range v.isTargets {
		v.treeInstance(sink, tree, target)
	}
}

// treeInstance states what errors.Is reports for an error whose tree is
// known and a target: whether the error is the target, or wraps an error
// that is not nil and in whose tree errors.Is finds the target.
func (v *fnVerifier) treeInstance(sink *state, tree errorTree, target *logic.Term) {
	note := "tree " + tree.err.Name + " " + target.String()
	if sink.noted[note] {
		return
	}
	sink.noted[note] = true
	found := logic.Eq(tree.err, target)
	if tree.wraps != nil {
		found = logic.Or(found, logic.And(logic.Not(logic.IsNil(tree.wraps)), logic.Is(tree.wraps, target)))
	}
	fact := logic.Iff(logic.Is(tree.err, target), found)
	v.fact(sink, fact)
	v.noteIs(sink, fact)
}

// errorsIs evaluates a call of errors.Is. It runs the Is and Unwrap
// methods of the errors in the tree of its first argument, so that error
// must have a known origin; of the target it only compares the dynamic
// type and, when that is comparable, the value.
func (v *fnVerifier) errorsIs(call *ast.CallExpr, st *state, guard []*logic.Term) *logic.Term {
	err, target := call.Args[0], call.Args[1]
	if !v.knownError(v.originsOf(v.fn.decl.Body), err, -1, map[*types.Var]bool{}) {
		v.unsupported(err.Pos(), fmt.Sprintf("errors.Is would run the Is and Unwrap methods of %s, an error whose origin is not known; "+
			"only an error made by errors.New or fmt.Errorf, here or in a verified function, can be its first argument%s",
			types.ExprString(err), v.originWhy(err)))
	}
	errorType := types.Universe.Lookup("error").Type()
	is := logic.Is(v.evalAs(err, errorType, st, guard)[0], v.evalAs(target, errorType, st, guard)[0])
	v.noteIs(st, is)
	return is
}

// isErrorsIs recognises errors.Is.
func isErrorsIs(callee *types.Func) bool {
	return callee != nil && callee.Pkg() != nil && callee.Pkg().Path() == "errors" && callee.Name() == "Is"
}

// originWhy says, for an error expression that names a package-level error
// variable which may not be taken to hold the error it was declared with,
// why not, after a separator; otherwise it returns "".
func (v *fnVerifier) originWhy(e ast.Expr) string {
	variable := v.namedVariable(e)
	if variable == nil || variable.Pkg() == nil || variable.Parent() != variable.Pkg().Scope() {
		return ""
	}
	if _, why := v.usableSentinel(variable); why != "" {
		return "; " + why
	}
	return ""
}
