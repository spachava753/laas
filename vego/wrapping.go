package vego

import (
	"fmt"
	"go/ast"
	"go/constant"
	"go/token"
	"go/types"
	"path/filepath"
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
		// A value of a concrete type that implements error is an error to
		// %w, which asserts its operand to error (F33).
		errs[i] = t != nil && (isError(t) || pv.concreteErrorType(operand, -1) != nil)
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
	for _, pair := range v.asPairs {
		v.asFacts(sink, pair, map[string]bool{})
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
	// Known origin of either kind makes the methods harmless, also with any
	// target, and errors.Is a function of the two errors. What it finds is
	// known only of a made error, from noteTree.
	if !v.knownError(v.bodyOrigins(), err, -1) {
		v.unsupported(err.Pos(), fmt.Sprintf("errors.Is would run the Is and Unwrap methods of %s, an error whose origin is not known; "+
			"only an error made by errors.New or fmt.Errorf, here or in a verified function, one that a contract vouches for, or one that holds a value of a type whose errors have a known origin, "+
			"can be its first argument%s",
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

// localOriginWhy says, for an error expression that names a local variable
// of unknown origin, after a separator, which assignment makes it unknown
// and what to do. Along the paths it names a definition that reaches the
// use; otherwise it says why every assignment counts and names one of them.
func (v *fnVerifier) localOriginWhy(e ast.Expr) string {
	id, ok := ast.Unparen(e).(*ast.Ident)
	if !ok {
		return ""
	}
	variable, ok := v.info.ObjectOf(id).(*types.Var)
	if !ok || !isError(variable.Type()) || (variable.Pkg() != nil && variable.Parent() == variable.Pkg().Scope()) {
		return ""
	}
	o := v.bodyOrigins()
	if o.unknown[variable] {
		return ""
	}
	if o.alongPath(variable, id.Pos()) {
		if defs, ok := v.reaching(o, variable, id.Pos()); ok {
			return v.pathWhy(o, id, defs)
		}
	}
	if v.isParameter[variable] || o.open[variable] {
		return ""
	}
	return v.textWhy(o, id, variable)
}

// assignedWhere describes what an assignment gives a variable and where.
func (v *fnVerifier) assignedWhere(from source) (where, what string) {
	at := v.pass.Fset.Position(from.expr.Pos())
	where = fmt.Sprintf("%s at %s:%d:%d", types.ExprString(from.expr), filepath.Base(at.Filename), at.Line, at.Column)
	what = "an error whose origin is not known"
	if _, isCall := ast.Unparen(from.expr).(*ast.CallExpr); isCall {
		what = "a call whose errors nothing vouches for"
	}
	if key := v.restedOnCall(from.expr); key != "" {
		// No project entry can vouch for these errors (restedon.go).
		what = fmt.Sprintf("the error of a call of %s through an interface value, which has no known origin: shipped entries rest on the entry of %s, "+
			"so no trust file can vouch for its errors; return the error as it is, or compare it with == to a sentinel, as in err == io.EOF", key, key)
	}
	if t := v.concreteErrorType(from.expr, from.index); t != nil {
		// Which condition of the typed origin the type fails, and what
		// to change (the orchestrator's condition on S4).
		what = fmt.Sprintf("a value of type %s, whose errors have no known origin: %s", types.TypeString(t, types.RelativeTo(v.pass.Pkg)), v.typedOriginWhy(t))
	}
	return where, what
}

// copiedVariable returns the local error variable an assignment copies, or
// nil.
func (v *fnVerifier) copiedVariable(from source) (*ast.Ident, *types.Var) {
	id, ok := ast.Unparen(from.expr).(*ast.Ident)
	if !ok || from.index >= 0 {
		return nil, nil
	}
	variable, ok := v.info.ObjectOf(id).(*types.Var)
	if !ok || !isError(variable.Type()) || (variable.Pkg() != nil && variable.Parent() == variable.Pkg().Scope()) {
		return nil, nil
	}
	return id, variable
}

// firstUnknown returns, of the definitions that reach a use, the one to name
// for a use without a known origin: one that brings the unknown error
// itself before one that copies another variable, then the first by
// position. known reports whether some definition gives a known origin.
func (v *fnVerifier) firstUnknown(o *origins, defs []*def) (bad *def, known bool) {
	copies := func(d *def) bool {
		_, copied := v.copiedVariable(d.src)
		return d.kind == defExpr && copied != nil
	}
	for _, d := range defs {
		switch {
		case v.knownDef(o, d, newSearch()):
			known = true
		case bad == nil, copies(bad) && !copies(d), copies(bad) == copies(d) && d.pos < bad.pos:
			bad = d
		}
	}
	return bad, known
}

// trail describes an assignment of unknown origin and, when it copies
// another variable, follows the copy to the assignment that brought the
// unknown error, through at most four variables. root is that assignment's
// expression, and mixed reports whether a variable the trail passes through
// also holds errors of known origin there, so that giving the error of root
// a variable of its own would help.
type trail struct {
	text, root    string
	mixed, copied bool
}

func (v *fnVerifier) describe(o *origins, from source, depth int, seen map[*def]bool) trail {
	id, variable := v.copiedVariable(from)
	if id == nil || depth >= 4 {
		where, what := v.assignedWhere(from)
		return trail{text: where + ", " + what, root: types.ExprString(from.expr)}
	}
	at := v.pass.Fset.Position(id.Pos())
	held := v.heldBy(o, variable, id, depth+1, seen)
	held.text = fmt.Sprintf("%s at %s:%d:%d, and %s holds there %s", id.Name, filepath.Base(at.Filename), at.Line, at.Column, id.Name, held.text)
	held.copied = true
	return held
}

// heldBy says what error of unknown origin a variable holds at a use.
func (v *fnVerifier) heldBy(o *origins, variable *types.Var, id *ast.Ident, depth int, seen map[*def]bool) trail {
	unknown := trail{text: "an error whose origin is not known"}
	if o.unknown[variable] {
		return unknown
	}
	if o.alongPath(variable, id.Pos()) {
		defs, ok := v.reaching(o, variable, id.Pos())
		if !ok {
			return unknown
		}
		var fresh []*def
		for _, d := range defs {
			if !seen[d] {
				fresh = append(fresh, d)
			}
		}
		bad, known := v.firstUnknown(o, fresh)
		if bad == nil {
			return unknown
		}
		seen[bad] = true
		var t trail
		switch bad.kind {
		case defParam, defOpen:
			t = trail{text: "the error it was passed as a parameter"}
		case defArgs:
			for _, arg := range o.args[bad.variable] {
				if !v.knownError(o, arg.expr, arg.index) {
					t = v.describe(o, arg, depth, seen)
					t.text = "the error its function literal is given, " + t.text
					break
				}
			}
		default:
			t = v.describe(o, bad.src, depth, seen)
			t.text = "the error assigned " + t.text
		}
		t.mixed = t.mixed || known
		return t
	}
	if v.isParameter[variable] || o.open[variable] {
		return trail{text: "the error it was passed as a parameter"}
	}
	known := false
	var bad *source
	for _, from := range o.sources[variable] {
		s := newSearch()
		s.vars[variable] = true
		switch {
		case v.knownErrorIn(o, from.expr, from.index, s):
			known = true
		case bad == nil:
			bad = &from
		}
	}
	if bad == nil {
		return unknown
	}
	t := v.describe(o, *bad, depth, seen)
	t.text = "the error assigned " + t.text
	t.mixed = t.mixed || known
	return t
}

// ownVariable is the remedy, after a separator, for an error of unknown
// origin that a copy brought into target. When a variable the copy came
// through also holds errors of known origin, the error of the assignment
// the copy came from needs a variable of its own; when only target does,
// that error must stay out of target. Otherwise nothing a variable can do
// helps, and nothing is said.
func ownVariable(t trail, target string, targetMixed bool) string {
	switch {
	case t.root == "":
		return ""
	case t.mixed:
		return fmt.Sprintf("; give the error of %s a variable of its own", t.root)
	case targetMixed:
		return fmt.Sprintf("; keep the error of %s in a variable of its own instead of assigning it to %s", t.root, target)
	}
	return ""
}

// pathWhy names a definition, of those that reach a use along the paths,
// that gives no known origin, and says what to do.
func (v *fnVerifier) pathWhy(o *origins, id *ast.Ident, defs []*def) string {
	bad, known := v.firstUnknown(o, defs)
	if bad == nil {
		return ""
	}
	seen := map[*def]bool{bad: true}
	switch bad.kind {
	case defParam, defOpen:
		if !known {
			return ""
		}
		return fmt.Sprintf("; %s is a parameter, and on a path to here nothing assigns it, so it may still hold the error it was passed, "+
			"which can be returned unchanged but not formatted", id.Name)
	case defArgs:
		for _, arg := range o.args[bad.variable] {
			if !v.knownError(o, arg.expr, arg.index) {
				t := v.describe(o, arg, 0, seen)
				return fmt.Sprintf("; %s is a parameter of the function literal, and is given %s; "+
					"pass the literal only errors of known origin, or return %s unchanged", id.Name, t.text, id.Name)
			}
		}
		return ""
	}
	t := v.describe(o, bad.src, 0, seen)
	loop := aroundLoop(o.homeOf(bad.variable), bad.pos, id.Pos())
	switch {
	case !known:
		return fmt.Sprintf("; %s is assigned %s%s", id.Name, t.text, ownVariable(t, id.Name, false))
	case t.copied && loop:
		return fmt.Sprintf("; in an earlier iteration of the loop, %s was assigned %s%s", id.Name, t.text, ownVariable(t, id.Name, true))
	case t.copied:
		return fmt.Sprintf("; on a path that reaches this use, %s is assigned %s%s", id.Name, t.text, ownVariable(t, id.Name, true))
	case loop:
		return fmt.Sprintf("; %s may hold here the error assigned %s, in an earlier iteration of the loop; "+
			"declare %s inside the loop, or give that error a variable of its own", id.Name, t.text, id.Name)
	}
	return fmt.Sprintf("; %s may hold here the error assigned %s, on a path that reaches this use; "+
		"give that error a variable of its own", id.Name, t.text)
}

// aroundLoop reports whether a definition reaches a use only by going around
// a loop of a body that holds both: it stands after the use, or in the post
// statement of the loop.
func aroundLoop(body *ast.BlockStmt, def, use token.Pos) bool {
	around := false
	ast.Inspect(body, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.FuncLit:
			return false
		case *ast.ForStmt, *ast.RangeStmt:
			if n.Pos() <= def && def < n.End() && n.Pos() <= use && use < n.End() {
				post, _ := n.(*ast.ForStmt)
				around = def > use || (post != nil && post.Post != nil && post.Post.Pos() <= def && def < post.Post.End())
			}
		}
		return true
	})
	return around
}

// textWhy says, for a variable whose use is decided from every assignment to
// it, why, and names the first assignment that gives no known origin.
func (v *fnVerifier) textWhy(o *origins, id *ast.Ident, variable *types.Var) string {
	home := o.homeOf(variable)
	reason := ""
	place := func(lit *ast.FuncLit) string {
		at := v.pass.Fset.Position(lit.Pos())
		return fmt.Sprintf("%s:%d:%d", filepath.Base(at.Filename), at.Line, at.Column)
	}
	if lit := o.outermostIn(home, id.Pos()); lit != nil {
		reason = fmt.Sprintf("the function literal at %s reads %s and may run after any assignment to it", place(lit), id.Name)
	} else {
		for _, at := range o.sites[variable] {
			if lit := o.outermostIn(home, at); lit != nil && !o.deferred[lit] {
				reason = fmt.Sprintf("%s is assigned in the function literal at %s, which may run at any point, so every assignment to %s counts",
					id.Name, place(lit), id.Name)
				break
			}
		}
	}
	var bad *source
	known := false
	for _, from := range o.sources[variable] {
		s := newSearch()
		s.vars[variable] = true
		if v.knownErrorIn(o, from.expr, from.index, s) {
			known = true
			continue
		}
		if bad == nil {
			bad = &from
		}
	}
	if bad == nil {
		return ""
	}
	t := v.describe(o, *bad, 0, map[*def]bool{})
	switch {
	case reason != "" && known && t.copied:
		return fmt.Sprintf("; %s, and %s is assigned %s%s", reason, id.Name, t.text, ownVariable(t, id.Name, true))
	case reason != "" && known:
		return fmt.Sprintf("; %s, and %s is assigned %s; give that error a variable of its own", reason, id.Name, t.text)
	case reason != "" || bad.expr.Pos() < id.Pos() || t.copied:
		// An assignment before the use may be the error that is used,
		// and then it is that call's errors that nothing vouches for.
		return fmt.Sprintf("; %s is assigned %s%s", id.Name, t.text, ownVariable(t, id.Name, false))
	}
	return fmt.Sprintf("; %s is also assigned %s, later, and an error variable has a known origin only when "+
		"every assignment to it gives it one; give that a variable of its own", id.Name, t.text)
}

// originWhy says, for an error expression that names a package-level error
// variable which may not be taken to hold the error it was declared with,
// or which holds an error that was not made by errors.New or fmt.Errorf,
// why, after a separator; otherwise it returns "".
func (v *fnVerifier) originWhy(e ast.Expr) string {
	if why := v.localOriginWhy(e); why != "" {
		return why
	}
	variable := v.namedErrorVariable(e)
	if variable == nil {
		return ""
	}
	r, why := v.resolve(variable)
	switch {
	case why != "":
		return "; " + why
	case r.info.Kind != stableMade:
		return fmt.Sprintf("; %s is not initialised with errors.New or fmt.Errorf, so nothing is known of its methods", v.spelling(variable))
	}
	return ""
}

// restedOnCall returns the key of the method a call of e makes through an
// interface value when shipped entries rest on its entry, so that no trust
// file can vouch for its errors (restedon.go), or "".
func (v *fnVerifier) restedOnCall(e ast.Expr) string {
	call, ok := ast.Unparen(e).(*ast.CallExpr)
	if !ok {
		return ""
	}
	sel, ok := ast.Unparen(call.Fun).(*ast.SelectorExpr)
	if !ok {
		return ""
	}
	selection := v.info.Selections[sel]
	if selection == nil || selection.Kind() != types.MethodVal || !isIface(selection.Recv()) {
		return ""
	}
	method, ok := selection.Obj().(*types.Func)
	if !ok {
		return ""
	}
	if _, rested := restedOn[method.FullName()]; !rested {
		return ""
	}
	return method.FullName()
}
