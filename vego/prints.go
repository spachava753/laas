package vego

import (
	"go/ast"
	"go/types"
	"slices"

	"github.com/spachava753/laas/vego/internal/logic"
	"gopkg.in/yaml.v3"
)

// A trusted function that formats may claim, under prints, what it does
// with the writer it is given: prints: {w: fmt.Sprintf} on fmt.Fprintf
// says that Fprintf formats its other arguments as fmt.Sprintf would, then
// calls w.Write once with exactly the bytes Sprintf returns, and returns
// what that Write returned, and calls nothing else of w.
//
// The claim lets the call be verified, where the writer is a value of a
// concrete type whose conversion to io.Writer is refused and whose Write
// has a contract of its own, as the Sprint function followed by that Write:
// fmt.Fprintf(&b, "%d items", n) for a strings.Builder b, a bytes.Buffer,
// or a bufio.Writer. No interface value is made, so the refusal of the
// conversion, which stands (the contract of (io.Writer).Write has no bound
// for a buffer's Write, and a bufio.Writer's Write calls through the writer
// it keeps), is not reached; what is checked is the requires of the
// writer's own Write for the bytes formatted, which for a buffer is a bound
// on its length and on what is formatted. TestPrintsClaims holds the claim
// against the shipped functions with writers that record their calls.

// addPrints reads the prints of an entry: a mapping from the writer
// parameter to the function whose result is written, as in
// prints: {w: fmt.Sprintf}.
func (f *trustFile) addPrints(entry *trustEntry, node *yaml.Node) {
	if node.Kind != yaml.MappingNode || len(node.Content) != 2 || node.Content[0].Kind != yaml.ScalarNode || node.Content[1].Kind != yaml.ScalarNode {
		f.problem(node.Line, "prints of %s must map the writer to the function whose result is written to it, as in {w: fmt.Sprintf}", entry.key)
		return
	}
	key, value := node.Content[0], node.Content[1]
	entry.prints = append(entry.prints, trustKeep{name: key.Value, line: key.Line, col: key.Column,
		dests: []trustFormula{{text: value.Value, line: value.Line, col: value.Column}}})
}

// readPrints checks the prints of an entry against the function: the
// writer is a parameter of an interface type with a Write method that the
// function lists under runs and modifies, the function formats, and the
// function it names is a function of the same package whose parameters are
// those of this one but the writer, in order, of the same names and types,
// and whose entry formats the same parameters.
func (pv *pkgVerifier) readPrints(fn *funcInfo, entry *trustEntry) {
	if len(entry.prints) == 0 {
		return
	}
	item := entry.prints[0]
	param, ok := fn.paramNames[item.name]
	sig := fn.obj.Type().(*types.Signature)
	switch {
	case len(entry.prints) > 1:
		fn.defect("its prints names more than one writer")
		return
	case !ok || param == sig.Recv():
		fn.defect("its prints %q: %s is not a parameter", item.name, item.name)
		return
	case !isIface(param.Type()) || !hasWrite(param.Type()):
		fn.defect("its prints names %s, of type %s, which has no Write method", item.name, param.Type())
		return
	case !fn.runs.get(param):
		fn.defect("its prints names %s, which its runs does not list; a function that calls Write of it runs it", item.name)
		return
	case fn.formatted == nil:
		fn.defect("its prints names a writer, but it formats nothing")
		return
	}
	pkgPath, name, _ := splitFuncName(item.dests[0].text)
	if fn.obj.Pkg() == nil || pkgPath != fn.obj.Pkg().Path() {
		fn.defect("its prints names %s, which is not a function of package %s", item.dests[0].text, fn.obj.Pkg().Path())
		return
	}
	as, isFunc := fn.obj.Pkg().Scope().Lookup(name).(*types.Func)
	if !isFunc {
		fn.defect("its prints names %s, which is not a function of package %s", item.dests[0].text, pkgPath)
		return
	}
	asSig := as.Type().(*types.Signature)
	var rest []*types.Var
	for i := range sig.Params().Len() {
		if sig.Params().At(i) != param {
			rest = append(rest, sig.Params().At(i))
		}
	}
	same := asSig.Params().Len() == len(rest) && asSig.Variadic() == sig.Variadic()
	for i := 0; same && i < len(rest); i++ {
		p := asSig.Params().At(i)
		same = p.Name() == rest[i].Name() && types.Identical(p.Type(), rest[i].Type())
	}
	if !same {
		fn.defect("its prints names %s, whose parameters are not those of %s without %s", item.dests[0].text, fn.obj.Name(), item.name)
		return
	}
	other := pv.entryFor(as.FullName())
	var mine, its []string
	for _, f := range entry.formats {
		mine = append(mine, f.text)
	}
	if other != nil {
		for _, f := range other.formats {
			its = append(its, f.text)
		}
	}
	slices.Sort(mine)
	slices.Sort(its)
	if other == nil || !slices.Equal(mine, its) {
		fn.defect("its prints names %s, whose entry does not format what this one formats", item.dests[0].text)
		return
	}
	fn.prints, fn.printsAs = param, as
}

// hasWrite reports whether a type has a method Write(p []byte) (n int, err
// error).
func hasWrite(t types.Type) bool {
	obj, _, _ := types.LookupFieldOrMethod(t, true, nil, "Write")
	method, ok := obj.(*types.Func)
	if !ok {
		return false
	}
	sig := method.Type().(*types.Signature)
	return sig.Params().Len() == 1 && sig.Results().Len() == 2 && isSlice(sig.Params().At(0).Type())
}

// printedInto returns, for a call of a function whose contract prints to a
// writer, the expression passed as the writer and the Write method of its
// type, when the call is to be verified as the Sprint function followed by
// that Write: the writer is a value of a concrete type, not an interface,
// whose conversion to io.Writer is refused, and whose Write has a contract.
// A value whose conversion is allowed, as a file or a writer of the
// project, keeps the path it has: it is converted and written through the
// contract of (io.Writer).Write.
func (v *fnVerifier) printedInto(call *ast.CallExpr, fn *funcInfo) (ast.Expr, *funcInfo) {
	if fn.prints == nil {
		return nil, nil
	}
	for _, b := range v.bindCall(call, fn.obj.Type().(*types.Signature)) {
		if b.param != fn.prints || b.expr == nil {
			continue
		}
		t := v.info.TypeOf(b.expr)
		if t == nil || isIface(t) || (growsUnbounded(t) == "" && wrapsKept(t) == "") {
			return nil, nil
		}
		obj, _, _ := types.LookupFieldOrMethod(t, true, v.pass.Pkg, "Write")
		method, ok := obj.(*types.Func)
		if !ok {
			return nil, nil
		}
		if write := v.contractOf(method); write != nil {
			return b.expr, write
		}
		return nil, nil
	}
	return nil, nil
}

// callPrinted verifies a call of a function whose contract prints to a
// writer that printedInto names: the arguments are evaluated, the writer as
// the value it is and not converted, the formatting is checked as for the
// function itself, the Sprint function its prints names is applied to the
// other arguments, and the writer's own Write to a new slice of the bytes
// it returned. The results are those of Write.
func (v *fnVerifier) callPrinted(call *ast.CallExpr, fn *funcInfo, writer ast.Expr, write *funcInfo, st *state, guard []*logic.Term, reach func()) []value {
	sig := fn.obj.Type().(*types.Signature)
	args := map[*types.Var]value{}
	for _, b := range v.bindCall(call, sig) {
		if b.param == fn.prints {
			// Go converts the writer to the interface of the parameter; the
			// call is verified without that interface value, so the value
			// is evaluated as it is, and only its own Write sees it.
			inner := ast.Unparen(b.expr)
			v.converting[inner]++
			args[b.param] = v.eval(b.expr, st, guard)
			v.converting[inner]--
			continue
		}
		args[b.param] = v.evalPassed(b, st, guard)
	}
	reach()
	formatted := v.checkFormattedAlloc(st, guard, call, fn, args, v.held)
	v.checkFormatRuns(call, v.formatRuns(call, fn), st, guard)
	if formatted == nil {
		// What is formatted has parts whose length no formula states, so
		// nothing bounds what Write is given, which its requires needs.
		v.report(call.Pos(), "%s writes to %s text whose length is not known: it formats the text of an error, what a String or Error method returns, "+
			"or strings or slices inside an element of a slice, and the Write of %s needs a bound on what it is given; format only values whose length is bounded",
			fn.obj.Name(), types.ExprString(writer), types.TypeString(v.info.TypeOf(writer), types.RelativeTo(v.pass.Pkg)))
		v.cut(st, guard)
		return v.nothingKnown(fn.obj, st)
	}
	as := v.contractOf(fn.printsAs)
	if as == nil {
		v.unsupported(call.Pos(), "the function that the prints of "+fn.trust.key+" names has no contract")
	}
	// The call of the Sprint function has the arguments of this one but
	// the writer.
	asArgs := map[*types.Var]value{}
	asSig := fn.printsAs.Type().(*types.Signature)
	var rest []ast.Expr
	for _, b := range v.bindCall(call, sig) {
		if b.param == fn.prints {
			continue
		}
		for i := range asSig.Params().Len() {
			if asSig.Params().At(i).Name() == b.param.Name() {
				asArgs[asSig.Params().At(i)] = args[b.param]
			}
		}
	}
	for i, arg := range call.Args {
		if i != slices.IndexFunc(v.bindCall(call, sig), func(b passedArg) bool { return b.param == fn.prints }) {
			rest = append(rest, arg)
		}
	}
	asCall := &ast.CallExpr{Fun: call.Fun, Lparen: call.Lparen, Args: rest, Ellipsis: call.Ellipsis, Rparen: call.Rparen}
	v.noteUse(as, call.Pos())
	printed := v.invoke(asCall, as, asArgs, st, guard)[0][0]
	if formatted != nil {
		st.assume(logic.Implies(logic.And(guard...), logic.Le(logic.Len(printed), formatted)))
	}
	// The writer's own Write of a new slice of those bytes.
	writeSig := write.obj.Type().(*types.Signature)
	p := writeSig.Params().At(0)
	bytes := v.copiedBytes(st, printed, p.Type())
	shown := &ast.Ident{NamePos: call.Lparen, Name: "[]byte(" + fn.printsAs.Name() + "(...))"}
	writeCall := &ast.CallExpr{Fun: &ast.SelectorExpr{X: writer, Sel: &ast.Ident{NamePos: call.Lparen, Name: "Write"}}, Lparen: call.Lparen, Args: []ast.Expr{shown}, Rparen: call.Rparen}
	v.noteUse(write, call.Pos())
	return v.invoke(writeCall, write, map[*types.Var]value{writeSig.Recv(): args[fn.prints], p: bytes}, st, guard)
}
