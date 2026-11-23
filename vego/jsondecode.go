package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"math/big"
	"strings"

	"golang.org/x/tools/go/types/typeutil"

	"github.com/spachava753/laas/vego/internal/logic"
)

// Decoding JSON (F29, step 3). A shipped entry with decodes, json.Unmarshal,
// names its parameter of type any into which it decodes the []byte it is
// handed, as package encoding/json does. Its claim: it writes only the
// exported fields that encoding/json writes, and of the embedded structs
// their exported fields; it stores into them only memory it makes during
// the call, when what it decodes into holds no slice with capacity, no
// map, and no pointer that is not nil (the decoder appends into a slice's
// array, keeps a map's entries, and decodes through a pointer it finds);
// it runs no method of what it decodes into but those of time.Time,
// json.RawMessage, and json.Number; it keeps nothing of the data; it writes
// on an error too, before and after the field that failed; and what it
// allocates is within a bound in proportion to the length of the data.
//
// So a call is verified as a trusted call made for it. The value decoded
// into is &x for a variable x, a field, or an element, or a pointer to a
// struct. Its type is walked as for encoding (json.go). What it holds
// must be nil where the decoder would reuse it. A struct is written
// through the pointer, with a frame of the fields json writes, so that
// unexported fields keep their values; anything else is a result of the
// made contract, stored into the variable, as `x = decoded` would be.

// readDecodes reads what the entry of a trusted function lists under
// decodes: one parameter of type any, decoded from the function's one
// []byte parameter. Only a shipped entry may.
func (pv *pkgVerifier) readDecodes(fn *funcInfo, entry *trustEntry) {
	if len(entry.decodes) == 0 {
		return
	}
	if entry.file == nil || !entry.file.shipped {
		fn.defect("it lists decodes, which only the entries that come with vego can list; a function of your own that decodes into a value it is handed is not supported yet")
		return
	}
	sig := fn.obj.Type().(*types.Signature)
	for _, item := range entry.decodes {
		param, ok := fn.paramNames[item.text]
		switch {
		case !ok || param == sig.Recv():
			fn.defect("its decodes %q: %s is not a parameter", item.text, item.text)
		case fn.decoded != nil:
			fn.defect("its decodes lists %s and %s; it can list one parameter of type any", fn.decoded.Name(), item.text)
		case !isAnyParam(sig, param) || sig.Variadic():
			fn.defect("its decodes lists %s, of type %s; it can list a parameter of type any", item.text, param.Type())
		default:
			fn.decoded = param
		}
	}
	for param := range sig.Params().Variables() {
		if s, ok := param.Type().(*types.Slice); ok && types.Identical(s.Elem(), types.Typ[types.Byte]) {
			fn.decodedFrom = param
		}
	}
	if len(entry.formats) > 0 || len(entry.calls) > 0 || len(entry.keeps) > 0 || len(entry.asserts) > 0 || len(entry.prints) > 0 || len(entry.encodes) > 0 || len(entry.runs) > 0 {
		fn.defect("it lists decodes with formats, calls, keeps, asserts, prints, encodes, or runs; decodes says all the function runs and keeps of what it decodes into")
	}
}

// decodeTarget is what a call decodes into: a pointer to a struct, written
// through, or a place that is assigned.
type decodeTarget struct {
	t       types.Type // the type decoded
	pointer ast.Expr   // a pointer to a struct, or nil
	place   ast.Expr   // a variable, a field, or an element, or nil
	why     string     // why the call is refused, or ""
}

// decodeTargetOf says what a call of a function with decodes decodes into.
func (v *fnVerifier) decodeTargetOf(call *ast.CallExpr, fn *funcInfo) (ast.Expr, ast.Expr, decodeTarget) {
	var into, data ast.Expr
	for _, b := range v.bindCall(call, fn.obj.Type().(*types.Signature)) {
		switch b.param {
		case fn.decoded:
			into = b.expr
		case fn.decodedFrom:
			data = b.expr
		}
	}
	if into == nil || (data == nil && fn.decodedFrom != nil) {
		return into, data, decodeTarget{why: "what it decodes and what it decodes into must be written out"}
	}
	t := v.info.TypeOf(into)
	if u, ok := ast.Unparen(into).(*ast.UnaryExpr); ok && u.Op == token.AND {
		inner := v.info.TypeOf(u.X)
		if _, isStruct := inner.Underlying().(*types.Struct); isStruct {
			return into, data, decodeTarget{t: inner, pointer: into}
		}
		switch x := ast.Unparen(u.X).(type) {
		case *ast.Ident, *ast.SelectorExpr:
			return into, data, decodeTarget{t: inner, place: u.X}
		case *ast.IndexExpr:
			// An element of a slice of bytes could be the data itself.
			if b, ok := inner.Underlying().(*types.Basic); ok && b.Info()&types.IsNumeric != 0 {
				return into, data, decodeTarget{why: fmt.Sprintf("%s is an element of %s, which is not supported; decode into a variable",
					types.ExprString(u.X), types.ExprString(x.X))}
			}
			return into, data, decodeTarget{t: inner, place: u.X}
		}
		return into, data, decodeTarget{why: "only the address of a variable, a field, or an element is supported; decode into a variable"}
	}
	if object, isPointer := pointee(t); isPointer {
		if _, isStruct := object.Underlying().(*types.Struct); isStruct {
			return into, data, decodeTarget{t: object, pointer: into}
		}
	}
	return into, data, decodeTarget{why: fmt.Sprintf("%s is of type %s; decode into &x for a variable x, or into a pointer to a struct",
		types.ExprString(into), types.TypeString(t, types.RelativeTo(v.pass.Pkg)))}
}

// checkDecodable refuses a call of a function with decodes whose target is
// not one vego follows, or of a type the walk refuses.
func (v *fnVerifier) checkDecodable(call *ast.CallExpr, fn *funcInfo) {
	if fn.decoded == nil {
		return
	}
	into, _, target := v.decodeTargetOf(call, fn)
	at := call.Pos()
	if into != nil {
		at = into.Pos()
	}
	if target.why == "" {
		target.why, _ = jsonPlainReason(v.pass.Pkg, v.pass.TypesSizes, target.t, strings.TrimPrefix(types.ExprString(into), "&"))
	}
	if target.why != "" {
		v.unsupported(at, fmt.Sprintf("%s decodes into %s, and %s", fn.obj.Name(), types.ExprString(into), target.why))
	}
}

// decodedLeaf reports whether encoding/json writes the leaf at a path of a
// value of type t, and the path of the field that holds it as a Modifies
// clause names it: an exported field, or one of an embedded struct, at any
// depth, and the whole of a leaf of the standard library or of a value
// that is not a struct.
func decodedLeaf(t types.Type, path string) (bool, string) {
	written, _ := decodedLeafIn(t, path)
	return written != "" || !strings.HasPrefix(path, "."), written
}

// decodedLeafIn is decodedLeaf, which also reports whether the leaf lies
// inside a leaf of the standard library that is a struct, as the location
// of a time.Time, which the decoder sets as that type's method does and
// which no obligation reaches into.
func decodedLeafIn(t types.Type, path string) (string, bool) {
	written := ""
	for path != "" {
		if jsonLeaf(t) != "" {
			_, isStruct := t.Underlying().(*types.Struct)
			return written, isStruct
		}
		st, ok := t.Underlying().(*types.Struct)
		if !ok || !strings.HasPrefix(path, ".") {
			return written, false
		}
		rest := path[1:]
		end := strings.IndexAny(rest, ".#")
		name := rest
		if end >= 0 {
			name = rest[:end]
		}
		path = rest[len(name):]
		var field *types.Var
		var tag string
		for i := range st.NumFields() {
			if st.Field(i).Name() == name {
				field, tag = st.Field(i), st.Tag(i)
			}
		}
		if field == nil {
			panic("vego: internal error: no field " + name + " in " + t.String())
		}
		parsed, _ := parseJSONTag(tag)
		embeddedStruct := false
		if field.Embedded() {
			ft := field.Type()
			if p, ok := types.Unalias(ft).(*types.Pointer); ok {
				ft = p.Elem()
			}
			_, embeddedStruct = ft.Underlying().(*types.Struct)
		}
		if parsed.skip || (!field.Exported() && !embeddedStruct) {
			return "", false
		}
		written += "." + name
		t = field.Type()
		if _, isPointer := types.Unalias(t).(*types.Pointer); isPointer {
			// The pointer itself is the leaf the decoder writes; what it
			// points to is new memory.
			return written, false
		}
	}
	return written, false
}

// decodeFactor bounds, for each byte of the data, what one allocation of
// the decoder may take: a string grows to three times the data (an invalid
// byte becomes U+FFFD) in a buffer that doubles, a slice holds an element
// for each two bytes in an array that doubles, and a map an entry for each
// six. It is at least 8, for the string.
func decodeFactor(t types.Type, sizes types.Sizes, seen map[types.Type]bool) int64 {
	if seen[t] || jsonLeaf(t) != "" {
		return 8
	}
	seen[t] = true
	most := int64(8)
	switch u := t.Underlying().(type) {
	case *types.Slice:
		most = max(most, sizes.Sizeof(u.Elem()), decodeFactor(u.Elem(), sizes, seen))
	case *types.Map:
		most = max(most, 2*(sizes.Sizeof(u.Key())+sizes.Sizeof(u.Elem())+16), decodeFactor(u.Elem(), sizes, seen))
	case *types.Pointer:
		most = max(most, decodeFactor(u.Elem(), sizes, seen))
	case *types.Struct:
		for field := range u.Fields() {
			most = max(most, decodeFactor(field.Type(), sizes, seen))
		}
	}
	return most
}

// callDecode verifies a call of a function with decodes as the contract
// made for it; see the comment at the top of the file.
func (v *fnVerifier) callDecode(call *ast.CallExpr, fn *funcInfo, st *state, guard []*logic.Term, reach func(), source *decodeSource) []value {
	_, data, target := v.decodeTargetOf(call, fn)
	byteSlice := types.Type(types.NewSlice(types.Typ[types.Byte]))
	if fn.decodedFrom != nil {
		byteSlice = fn.decodedFrom.Type()
	}
	if source != nil {
		// What the decoder reads, which no expression names.
		data = &ast.Ident{NamePos: call.Lparen, Name: "data"}
	}
	params := []*types.Var{types.NewParam(data.Pos(), v.pass.Pkg, "data", byteSlice)}
	results := []*types.Var{}
	var modifies []string
	if target.pointer != nil {
		params = append(params, types.NewParam(target.pointer.Pos(), v.pass.Pkg, "p", types.NewPointer(target.t)))
		leaves, _ := layoutOf(target.t)
		seen := map[string]bool{}
		for _, l := range leaves {
			if written, path := decodedLeaf(target.t, l.path); written && path != "" && !seen[path] {
				seen[path] = true
				modifies = append(modifies, "p"+path)
			}
		}
	} else {
		results = append(results, types.NewParam(target.place.Pos(), v.pass.Pkg, "r", target.t))
	}
	results = append(results, types.NewParam(call.Pos(), v.pass.Pkg, "err", types.Universe.Lookup("error").Type()))
	obj := types.NewFunc(call.Pos(), fn.obj.Pkg(), fn.obj.Name(), types.NewSignatureType(nil, nil, nil, types.NewTuple(params...), types.NewTuple(results...), false))
	view := newFuncInfo(obj)
	view.trust = fn.trust
	view.vouches[len(results)-1] = fn.vouches[0]
	factor := decodeFactor(target.t, v.pass.TypesSizes, map[types.Type]bool{})
	for _, text := range []string{
		fmt.Sprintf("%d * (|data| + 1) + 65536 <= MaxAlloc", factor),
		fmt.Sprintf("%d * (|data| + 1) <= MaxInt", factor),
	} {
		node, err := logic.ParseFormula(text)
		if err != nil {
			panic("vego: internal error: " + err.Error())
		}
		view.requires = append(view.requires, &clause{kind: "requires", text: text, node: node, pos: call.Pos(), res: v.pkgVerifier.plain})
	}
	if target.pointer != nil {
		node, _ := logic.ParseFormula("p != nil")
		view.requires = append(view.requires, &clause{kind: "requires", text: "p != nil", node: node, pos: call.Pos(), res: v.pkgVerifier.plain})
	}
	for _, text := range modifies {
		targets, err := logic.ParseTargets(text)
		if err != nil {
			panic("vego: internal error: " + err.Error())
		}
		view.modifies = append(view.modifies, newModTargets(targets, &clause{kind: "modifies", text: text, pos: call.Pos(), res: v.pkgVerifier.plain})...)
	}
	// The arguments, as the call evaluates them: the data, and the
	// pointer or what the place holds now.
	args := map[*types.Var]value{}
	if source == nil {
		args[params[0]] = v.eval(data, st, guard)
	}
	var old value
	if target.pointer != nil {
		// Go converts it to any for the call, which is verified without
		// that interface value.
		inner := ast.Unparen(target.pointer)
		v.converting[inner]++
		args[params[1]] = v.eval(target.pointer, st, guard)
		v.converting[inner]--
	} else {
		old = v.eval(target.place, st, guard)
	}
	reach()
	if source != nil {
		// What the decoder read from the reader, before anything is
		// decoded.
		args[params[0]] = source.read()
	}
	shown := strings.TrimPrefix(types.ExprString(call.Args[len(call.Args)-1]), "&")
	// What the decoder would reuse must be nil: a slice with no capacity,
	// a nil map, a nil pointer.
	v.checkNilTargets(st, guard, call, target, args, params, old, shown)
	// The made contract takes the data, and the pointer it writes through.
	made := &ast.CallExpr{Fun: call.Fun, Lparen: call.Lparen, Args: []ast.Expr{data}, Rparen: call.Rparen}
	if target.pointer != nil {
		made.Args = append(made.Args, target.pointer)
	}
	out := v.invoke(made, view, args, st, guard)
	if target.place != nil {
		lv := v.lvalue(target.place, st, guard)
		v.store(lv, out[0], st)
		return out[1:]
	}
	return out
}

// checkNilTargets proves that every slice, map, and pointer that the
// decoder writes in the value decoded into is nil, a slice of no capacity:
// otherwise it appends into the array, keeps the map's entries, or decodes
// through the pointer, into memory the caller may hold.
func (v *fnVerifier) checkNilTargets(st *state, guard []*logic.Term, call *ast.CallExpr, target decodeTarget, args map[*types.Var]value, params []*types.Var, old value, shown string) {
	leaves, _ := layoutOf(target.t)
	val := old
	if target.pointer != nil {
		v.check(st, guard, logic.Ne(args[params[1]][0], logic.RefLit(0)), call.Pos(), "%s, which Unmarshal decodes into, may be nil", shown)
		v.quietly(func() { val = v.pointedIn(st, st.mem, target.t, args[params[1]]) })
	}
	for i, l := range leaves {
		written, _ := decodedLeaf(target.t, l.path)
		if _, inside := decodedLeafIn(target.t, l.path); !written || inside {
			continue
		}
		var nilled *logic.Term
		switch {
		case l.part == partCap:
			nilled = logic.Eq(val[i], logic.IntLit(0))
		case l.part == partPtr:
			nilled = logic.Eq(val[i], logic.RefLit(0))
		case l.part == partValue && l.sort == logic.Ref:
			if _, isMap := l.typ.Underlying().(*types.Map); isMap {
				nilled = logic.Eq(val[i], logic.RefLit(0))
			}
		}
		if nilled == nil {
			continue
		}
		path := strings.SplitN(l.path, "#", 2)[0]
		v.check(st, guard, nilled, call.Pos(), "Unmarshal may decode into memory that %s%s refers to, which the caller may hold: it appends into a slice's array, "+
			"keeps a map's entries, and decodes through a pointer it finds; decode into a value whose slices, maps, and pointers are nil, as var x T declares it", shown, path)
	}
}

// The in-place decoder (F29, D3). json.NewDecoder(io.LimitReader(r,
// n)).Decode(&x), written as one expression, makes a decoder over a reader
// that yields at most n bytes of r, and that nothing else holds. In every
// build, Decode reads from it into a buffer until it holds the first
// value (at most n bytes, the buffer at most twice that and a little
// more), and decodes that value as Unmarshal does; what it did not read
// stays in r. So the call is verified as r's own Read of a new slice,
// which gives what the read may change of r, followed by the decoding of
// Unmarshal from at most n bytes. Its error may be one r's Read returned,
// so it is not vouched for. Any other use of a Decoder or of NewDecoder is
// refused: a decoder over a reader without a limit reads without one, and
// one from elsewhere may hold what it read before.

// jsonDecodeKey and jsonNewDecoderKey are the functions of the route.
const (
	jsonDecodeKey     = "(*encoding/json.Decoder).Decode"
	jsonNewDecoderKey = "encoding/json.NewDecoder"
)

// decodeSource is what the in-place decoder reads: read applies the
// reader's own Read and returns the bytes read.
type decodeSource struct {
	read func() value
}

// decoderInPlace returns, for json.NewDecoder(io.LimitReader(r,
// n)).Decode(v) written as one expression, the calls of NewDecoder and of
// LimitReader, and otherwise nil. With limited false, the expression is
// json.NewDecoder(r).Decode(v), whose reader has no limit.
func (pv *pkgVerifier) decoderInPlace(call *ast.CallExpr) (made, limit *ast.CallExpr, limited bool) {
	sel, ok := ast.Unparen(call.Fun).(*ast.SelectorExpr)
	if !ok || sel.Sel.Name != "Decode" {
		return nil, nil, false
	}
	if decode := typeutil.StaticCallee(pv.info, call); decode == nil || decode.FullName() != jsonDecodeKey {
		return nil, nil, false
	}
	made, ok = ast.Unparen(sel.X).(*ast.CallExpr)
	if !ok || len(made.Args) != 1 {
		return nil, nil, false
	}
	if newDecoder := typeutil.StaticCallee(pv.info, made); newDecoder == nil || newDecoder.FullName() != jsonNewDecoderKey {
		return nil, nil, false
	}
	limit, ok = ast.Unparen(made.Args[0]).(*ast.CallExpr)
	if ok && len(limit.Args) == 2 {
		if limiter := typeutil.StaticCallee(pv.info, limit); limiter != nil && limiter.FullName() == "io.LimitReader" {
			return made, limit, true
		}
	}
	return made, nil, false
}

// jsonDecoderUse is the message for any other use of NewDecoder or of a
// Decoder, or "" for a function that is neither.
func jsonDecoderUse(callee *types.Func) string {
	switch callee.FullName() {
	case jsonNewDecoderKey:
		return "json.NewDecoder keeps r in the decoder it returns; write json.NewDecoder(io.LimitReader(r, n)).Decode(&x) in one expression, " +
			"since a decoder held in a variable is not supported yet"
	case jsonDecodeKey:
		return "Decode is verified only on a new decoder over a limited reader, written as json.NewDecoder(io.LimitReader(r, n)).Decode(&x) in one expression: " +
			"a Decoder made elsewhere may hold what it read before"
	}
	return ""
}

// callDecoder verifies json.NewDecoder(io.LimitReader(r, n)).Decode(v)
// written as one expression; see decoderInPlace.
func (v *fnVerifier) callDecoder(call, limit *ast.CallExpr, st *state, guard []*logic.Term) []value {
	decode := typeutil.StaticCallee(v.info, call)
	fn := v.contractOf(decode)
	if fn == nil || fn.decoded == nil {
		v.unsupported(call.Pos(), "json.NewDecoder(io.LimitReader(r, n)).Decode(&x) needs the entry of (*encoding/json.Decoder).Decode that comes with vego, which lists decodes")
	}
	fn = v.usable(call.Pos(), fn, decode.Name(), st, guard, true)
	v.noteUse(fn, call.Pos())
	v.checkDecodable(call, fn)
	r, n := limit.Args[0], limit.Args[1]
	rt := v.info.TypeOf(r)
	obj, _, _ := types.LookupFieldOrMethod(rt, true, v.pass.Pkg, "Read")
	method, _ := obj.(*types.Func)
	if method == nil {
		v.unsupported(r.Pos(), fmt.Sprintf("%s has no method Read", types.ExprString(r)))
	}
	var read *funcInfo
	if isIface(rt) {
		read = v.methodContract(method)
	} else {
		read = v.contractOf(method)
	}
	if read == nil {
		v.unsupported(r.Pos(), fmt.Sprintf("the decoder calls %s.Read, which has no contract", types.ExprString(r)))
	}
	read = v.usable(call.Pos(), read, types.ExprString(r)+".Read", st, guard, true)
	if isIface(rt) {
		v.ifaceStatesOf(rt)
	}
	u := v.unit
	operands := u.pushCeiling()
	made := unitCall{name: decode.Name(), pos: call.Pos()}
	// The reader is evaluated as it is: Go converts it to io.Reader for
	// LimitReader, and the call is verified without that interface value.
	inner := ast.Unparen(r)
	v.converting[inner]++
	reader := v.eval(r, st, guard)
	v.converting[inner]--
	most := v.eval(n, st, guard)
	// What may be read must be something that can be decoded: the bound
	// of Unmarshal at n.
	if _, _, target := v.decodeTargetOf(call, fn); target.why == "" {
		factor := decodeFactor(target.t, v.pass.TypesSizes, map[types.Type]bool{})
		read := logic.Add(logic.Ite(logic.Lt(most[0], logic.IntLit(0)), logic.IntLit(0), most[0]), logic.IntLit(1))
		maxInt := new(big.Int).Lsh(big.NewInt(1), uint(8*v.pass.TypesSizes.Sizeof(types.Typ[types.Int])-1))
		maxInt.Sub(maxInt, big.NewInt(1))
		fits := logic.And(
			logic.Le(logic.Add(logic.Mul(logic.IntLit(factor), read), logic.IntLit(1<<16)), logic.BigLit(v.maxAlloc())),
			logic.Le(logic.Mul(logic.IntLit(factor), read), logic.BigLit(maxInt)))
		limit := new(big.Int).Sub(v.maxAlloc(), big.NewInt(1<<16))
		limit.Div(limit, big.NewInt(factor))
		if byInt := new(big.Int).Div(maxInt, big.NewInt(factor)); byInt.Cmp(limit) < 0 {
			limit = byInt
		}
		limit.Sub(limit, big.NewInt(1))
		v.check(st, guard, fits, call.Pos(), "the decoder may read %s bytes, more than can be decoded; it holds when %s <= %s",
			types.ExprString(n), types.ExprString(n), limit)
	}
	source := &decodeSource{read: func() value {
		if isIface(rt) {
			// Read through a nil reader panics.
			v.check(st, guard, logic.Ne(reader[0], logic.RefLit(0)), call.Pos(), "the reader %s handed to io.LimitReader may be nil", types.ExprString(r))
		}
		// The reader's own Read of a new slice, which gives what the
		// reads may change of r.
		readSig := read.obj.Type().(*types.Signature)
		p := readSig.Params().At(0)
		// The decoder reads into a buffer with room left, of at least 512
		// bytes.
		room := v.fresh("buffer", logic.IntSeq)
		st.assume(logic.Le(logic.IntLit(1), logic.Len(room)))
		buf := v.copiedBytes(st, room, p.Type())
		readArgs := map[*types.Var]value{p: buf}
		if read.receiver != nil {
			readArgs[read.receiver] = reader
		} else if recv := readSig.Recv(); recv != nil {
			readArgs[recv] = reader
		}
		shown := &ast.Ident{NamePos: call.Lparen, Name: "buffer"}
		readCall := &ast.CallExpr{Fun: &ast.SelectorExpr{X: r, Sel: &ast.Ident{NamePos: call.Lparen, Name: "Read"}}, Lparen: call.Lparen, Args: []ast.Expr{shown}, Rparen: call.Rparen}
		if read.trust != nil {
			v.noteUse(read, call.Pos())
		}
		v.invoke(readCall, read, readArgs, st, guard)
		// What was read: at most n bytes, none for a limit below one.
		text := v.fresh("read", logic.IntSeq)
		st.assume(logic.Implies(logic.And(guard...), logic.Le(logic.Len(text), logic.Ite(logic.Lt(most[0], logic.IntLit(0)), logic.IntLit(0), most[0]))))
		return v.copiedBytes(st, text, types.NewSlice(types.Typ[types.Byte]))
	}}
	results := v.callDecode(call, fn, st, guard, func() { u.reach(operands) }, source)
	u.calls = append(u.calls, made)
	u.event()
	return results
}
