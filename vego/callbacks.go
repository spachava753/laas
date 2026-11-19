package vego

import (
	"go/types"
	"slices"
	"strings"

	"github.com/spachava753/laas/vego/internal/logic"
)

// A trusted function may take a function and call it while it runs, as
// sort.Search and strings.IndexFunc do. Its entry can give such a parameter
// a contract under calls, which names the parameters of the function type
// and says what holds whenever the trusted function calls it:
//
//	sort.Search:
//	  runs: [f]
//	  calls:
//	    f(i):
//	      requires: ["0 <= i < n"]
//
// The parameter must be listed under runs as well: the entry claims what
// runs claims, that the function calls f only before it returns, on the
// goroutine that called it, and keeps it nowhere, and also that it calls f
// only with arguments that meet the requires of calls, in the state at that
// call. The rest of the contract has to hold for every function that meets
// them, returns, and writes nothing that the modifies of the entry covers.

// callback is the contract a trusted entry gives one function parameter.
type callback struct {
	// param is the parameter of the trusted function, and sig its function
	// type.
	param *types.Var
	sig   *types.Signature
	// params are the parameters of the function type, named as the entry
	// names them.
	params []*types.Var
	// fn resolves the requires: it names the parameters of the function
	// type and those of the trusted function.
	fn       *funcInfo
	requires []*clause
}

// callWords are the names that a formula reads as something else when
// they are applied, as in is(err, target).
var callWords = []string{"is", "has", "old", "fresh", "within", "len"}

// trustedCall reads one entry under calls of a trusted contract into fn,
// or records why it cannot be used.
func (pv *pkgVerifier) trustedCall(fn *funcInfo, item trustCall) {
	param, ok := fn.paramNames[item.name]
	if !ok {
		fn.defect("its calls %s(...): %s is not a parameter", item.name, item.name)
		return
	}
	sig, isFunc := param.Type().Underlying().(*types.Signature)
	switch {
	case !isFunc:
		fn.defect("its calls lists %s, whose type %s is not a function type", item.name, param.Type())
		return
	case !fn.runs[param]:
		fn.defect("its calls gives %s a contract, so its runs must list %s too: calls claims everything runs does", item.name, item.name)
		return
	case fn.calls[param] != nil:
		fn.defect("its calls lists %s twice", item.name)
		return
	case pv.valueContract(param.Type()) != nil:
		fn.defect("its calls gives %s a contract, but its type %s has a contract of its own", item.name, param.Type())
		return
	case sig.Variadic() || sig.TypeParams() != nil:
		fn.defect("its calls lists %s, whose type %s is variadic or generic, which is not supported yet", item.name, param.Type())
		return
	case slices.Contains(callWords, item.name):
		fn.defect("its calls lists %s, which a formula reads as a word of its own when it is applied", item.name)
		return
	case len(item.params) != sig.Params().Len():
		fn.defect("its calls names %d parameters for %s, whose type %s has %d", len(item.params), item.name, param.Type(), sig.Params().Len())
		return
	}
	pos := pv.trustPos(fn.trust.file, item.line, item.col)
	// The requires name the parameters of the function type, and those of
	// the trusted function, whose values are those of the call.
	cb := &callback{param: param, sig: sig}
	cb.fn = &funcInfo{
		obj: fn.obj, trust: fn.trust, paramNames: map[string]*types.Var{}, resultNames: map[string]int{},
		runs: map[*types.Var]bool{}, vouches: map[int]bool{}, calls: map[*types.Var]*callback{},
	}
	for name, p := range fn.paramNames {
		cb.fn.paramNames[name] = p
	}
	for i, name := range item.params {
		// A formula must read the name as a name, and not as a word of its
		// own such as True, or as a result, result1, result2, ...
		node, err := logic.ParseFormula(name)
		rest, numbered := strings.CutPrefix(name, "result")
		numbered = numbered && strings.Trim(rest, "0123456789") == ""
		readAsName := err == nil && node.Kind == logic.NIdent && node.Name == name && !numbered
		switch {
		case slices.Contains(item.params[:i], name):
			fn.defect("its calls names the parameter %s of %s twice", name, item.name)
			return
		case fn.paramNames[name] != nil:
			fn.defect("its calls names a parameter of %s %s, which is a parameter of %s already", item.name, name, fn.obj.Name())
			return
		case !readAsName || slices.Contains(callWords, name):
			fn.defect("its calls names a parameter of %s %s, which means something else in a formula", item.name, name)
			return
		}
		if _, isResult := fn.resultNames[name]; isResult {
			fn.defect("its calls names a parameter of %s %s, which is a result of %s", item.name, name, fn.obj.Name())
			return
		}
		named := types.NewVar(pos, fn.obj.Pkg(), name, sig.Params().At(i).Type())
		cb.params = append(cb.params, named)
		cb.fn.params = append(cb.fn.params, named)
		cb.fn.paramNames[name] = named
	}
	cb.fn.params = append(cb.fn.params, fn.params...)
	// What the trusted function passes to the callback, and what it gets
	// back, must be values vego models. Code there would be code handed on
	// between two functions vego does not see.
	for _, tuple := range []*types.Tuple{sig.Params(), sig.Results()} {
		for variable := range tuple.Variables() {
			if _, modelled := layoutOf(variable.Type()); !modelled {
				fn.defect("its calls lists %s, whose type %s takes or returns a %s, which is not supported", item.name, param.Type(), variable.Type())
				return
			}
			if holdsCode(variable.Type(), map[types.Type]bool{}) {
				fn.defect("its calls lists %s, whose type %s takes or returns a %s, which can hold code; that is not supported yet",
					item.name, param.Type(), variable.Type())
				return
			}
		}
	}
	for _, formula := range item.requires {
		cb.requires = append(cb.requires, &clause{
			kind: "requires", text: formula.text, node: formula.node, res: pv.plain,
			pos: pv.trustPos(fn.trust.file, formula.line, formula.col),
		})
	}
	cb.fn.requires = cb.requires
	fn.calls[param] = cb
}

// callRequires resolves what holds when a trusted function calls a
// function parameter: in memory as it is at that call, with the arguments
// of that call for the parameters of the function type and those of the
// call of the trusted function for its own.
func (v *fnVerifier) callRequires(cb *callback, given []value, args map[*types.Var]value, st *state) []*logic.Term {
	all := map[*types.Var]value{}
	for param, val := range args {
		all[param] = val
	}
	for i, param := range cb.params {
		all[param] = given[i]
	}
	env := &specEnv{v: v, sink: st, fn: cb.fn, args: all, now: st.mem}
	var facts []*logic.Term
	for _, c := range cb.requires {
		facts = append(facts, v.formula(c, c.node, env))
	}
	return facts
}
