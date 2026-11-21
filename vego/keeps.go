package vego

import (
	"go/types"
	"slices"
	"strings"

	"gopkg.in/yaml.v3"
)

// A trusted function may keep code it is given: a constructor that wraps a
// reader keeps the reader in what it returns, and a registry method keeps a
// handler in the registry it is called on. Under keeps, an entry names each
// parameter whose code the function keeps and its destinations: results,
// or other parameters whose memory it writes. The claim is about what the
// function does, for whatever code the parameter holds (for a function value
// of a type with a contract, or an interface value whose methods all have
// contracts, only for values that meet them):
//
//   - while the call lasts, it runs none of that code, unless its runs lists
//     the parameter too;
//   - when it returns, it holds the code only in memory that the
//     destinations reach;
//   - it has started or registered nothing that runs the code later: no
//     goroutine, timer, finalizer or cleanup, callback given to another
//     package such as context.AfterFunc, or package-level variable.
//
// What follows: a later run of the code is made by code that holds a
// reference to the kept value, which it can reach only through a
// destination or a copy of one. By Go's types that is a call handed a value
// that holdsCode counts, so a trusted function must list it under runs or
// keeps, whose claim carries the later run (it returns, runs the code only
// on its goroutine and before it returns, and keeps what the code writes
// and is given inside its entry), or a call through a value, which is
// always counted as one. Stratification sees the later run at those calls,
// provided a destination of code that verified code may have made is
// itself counted by holdsCallable, which readKeeps demands.

// addKeeps reads the keeps of an entry: a mapping from a parameter to the
// list of its destinations.
func (f *trustFile) addKeeps(entry *trustEntry, node *yaml.Node) {
	if node.Kind != yaml.MappingNode {
		f.problem(node.Line, "keeps of %s must map a parameter to the results and parameters it is kept in, as in r: [result]", entry.key)
		return
	}
	for i := 0; i+1 < len(node.Content); i += 2 {
		key, body := node.Content[i], node.Content[i+1]
		if key.Kind != yaml.ScalarNode {
			f.problem(key.Line, "keeps of %s must map a parameter to the results and parameters it is kept in, as in r: [result]", entry.key)
			continue
		}
		kept := trustKeep{name: key.Value, line: key.Line, col: key.Column}
		if body.Kind != yaml.SequenceNode {
			f.problem(body.Line, "keeps of %s: %s must map to a list of results and parameters, as in [result]", entry.key, key.Value)
			continue
		}
		for _, item := range body.Content {
			if item.Kind != yaml.ScalarNode {
				f.problem(item.Line, "keeps of %s: %s must map to a list of names of results and parameters", entry.key, key.Value)
				continue
			}
			kept.dests = append(kept.dests, trustFormula{text: item.Value, line: item.Line, col: item.Column})
		}
		entry.keeps = append(entry.keeps, kept)
	}
}

// readKeeps reads what a trusted function keeps into fn, recording as
// defects what the claim cannot be true of or would leave unseen.
func (pv *pkgVerifier) readKeeps(fn *funcInfo, entry *trustEntry) {
	for _, item := range entry.keeps {
		param, ok := fn.paramNames[item.name]
		switch {
		case !ok:
			fn.defect("its keeps %q: %s is not a parameter", item.name, item.name)
			continue
		case !holdsCode(param.Type(), map[types.Type]bool{}):
			fn.defect("its keeps lists %s, whose type %s can hold no error, interface value, function value, channel, or unsafe.Pointer to keep",
				item.name, param.Type())
			continue
		case fn.calls.get(param) != nil:
			fn.defect("its keeps lists %s, which its calls gives a contract; what is handed over there runs only while the call lasts, "+
				"and a function literal handed over may assign the variables of its caller", item.name)
			continue
		case param == fn.formatted:
			fn.defect("its keeps lists %s, which its formats lists; formats claims that the function keeps none of the values", item.name)
			continue
		case len(item.dests) == 0:
			fn.defect("its keeps lists %s with no destination; name the results or parameters in which the function keeps it, "+
				"and if it keeps it anywhere else, such as in a package-level variable, the entry cannot be true", item.name)
			continue
		}
		callable := holdsCallable(pv, param.Type(), map[types.Type]bool{})
		var dests []string
		for _, dest := range item.dests {
			var t types.Type
			if index, isResult := fn.resultNames[dest.text]; isResult {
				t = fn.results[index].Type()
			} else if target, isParam := fn.paramNames[dest.text]; isParam {
				t = target.Type()
				switch {
				case target == param:
					fn.defect("its keeps lists %s as kept in itself; name the results or other parameters in which the function keeps it", item.name)
					continue
				case !slices.ContainsFunc(fn.modifies, func(m *modTarget) bool { return m.name == dest.text }):
					fn.defect("its keeps lists %s as kept in %s, which its modifies does not list; keeping a value in memory that a parameter "+
						"reaches writes that memory", item.name, dest.text)
					continue
				case !slices.ContainsFunc(fn.modifies, func(m *modTarget) bool {
					covered := coveredType(fn, m)
					return m.name == dest.text && covered != nil && holdsCode(covered, map[types.Type]bool{}) &&
						(!callable || holdsCallable(pv, covered, map[types.Type]bool{}))
				}):
					// Keeping the code writes memory that holds it, which a
					// modifies over other memory under the parameter claims
					// to be unchanged.
					fn.defect("its keeps lists %s as kept in %s, but nothing its modifies lists under %s can hold it", item.name, dest.text, dest.text)
					continue
				}
			} else {
				fn.defect("its keeps lists %s as kept in %s, which is not a result or a parameter", item.name, dest.text)
				continue
			}
			switch {
			case slices.Contains(dests, dest.text):
				fn.defect("its keeps lists %s as kept in %s twice", item.name, dest.text)
			case !holdsCode(t, map[types.Type]bool{}):
				fn.defect("its keeps lists %s as kept in %s, whose type %s can hold no code", item.name, dest.text, t)
			case callable && !holdsCallable(pv, t, map[types.Type]bool{}):
				// A later call handed the destination would not count as
				// one that may call through a value, though it would run
				// code that verified code may have made.
				fn.defect("its keeps lists %s as kept in %s, whose type %s can hold no function value and no value of an interface whose methods "+
					"all have contracts. But %s can hold %s, and a call handed %s would run that code without being counted as one that may "+
					"call through a value", item.name, dest.text, t, item.name, pv.callableIn(param.Type(), map[types.Type]bool{}), dest.text)
			default:
				dests = append(dests, dest.text)
			}
		}
		if len(dests) > 0 {
			fn.keeps.set(param, dests)
		}
	}
}

// keepsDescribed describes what an entry keeps for the trust report, as in
// "r in result; h in reg".
func keepsDescribed(entry *trustEntry) []string {
	var described []string
	for _, item := range entry.keeps {
		var dests []string
		for _, dest := range item.dests {
			dests = append(dests, dest.text)
		}
		described = append(described, item.name+" in "+strings.Join(dests, " and "))
	}
	return described
}
