package vego

import (
	"go/token"
	"go/types"
	"slices"
	"strings"
	"sync"

	"gopkg.in/yaml.v3"
)

// stateDecl is a state that a type of another module owns, such as whether
// the calling goroutine holds a sync.Mutex. It is a boolean that no Go code
// can read or write and only contracts speak of. In the logic it is one more
// leaf of the struct, after its fields, in a region of its own keyed by the
// underlying struct type and the name of the state, so that it is created,
// copied, and forgotten with the struct and needs no rule of its own in the
// translation. Its value in the zero value of the type is False.
type stateDecl struct {
	name   string
	reason string
	line   int
	// typeLine is the line of the type the state is declared for.
	typeLine int
}

// addStates reads the state section of a file: a mapping from a type, as
// in sync.Mutex, to the names of its states, each with a reason.
func (f *trustFile) addStates(node *yaml.Node) {
	if node.Kind != yaml.MappingNode {
		f.problem(node.Line, "state must map types to their states")
		return
	}
	for i := 0; i+1 < len(node.Content); i += 2 {
		typeName, body := node.Content[i], node.Content[i+1]
		if _, _, ok := splitTypeName(typeName.Value); !ok {
			f.problem(typeName.Line, "state: %q is not a type named by its package, as in sync.Mutex", typeName.Value)
			continue
		}
		if body.Kind != yaml.MappingNode || len(body.Content) == 0 {
			f.problem(body.Line, "the state of %s must map the names of its states to a reason", typeName.Value)
			continue
		}
		for j := 0; j+1 < len(body.Content); j += 2 {
			name, decl := body.Content[j], body.Content[j+1]
			// A name that means something of its own in formulas cannot
			// name a state.
			reserved := slices.Contains(reservedStateNames, name.Value)
			if !token.IsIdentifier(name.Value) || reserved {
				f.problem(name.Line, "%q cannot name a state: it must be an identifier that the formula language does not use", name.Value)
				continue
			}
			reason := ""
			if decl.Kind == yaml.MappingNode {
				for k := 0; k+1 < len(decl.Content); k += 2 {
					switch field, value := decl.Content[k], decl.Content[k+1]; field.Value {
					case "reason":
						reason = strings.TrimSpace(value.Value)
					default:
						f.problem(field.Line, "unknown field %q in the state %s of %s; expected reason", field.Value, name.Value, typeName.Value)
					}
				}
			}
			if reason == "" {
				f.problem(name.Line, "the state %s of %s needs a reason saying what it means and why it is False in the zero value",
					name.Value, typeName.Value)
				continue
			}
			f.states[typeName.Value] = append(f.states[typeName.Value], stateDecl{name: name.Value, reason: reason, line: name.Line, typeLine: typeName.Line})
		}
	}
}

// splitTypeName splits a type named by its package, as in sync.Mutex or
// "example.com/x".T, into the path of the package and the name.
func splitTypeName(key string) (pkg, name string, ok bool) {
	dot := strings.LastIndex(key, ".")
	if dot <= 0 || dot == len(key)-1 || !token.IsIdentifier(key[dot+1:]) {
		return "", "", false
	}
	return strings.Trim(key[:dot], `"`), key[dot+1:], true
}

// shippedStates holds the states that the shipped files declare, by the
// path of the package and the name of the type.
var shippedStates = sync.OnceValue(func() map[string]map[string][]stateDecl {
	byPackage := map[string]map[string][]stateDecl{}
	for _, file := range shippedContracts() {
		for key, decls := range file.states {
			pkg, name, _ := splitTypeName(key)
			if byPackage[pkg] == nil {
				byPackage[pkg] = map[string][]stateDecl{}
			}
			byPackage[pkg][name] = append(byPackage[pkg][name], decls...)
		}
	}
	return byPackage
})

// statesOf returns the states of a struct type: those declared for a type
// whose underlying type is identical to it. They belong to the memory and
// not to the name, so a type defined from sync.Mutex, which can be
// converted to and from it, has the same states. A struct identical to the
// underlying type of a declared type has fields declared in the package of
// that type, which is where the declaration is looked up. That finds every
// such struct only when the declared type has an unexported field, which
// TestStateDeclarations requires of every declaration.
func statesOf(u *types.Struct) []stateDecl {
	var home *types.Package
	for field := range u.Fields() {
		if field.Pkg() != nil {
			home = field.Pkg()
			break
		}
	}
	if home == nil {
		return nil
	}
	declared := shippedStates()[home.Path()]
	if declared == nil {
		return nil
	}
	plain := untagged(u)
	for name, decls := range declared {
		obj, ok := home.Scope().Lookup(name).(*types.TypeName)
		if ok && types.Identical(plain, untagged(obj.Type().Underlying())) {
			return decls
		}
	}
	return nil
}
