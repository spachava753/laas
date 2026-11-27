package vego

import (
	"fmt"
	"go/ast"
	"go/types"
	"strings"
)

// A census (-vego.census) looks at every function of a module as if it
// carried the weakest contract and records what stops the verifier, without
// proving anything; see census.go's second half and docs/verification.md.
// What stops it is a refusal, and every place that refuses names the class
// of what it refuses, so that the census can count functions by the Go that
// stops them and not by the words of a message.

// refusal is the class of a refusal: a key of refusalClasses, optionally
// followed by "|" and a detail, such as the callee or the type that was
// refused. Only the census reads it; a diagnostic shows the message alone.
type refusal string

// class returns the class without its detail.
func (r refusal) class() string {
	class, _, _ := strings.Cut(string(r), "|")
	return class
}

// withDetail adds a detail to a class.
func withDetail(class refusal, detail string) refusal {
	return refusal(string(class) + "|" + detail)
}

// The classes. Each is named group:kind; the census reports both levels.
// The comment of each, in refusalClasses, says what Go it is and where the
// roadmap plans it.
const (
	rNoEntryStd            refusal = "no-entry:std"
	rNoEntryModule         refusal = "no-entry:module"
	rNoEntryOther          refusal = "no-entry:other"
	rEntryImpossible       refusal = "no-entry:impossible"
	rTypeUintptr           refusal = "type:uintptr"
	rTypeComplex           refusal = "type:complex"
	rTypeUnsafe            refusal = "type:unsafe-pointer"
	rTypeOther             refusal = "type:other"
	rTypeIface             refusal = "type:iface-literal"
	rTypeArray             refusal = "type:array"
	rTypeArrayStruct       refusal = "type:array-in-struct"
	rTypeArrayElem         refusal = "type:array-elem"
	rTypeMapKey            refusal = "type:map-key"
	rPointerTo             refusal = "pointer:to-non-struct"
	rChannel               refusal = "channel:use"
	rGoroutine             refusal = "goroutine:go"
	rSelect                refusal = "select:statement"
	rIterator              refusal = "generic:iterator"
	rGenericDeclared       refusal = "generic:declared"
	rGenericCalled         refusal = "generic:called"
	rGenericMethod         refusal = "generic:method-call"
	rGenericHanded         refusal = "generic:as-value"
	rGenericTypeArgs       refusal = "generic:type-args"
	rGenericTypeParam      refusal = "generic:type-param"
	rAddrField             refusal = "address-of:field"
	rAddrElement           refusal = "address-of:element"
	rAddrGlobal            refusal = "address-of:global"
	rAddrOther             refusal = "address-of:other"
	rIfaceNoContract       refusal = "iface-method:no-contract"
	rIfaceForm             refusal = "iface-method:form"
	rConvOptional          refusal = "convert:iface-optional"
	rConvErrToIface        refusal = "convert:error-to-iface"
	rConvIfaceType         refusal = "convert:iface-unsupported"
	rConvIfaceArray        refusal = "convert:iface-array"
	rConvWrapsWriter       refusal = "convert:iface-wraps-writer"
	rConvBuffer            refusal = "convert:iface-buffer"
	rConvOwns              refusal = "convert:iface-owns"
	rConvStates            refusal = "convert:iface-states"
	rConvNoContract        refusal = "convert:iface-no-contract"
	rConvForeignImpl       refusal = "convert:iface-foreign-impl"
	rConvByContract        refusal = "convert:iface-by-contract"
	rConvToError           refusal = "convert:to-error"
	rConvValue             refusal = "convert:value"
	rConvMultiValue        refusal = "convert:multi-value"
	rConvUnplaced          refusal = "convert:unplaced"
	rErrUnknown            refusal = "error:unknown-origin"
	rErrCompare            refusal = "error:compare"
	rErrSentinel           refusal = "error:sentinel"
	rDynLocalType          refusal = "dyntype:local-type"
	rDynAssert             refusal = "dyntype:assert"
	rDynSwitch             refusal = "dyntype:switch"
	rDynCompare            refusal = "dyntype:compare"
	rDynAs                 refusal = "dyntype:errors-as"
	rLitValue              refusal = "func-literal:value"
	rLitCaptures           refusal = "func-literal:captures"
	rLitRecursion          refusal = "func-literal:recursion"
	rLitSignature          refusal = "func-literal:signature"
	rClosure               refusal = "closure:recursive"
	rFuncNoContract        refusal = "func-value:no-contract"
	rFuncMethodValue       refusal = "func-value:method-value"
	rFuncMethodExpr        refusal = "func-value:method-expr"
	rFuncMadeFrom          refusal = "func-value:made-from"
	rFuncTrusted           refusal = "func-value:trusted-callee"
	rFuncCallsValues       refusal = "func-value:calls-values"
	rHandUnknownCode       refusal = "handover:unknown-code"
	rHandNoContract        refusal = "handover:no-contract"
	rHandEntry             refusal = "handover:entry"
	rHandFootprint         refusal = "handover:footprint"
	rHandApart             refusal = "handover:apart"
	rSortSlice             refusal = "handover:sort"
	rDeferLoop             refusal = "defer:in-loop"
	rDeferForm             refusal = "defer:form"
	rRecover               refusal = "recover:call"
	rExitContext           refusal = "exit:context"
	rGlobalAssign          refusal = "global:assign"
	rGlobalRead            refusal = "global:read"
	rGlobalType            refusal = "global:type"
	rGlobalUnreliable      refusal = "global:unreliable"
	rGlobalFollowed        refusal = "global:followed-code"
	rGlobalInit            refusal = "global:initialiser"
	rGoto                  refusal = "stmt:goto"
	rFallthrough           refusal = "stmt:fallthrough"
	rStmtExpr              refusal = "stmt:expression"
	rStmtOther             refusal = "stmt:other"
	rSwitchArray           refusal = "stmt:switch-array"
	rSwitchIface           refusal = "stmt:switch-iface-case"
	rRangeForm             refusal = "stmt:range-form"
	rRangeOther            refusal = "stmt:range-other"
	rOpBits                refusal = "operator:bits"
	rOpOther               refusal = "operator:other"
	rOpPointer             refusal = "operator:pointer"
	rOpNil                 refusal = "operator:nil-compare"
	rIndex                 refusal = "expr:index"
	rLiteral               refusal = "expr:literal"
	rExprOther             refusal = "expr:other"
	rExprValueShape        refusal = "expr:value-shape"
	rConstant              refusal = "expr:constant"
	rAppendExpr            refusal = "append:in-expression"
	rAppendCallTarget      refusal = "append:call-in-target"
	rCopyElements          refusal = "copy:elements"
	rCopyTarget            refusal = "copy:in-target"
	rCopyValue             refusal = "copy:value-with-state"
	rBuiltin               refusal = "call:builtin"
	rCallForm              refusal = "call:form"
	rCallMultiArgs         refusal = "call:multi-value-args"
	rCallInitOnly          refusal = "call:initialiser-only"
	rAssignTarget          refusal = "assign:target"
	rAssignInPlace         refusal = "assign:in-place"
	rAssignMulti           refusal = "assign:multi-value"
	rFormatCode            refusal = "format:runs-code"
	rFormatPack            refusal = "format:slice-pack"
	rFormatPrints          refusal = "format:prints"
	rJSON                  refusal = "json:form"
	rJSONEncode            refusal = "json:encode"
	rJSONDecode            refusal = "json:decode"
	rOwnsUntrusted         refusal = "owns:untrusted"
	rScopedHidden          refusal = "scoped:hidden"
	rScopedWritten         refusal = "scoped:written"
	rSizeTooLarge          refusal = "size:too-large"
	rCallsAnnotation       refusal = "calls-annotation:use"
	rUnreadable            refusal = "annotation:unreadable"
	rAmbiguousName         refusal = "name:ambiguous"
	rPaths                 refusal = "limit:paths"
	rNoBody                refusal = "function:no-body"
	rFormulaLimit          refusal = "limit:formula"
	rRecursionTrusted      refusal = "recursion:through-trusted"
	rRecursionPackages     refusal = "recursion:across-packages"
	rRecursionDynamic      refusal = "recursion:dynamic"
	rContractUnusable      refusal = "contract:unusable"
	rFormatLength          refusal = "format:length-unknown"
	rAnnotationUnsupported refusal = "annotation:unsupported"
	rErrCompareUnproved    refusal = "error:compare-unproved"
	rJSONDecodeUnproved    refusal = "json:read-frame-unproved"
	rHandApartUnproved     refusal = "handover:apart-unproved"
	rOwnsStoreUnproved     refusal = "owns:store-unproved"

	// What a report is when it is not a refusal: an obligation that was not
	// proved, which a user meets by annotating or changing the code, and a
	// fault of an annotation or a trust file. The census counts neither.
	rObligation      refusal = "report:obligation"
	rAnnotationFault refusal = "report:annotation"
)

// refusalClasses describes every class: what Go it refuses, and where the
// roadmap plans it. TestRefusalClasses fails for a class without a line
// here, for one no place in the verifier uses, and for a place that
// refuses without a class.
var refusalClasses = map[refusal]string{
	rNoEntryStd:            "a call of a function or method of the standard library that has no shipped entry (Trusted contracts for unproved code)",
	rNoEntryModule:         "a call of a function of the module that has neither annotations nor an entry (annotate it)",
	rNoEntryOther:          "a call of a function or method of another module that has no entry in the trust file (the project writes one)",
	rEntryImpossible:       "a call of a function that no true entry could describe as vego reads entries (Trusted contracts for unproved code)",
	rTypeUintptr:           "a value of type uintptr (not planned in the roadmap)",
	rTypeComplex:           "a value of a complex type (not planned; the Target leaves numerical code out)",
	rTypeUnsafe:            "a value of type unsafe.Pointer (not planned in the roadmap)",
	rTypeOther:             "a value of a type the verifier has no model of, not in another class (Structs and pointers)",
	rTypeIface:             "an interface literal that embeds a declared interface, or an interface with type parameters or the methods of error (Interfaces)",
	rTypeArray:             "an array of anything but numbers and booleans, a slice of arrays, or an array in an interface value (Structs and pointers, What F36 left)",
	rTypeArrayStruct:       "a struct that holds an array of elements larger than a byte, or a pointer to one (Structs and pointers, What F36 left)",
	rTypeArrayElem:         "a slice, map, or channel whose elements are arrays (Structs and pointers, What F36 left)",
	rTypeMapKey:            "a map whose keys are not numbers, strings, or booleans, as pointers or structs (Maps, Not built yet)",
	rPointerTo:             "a pointer to a slice, a map, a pointer, an interface value, a function, or an array (item 7)",
	rChannel:               "a channel: a value of a channel type, a send, a receive, or a range over one (item 11)",
	rGoroutine:             "a go statement (item 11)",
	rSelect:                "a select statement (item 6 and item 11)",
	rIterator:              "a range over a function, an iterator (item 10)",
	rGenericDeclared:       "a generic function or method of the project, verified itself (item 10)",
	rGenericCalled:         "a call of a generic function of the project, or of one without an entry (item 10)",
	rGenericMethod:         "a call of a method of a generic type (item 10)",
	rGenericHanded:         "a generic function used as a value or handed over (item 10)",
	rGenericTypeArgs:       "a call of a generic function with type arguments its entry does not cover (item 10)",
	rGenericTypeParam:      "a value whose type is a type parameter (item 10)",
	rAddrField:             "&s.f of a number, a boolean, or a string, or a pointer method called on such a field (item 7, interior pointers)",
	rAddrElement:           "&xs[i] or &a[i] of a number, a boolean, or a string, or a pointer method called on such an element (item 7, interior pointers)",
	rAddrGlobal:            "&g of a package-level variable, or a pointer method called on one (item 7, interior pointers)",
	rAddrOther:             "the address of anything else that is not a struct or a single value, or new of such a type (item 7)",
	rIfaceNoContract:       "a call through an interface whose method has no contract, of the standard library or of another module (Interfaces)",
	rIfaceForm:             "a call through an interface in a form not supported: a method expression, an embedded interface field, an interface not modelled (Interfaces)",
	rConvOptional:          "a conversion between interfaces with the methods of an optional interface of another module (Dynamic types, Part 3)",
	rConvErrToIface:        "an error converted to an interface other than any (Dynamic types, Not built yet)",
	rConvIfaceType:         "a value of a type with no model converted to an interface (Interfaces)",
	rConvIfaceArray:        "an array, or a pointer to what holds one, converted to an interface (Structs and pointers, What F36 left)",
	rConvWrapsWriter:       "a wrapper that keeps a writer, as a *bufio.Writer, converted to an io.Writer (item 12)",
	rConvBuffer:            "a *bytes.Buffer or *strings.Builder converted to an io.Writer without a declared memory (Sizes under a declared memory)",
	rConvOwns:              "a value that owns memory or an interface value converted to an interface whose methods write behind it (Footprints)",
	rConvStates:            "a value converted to an interface with states that its methods change (State that a value owns)",
	rConvNoContract:        "a value converted to an interface while a method of its type has no contract, of the standard library or of another module (Interfaces)",
	rConvForeignImpl:       "a value converted to an interface whose implementation is code of another module that could run what it holds (Interfaces, second part)",
	rConvByContract:        "a conversion checked against the contract of the interface that fails a condition of that check (Interfaces)",
	rConvToError:           "a value of the project converted to error that the model of errors cannot hold (Dynamic types and typed errors)",
	rConvValue:             "a conversion between types other than to an interface that is not modelled, as between floats and integers (Floats, Strings)",
	rConvMultiValue:        "a result of a call with several converted where it is assigned (item 6)",
	rConvUnplaced:          "a conversion to an interface whose expression cannot be told, as one result of several (item 6)",
	rErrUnknown:            "an error whose origin is not known formatted, wrapped, compared with errors.Is or As, or handed on (Errors)",
	rErrCompare:            "two errors compared, which can panic, or an error compared with another type (Errors)",
	rErrSentinel:           "a package-level error variable that cannot be used as a sentinel (Errors)",
	rDynLocalType:          "an assertion, type switch, or comparison to a type declared inside a function (Dynamic types)",
	rDynAssert:             "a type assertion that is not supported (Dynamic types)",
	rDynSwitch:             "a case of a type switch that is not supported (Dynamic types)",
	rDynCompare:            "an interface value compared with a value of a type that is not supported there (Dynamic types)",
	rDynAs:                 "errors.As in a form not supported (Dynamic types)",
	rLitValue:              "a function literal used as a value whose type has no contract (Function literals, Function values)",
	rLitCaptures:           "a function literal used as a value that assigns or calls what the function around it holds (Function literals)",
	rLitRecursion:          "a function literal used as a value that calls through values or recursion with no variant (Function values)",
	rLitSignature:          "a function literal whose parameters or results have no model, or a literal used in a way not supported (Function literals)",
	rClosure:               "a recursive closure in a form not supported (Function literals)",
	rFuncNoContract:        "a call through a value of a function type that has no contract, of the standard library, of another module, or unnamed (Function values)",
	rFuncMethodValue:       "a method value x.M used as a value (Function values)",
	rFuncMethodExpr:        "a method expression T.M used as a value (Function values)",
	rFuncMadeFrom:          "a function value made from something other than a literal, a function, or a method value (Function values)",
	rFuncTrusted:           "a trusted function used as a value of a function type (Function values)",
	rFuncCallsValues:       "a function used as a value that calls through function or interface values (Function values)",
	rHandUnknownCode:       "a value that may carry code nobody has seen handed to a trusted function (Callbacks handed to trusted functions)",
	rHandNoContract:        "a function with no contract handed to a trusted function that calls it (Callbacks handed to trusted functions)",
	rHandEntry:             "a function handed to a trusted function whose entry lists it under runs or keeps without a contract (Callbacks handed to trusted functions)",
	rHandFootprint:         "a function handed to a trusted function that writes the footprint of an interface value (Footprints)",
	rHandApart:             "what a caller of a function value or an interface method would have to show apart (Footprints)",
	rSortSlice:             "sort.Slice or a relative in a form not supported (Callbacks handed to trusted functions)",
	rDeferLoop:             "defer inside a loop (item 6)",
	rDeferForm:             "a deferred call of a form not supported (item 6)",
	rRecover:               "recover (item 12)",
	rExitContext:           "a call that may end the process where that cannot be said: handed over, in a literal used as a value, deferred (Functions that end the process)",
	rGlobalAssign:          "a package-level variable assigned, or written through, where that is not supported (item 3)",
	rGlobalRead:            "a package-level variable read that is not known to keep its value (item 3)",
	rGlobalType:            "a package-level variable of a type that is not supported there, as one that holds code (item 3)",
	rGlobalUnreliable:      "a package-level variable whose initialiser does not verify (item 3); made only when a proof fails",
	rGlobalFollowed:        "code a call may run that writes a package-level variable in a way that cannot be followed (item 3)",
	rGlobalInit:            "an initialiser of a package-level variable in a form not supported (item 3)",
	rGoto:                  "goto (item 6)",
	rFallthrough:           "fallthrough anywhere but the end of a clause of an expression switch (item 6)",
	rStmtExpr:              "an expression statement that is not a call (item 6)",
	rStmtOther:             "a statement of another kind not supported (item 6)",
	rSwitchArray:           "a switch on an array (Structs and pointers, What F36 left)",
	rSwitchIface:           "a switch whose cases are errors or interface values on a tag of another type (Dynamic types)",
	rRangeForm:             "a range loop whose variables are not declared with :=, or shared before Go 1.22 (item 6)",
	rRangeOther:            "a range over something else not supported (item 6)",
	rOpBits:                "a bit operator on an operand of a type it is not supported for (Integers)",
	rOpOther:               "an operator not supported for its operands (Integers, Strings, Floats)",
	rOpPointer:             "an operator on pointers other than == and !=, or a comparison of pointers to values of size zero (Structs and pointers)",
	rOpNil:                 "a comparison with nil of a type for which it is not supported (Structs and pointers)",
	rIndex:                 "indexing or slicing a value of a type for which it is not supported, or cap of a map (Structs and pointers, Maps)",
	rLiteral:               "a composite literal not supported: keyed slice literals, an index of an array literal, literals of other types (item 6)",
	rExprOther:             "an expression of a kind not supported (item 6)",
	rExprValueShape:        "a value with several parts used where one is needed (item 6)",
	rConstant:              "a constant not supported, or a string sliced with a capacity (Strings)",
	rAppendExpr:            "append inside a larger expression (item 6)",
	rAppendCallTarget:      "a call in the target of an assignment beside an append that may write in place (item 6); made only when a proof fails",
	rCopyElements:          "copy of slices of anything but numbers and booleans (item 6)",
	rCopyTarget:            "copy as the right-hand side of an assignment whose target calls something (item 6)",
	rCopyValue:             "a value with states, as a mutex, or one no rule accounts for, copied by Go (State that a value owns)",
	rBuiltin:               "a built-in function not supported there (item 6)",
	rCallForm:              "a call of a form not supported: a call of what a call returns, a method expression, json encoders or decoders used otherwise (item 6)",
	rCallMultiArgs:         "a call with several results as the arguments of another call, g(f()) (item 6)",
	rCallInitOnly:          "a call of a function that may run only while the package is initialised (Package-level variables)",
	rAssignTarget:          "an assignment to a target not supported: an element of an array not held by a variable, a field of a map value, an embedded pointer (item 6)",
	rAssignInPlace:         "an operand that cannot be read and updated in place, or a value that cannot be assigned to its target (item 6)",
	rAssignMulti:           "a multi-value expression other than a call, or an operator assignment not supported (item 6)",
	rFormatCode:            "formatting that may run code nobody has checked: a value with methods, a String method with no contract or that modifies memory (Variadic calls and formatting)",
	rFormatPack:            "formatting what a slice passed with ... holds (Variadic calls and formatting)",
	rFormatPrints:          "a trusted function that prints through a function with no contract (Variadic calls and formatting)",
	rJSON:                  "encoding/json in a form not supported: a decoder without a limit, an encoder or decoder held in a variable, deferred (JSON)",
	rJSONEncode:            "encoding a value encoding/json may run code of, or that the walk of encoding/json does not model (JSON)",
	rJSONDecode:            "decoding into a value the walk of encoding/json does not model (JSON)",
	rOwnsUntrusted:         "a trusted function that modifies or returns a value that owns memory, without a contract that comes with vego (Ownership in source)",
	rScopedHidden:          "a field the shipped files hide, or a value scoped to a call, used where that is not supported (Footprints, What a handler reads of its request)",
	rScopedWritten:         "a scoped value stored into memory (Footprints)",
	rSizeTooLarge:          "a type larger than one allocation can be (Sizes under a declared memory)",
	rCallsAnnotation:       "a parameter under a Calls annotation used in a form not supported (Callbacks handed to trusted functions)",
	rUnreadable:            "an annotation the function relies on that cannot be read (The annotation language)",
	rAmbiguousName:         "a variable whose name means something else in annotations (The annotation language)",
	rPaths:                 "more than 4000 branches to explore; the census stops the function there (Speed, under Before it is called ready)",
	rNoBody:                "a function without a body (Trusted contracts for unproved code)",
	rFormulaLimit:          "a formula built for the function grows beyond the limit of its size; the census stops the function there (The prover)",
	rRecursionTrusted:      "a cycle of calls through a trusted function that calls back (Callbacks handed to trusted functions)",
	rRecursionPackages:     "a cycle of calls through code of another package, across which no Variant can be checked (Trusted contracts for unproved code)",
	rRecursionDynamic:      "a cycle of calls through an interface method or a function value, as a walk of a tree of interface values (item 12)",
	rContractUnusable:      "a contract or trusted entry that cannot be used at the call (Trusted contracts for unproved code)",
	rFormatLength:          "formatting into a writer text whose length the writer's Write needs bounded and is not counted (Variadic calls and formatting); made only when a proof fails",
	rAnnotationUnsupported: "an annotation of a form that is not supported yet (The annotation language)",
	rErrCompareUnproved:    "two errors compared where neither is shown to be nil or of a comparable kind (Errors); made only when a proof fails",
	rJSONDecodeUnproved:    "a decoder over a reader whose Read contract is not shown to speak only of what Read leaves alone (JSON); made only when a proof fails",
	rHandApartUnproved:     "a value handed over that is not shown to be the one whose footprint the function's Modifies places (Footprints); made only when a proof fails",
	rOwnsStoreUnproved:     "the result of a call stored into an owned field that is not shown to be new (Ownership in source); made only when a proof fails",
	rObligation:            "an obligation that was not proved; not a cause",
	rAnnotationFault:       "a fault of an annotation or of a trust file; not a cause",
}

// proofClasses are the classes that are made only when a proof fails. A
// census answers every question "not proved", so it makes them wherever
// they are reached, where the prover would often prove what they ask; the
// summary lists them apart.
var proofClasses = map[refusal]bool{
	rGlobalUnreliable: true, rAppendCallTarget: true, rFormatLength: true,
	rErrCompareUnproved: true, rJSONDecodeUnproved: true, rHandApartUnproved: true, rOwnsStoreUnproved: true,
}

// typeClass returns the class of a type that layoutOf gives no layout,
// with the type as its detail. It follows layoutOf case by case, to the
// case that has no layout; TestTypeClass holds the two together.
func typeClass(t types.Type) refusal {
	r := typeClassOf(t)
	if t == nil {
		return r
	}
	return withDetail(r, t.String())
}

// typeClassOf is typeClass without the detail. It takes the arms of
// layoutOf in turn: a type parameter; a basic type that has no sort
// (uintptr, complex, unsafe.Pointer); an interface that isIface does not
// model; a pointer to anything but a struct or a single value, where a
// struct that holds a large array is told apart; a map whose keys are not
// modelled; a generic signature; an array of what plainElem refuses; a
// struct that holds such an array; and a channel.
func typeClassOf(t types.Type) refusal {
	if t == nil {
		return rTypeOther
	}
	if _, ok := types.Unalias(t).(*types.TypeParam); ok {
		return rGenericTypeParam
	}
	switch u := t.Underlying().(type) {
	case *types.Basic:
		switch {
		case u.Kind() == types.Uintptr:
			return rTypeUintptr
		case u.Info()&types.IsComplex != 0:
			return rTypeComplex
		case u.Kind() == types.UnsafePointer:
			return rTypeUnsafe
		}
	case *types.Interface:
		return rTypeIface
	case *types.Pointer:
		if holdsArray(u.Elem()) {
			if isArray(u.Elem()) {
				return rPointerTo
			}
			return rTypeArrayStruct
		}
		if _, isTP := types.Unalias(u.Elem()).(*types.TypeParam); isTP {
			return rGenericTypeParam
		}
		return rPointerTo
	case *types.Map:
		return rTypeMapKey
	case *types.Signature:
		return rGenericTypeParam
	case *types.Array:
		return rTypeArray
	case *types.Struct:
		return rTypeArrayStruct
	case *types.Chan:
		return rChannel
	}
	return rTypeOther
}

// elemClass is typeClass for the elements of a slice or a map, where an
// array is not modelled either (elemLayout).
func elemClass(t types.Type) refusal {
	if isArray(t) {
		return withDetail(rTypeArrayElem, t.String())
	}
	return typeClass(t)
}

// mapClass returns the class of a map type whose contents are not
// modelled (mapModelled): its keys, or what it holds.
func mapClass(t types.Type) refusal {
	if !isMap(t) {
		return typeClass(t)
	}
	if !mapKeyed(t) {
		return withDetail(rTypeMapKey, t.String())
	}
	_, elem := mapParts(t)
	return elemClass(elem)
}

// varClass returns the class of a variable that has no value to read: one
// of a type without a model, or something that is no variable.
func (v *fnVerifier) varClass(variable *types.Var) refusal {
	if variable == nil {
		return rExprOther
	}
	if _, ok := layoutOf(variable.Type()); !ok {
		return typeClass(variable.Type())
	}
	return withDetail(rExprOther, "variable "+variable.Name())
}

// funcValueClass returns the class of a call through, or a use as, a value
// of a function type that has no contract.
func (v *fnVerifier) funcValueClass(t types.Type) refusal {
	return withDetail(rFuncNoContract, t.String())
}

// addressClass returns the class of an address that cannot be taken, by
// the form of the expression whose address it is.
func (v *fnVerifier) addressClass(e ast.Expr) refusal {
	switch e := ast.Unparen(e).(type) {
	case *ast.SelectorExpr:
		if selection := v.info.Selections[e]; selection != nil && selection.Kind() == types.FieldVal {
			return withDetail(rAddrField, types.ExprString(e))
		}
		if variable, ok := v.info.Uses[e.Sel].(*types.Var); ok && !variable.IsField() {
			return withDetail(rAddrGlobal, types.ExprString(e))
		}
	case *ast.IndexExpr:
		return withDetail(rAddrElement, types.ExprString(e))
	case *ast.Ident:
		if variable, ok := v.info.Uses[e].(*types.Var); ok && variable.Parent() == variable.Pkg().Scope() {
			return withDetail(rAddrGlobal, e.Name)
		}
	}
	return withDetail(rAddrOther, types.ExprString(e))
}

// callClass returns the class of a call of a function that has no
// contract, by the module the callee belongs to, and of a generic function
// without a trusted contract.
func (v *fnVerifier) callClass(callee *types.Func) refusal {
	name := callee.FullName()
	switch {
	case callee.Pkg() == nil || !strings.Contains(strings.Split(callee.Pkg().Path(), "/")[0], "."):
		return withDetail(rNoEntryStd, name)
	case v.pkgVerifier.inScope(callee.Pkg().Path()) && isGeneric(callee):
		// A generic function of the project waits for generic functions
		// to be verified, not for an entry.
		return withDetail(rGenericCalled, name)
	case v.pkgVerifier.inScope(callee.Pkg().Path()):
		return withDetail(rNoEntryModule, name)
	}
	return withDetail(rNoEntryOther, name)
}

// stmtClass returns the class of a statement of a kind that is not
// supported.
func stmtClass(s ast.Stmt) refusal {
	switch s.(type) {
	case *ast.GoStmt:
		return rGoroutine
	case *ast.SelectStmt:
		return rSelect
	case *ast.SendStmt:
		return rChannel
	}
	return withDetail(rStmtOther, fmt.Sprintf("%T", s))
}

// rangeClass returns the class of a range over a value of a type that is
// not supported.
func rangeClass(t types.Type) refusal {
	switch t.Underlying().(type) {
	case *types.Chan:
		return rChannel
	case *types.Signature:
		return rIterator
	}
	return withDetail(rRangeOther, t.String())
}

// inScope reports whether a package is one of the module a census looks
// at. Outside a census no package is.
func (pv *pkgVerifier) inScope(path string) bool {
	return false
}
