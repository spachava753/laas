package vego

import (
	"encoding/json"
	"fmt"
	"go/ast"
	"go/build"
	"go/token"
	"go/types"
	"maps"
	"os"
	"path/filepath"
	"runtime/debug"
	"slices"
	"strings"
	"sync"
	"time"

	"github.com/spachava753/laas/vego/internal/logic"
	"github.com/spachava753/laas/vego/internal/solver"
	"golang.org/x/tools/go/analysis"
	"golang.org/x/tools/go/types/typeutil"
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

// check panics for a class that is not one of refusalClasses, which
// TestRefusalClasses holds every place that refuses to.
func (r refusal) check() {
	if refusalClasses[refusal(r.class())] == "" {
		panic(fmt.Sprintf("vego: internal error: %q is not a class of refusalClasses", r))
	}
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
	rPointerToArray        refusal = "pointer:to-array"
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
	rConvNoContractOther   refusal = "convert:iface-no-contract-other"
	rIfaceNoContractOther  refusal = "iface-method:no-contract-other"
	rFuncNoContractOther   refusal = "func-value:no-contract-other"
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
	rRecursionCall         refusal = "recursion:through-call"
	rRecursionValue        refusal = "recursion:through-value"
	rRecursionMethod       refusal = "recursion:through-method"
	rRecursionFormat       refusal = "recursion:through-format"
	rContractUnusable      refusal = "contract:unusable"
	rFormatLength          refusal = "format:length-unknown"
	rAnnotationUnsupported refusal = "annotation:unsupported"
	rErrCompareUnproved    refusal = "error:compare-unproved"
	rJSONDecodeUnproved    refusal = "json:read-frame-unproved"
	rHandApartUnproved     refusal = "handover:apart-unproved"
	rOwnsStoreUnproved     refusal = "owns:store-unproved"

	// Events of a census that are not refusals: callees and values of the
	// module taken with the weakest contract, what only a declaration of the
	// trust file lets through, and where the census stops a function.
	rAssumedModule    refusal = "assumed:module"
	rAssumedMethod    refusal = "assumed:module-method"
	rAssumedType      refusal = "assumed:module-type"
	rAssumedCalls     refusal = "assumed:calls"
	rAssumedClosure   refusal = "assumed:closure"
	rDeclaredSizes    refusal = "declared:sizes"
	rDeclaredInputs   refusal = "declared:inputs"
	rInternal         refusal = "limit:internal"
	rLimitAttempts    refusal = "limit:attempts"
	rFacts            refusal = "limit:facts"
	rAnnotationBroken refusal = "annotation:broken"
	rGenerated        refusal = "skip:generated"
	rAnnotateCalls    refusal = "annotate:calls"
	rOwnsKept         refusal = "owns:kept"
	rOwnsSelf         refusal = "owns:self"
	rOwnsReturned     refusal = "owns:returned"
	rScopedKept       refusal = "scoped:kept"

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
	rTypeArrayStruct:       "a struct that holds an array of anything but numbers and booleans, or a pointer to one (Structs and pointers, What F36 left)",
	rTypeArrayElem:         "a slice, map, or channel whose elements are arrays (Structs and pointers, What F36 left)",
	rTypeMapKey:            "a map whose keys are not numbers, strings, or booleans, as pointers or structs (Maps, Not built yet)",
	rPointerTo:             "a pointer to a slice, a map, a pointer, an interface value, or a function, the address of one, or new of one (item 7)",
	rPointerToArray:        "a pointer to an array, the address of one, or new of one (Structs and pointers, What F36 left)",
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
	rAddrOther:             "the address of a value that is not where a pointer can point, not in another class (item 7)",
	rIfaceNoContract:       "a call through an interface of the standard library whose method has no contract (Interfaces, second part: entries ship)",
	rIfaceNoContractOther:  "a call through an interface of another module whose method has no entry, which the project writes (Interfaces, second part)",
	rIfaceForm:             "a call through an interface in a form not supported: a method expression, an embedded interface field, an interface not modelled (Interfaces)",
	rConvOptional:          "a conversion between interfaces with the methods of an optional interface of another module (Dynamic types, Part 3)",
	rConvErrToIface:        "an error converted to an interface other than any (Dynamic types, Not built yet)",
	rConvIfaceType:         "a value of a type with no model converted to an interface (Interfaces)",
	rConvIfaceArray:        "an array, or a value that holds one, converted to an interface (Structs and pointers, What F36 left)",
	rConvWrapsWriter:       "a wrapper that keeps a writer, as a *bufio.Writer, converted to an io.Writer (item 12)",
	rConvBuffer:            "a *bytes.Buffer or *strings.Builder converted to an io.Writer without a declared memory (Sizes under a declared memory)",
	rConvOwns:              "a value that owns memory or an interface value converted to an interface whose methods write behind it (Footprints)",
	rConvStates:            "a value converted to an interface with states that its methods change (State that a value owns)",
	rConvNoContract:        "a value of a type of the standard library converted to an interface while a method of the type has no contract (Interfaces)",
	rConvNoContractOther:   "a value of a type of another module converted to an interface while a method of the type has no entry, which the project writes (Interfaces, second part)",
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
	rLitSignature:          "a function literal whose parameters or results have no model, or a literal used in a way not supported (Function literals)",
	rClosure:               "a recursive closure in a form not supported (Function literals)",
	rFuncNoContract:        "a call through, or a use as, a value of a function type of the standard library, or unnamed, that has no contract (Function values)",
	rFuncNoContractOther:   "a call through, or a use as, a value of a named function type of another module that has no entry, which the project writes (Interfaces and function types of other modules)",
	rFuncMethodValue:       "a method value x.M used as a value (Function values)",
	rFuncMethodExpr:        "a method expression T.M used as a value (Function values)",
	rFuncMadeFrom:          "a function value made from something other than a literal, a function, or a method value (Function values)",
	rFuncTrusted:           "a trusted function used as a value of a function type (Function values)",
	rFuncCallsValues:       "a value that calls a value: a function or a function literal used as a value that calls through function or interface values, or with recursion and no variant (Function values)",
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
	rRecursionCall:         "a cycle of calls that goes through a call of a function of another package handed what may hold code of the package, as reflect.ValueOf or io.ReadFull; an entry that says what it runs lifts it (Function values, what the call graph reads of a call of another package)",
	rRecursionValue:        "a cycle of calls that goes through a call of a function value, or a range over one, which the call graph does not follow to the values it may hold (Function values, Not built yet)",
	rRecursionMethod:       "a cycle of calls that goes through a call of an interface method, which the call graph does not follow to the implementations (item 12, interface values that call interface values)",
	rRecursionFormat:       "a cycle of calls that goes through formatting, which may run the String or Error method of what it formats (Variadic calls and formatting)",
	rContractUnusable:      "a contract or trusted entry that cannot be used at the call (Trusted contracts for unproved code)",
	rFormatLength:          "formatting into a writer text whose length the writer's Write needs bounded and is not counted (Variadic calls and formatting); made only when a proof fails",
	rAnnotationUnsupported: "an annotation of a form that is not supported yet (The annotation language)",
	rErrCompareUnproved:    "two errors compared where neither is shown to be nil or of a comparable kind (Errors); made only when a proof fails",
	rJSONDecodeUnproved:    "a decoder over a reader whose Read contract is not shown to speak only of what Read leaves alone (JSON); made only when a proof fails",
	rHandApartUnproved:     "a value handed over that is not shown to be the one whose footprint the function's Modifies places (Footprints); made only when a proof fails",
	rOwnsStoreUnproved:     "the result of a call stored into an owned field that is not shown to be new (Ownership in source); made only when a proof fails",
	rAssumedModule:         "a call of a function of the module with no contract, taken with the weakest contract; not a cause",
	rAssumedMethod:         "a call of a method of an interface of the module with no contract, taken with the weakest contract; not a cause",
	rAssumedType:           "a call of a value of a function type of the module with no contract, taken with the weakest contract; not a cause",
	rAssumedClosure:        "a call of a recursive closure that the function around it refuses, in its body, which the census walks as a literal with the weakest contract for the call; not a cause",
	rAssumedCalls:          "a value of an unnamed function type handed to a function of the module taken with the weakest contract, which a Calls annotation on it might give a contract; not a cause",
	rDeclaredSizes:         "what only the declared memory of the trust file lets through, as a buffer converted to an io.Writer; not a cause",
	rDeclaredInputs:        "a shipped entry that only the declaration that inputs end makes usable; not a cause",
	rInternal:              "a panic of the verifier that is no refusal; the census stops the function there (The prover)",
	rFacts:                 "a state of the census that holds more facts than the census follows; it stops the function there (Speed, under Before it is called ready)",
	rLimitAttempts:         "more refusals in one function than the census follows; it stops the function there (The prover)",
	rOwnsKept:              "memory an owner owns kept elsewhere: stored, held by a method value or a literal, or handed to what may keep it (Ownership in source)",
	rOwnsSelf:              "an owner that may come to own itself (Ownership in source)",
	rOwnsReturned:          "memory an owner owns returned where no contract can place it (Ownership in source)",
	rScopedKept:            "a value scoped to a call, as an http.ResponseWriter or a *http.Request, kept where a later call could use it (Footprints, The writer of a handler)",
	rAnnotateCalls:         "a call of a parameter of an unnamed function type, which a Calls annotation on the function gives a contract; not a cause",
	rGenerated:             "a function of a generated file, which the census counts apart and does not look at; not a cause",
	rAnnotationBroken:      "a function whose annotations cannot be read, which is not looked at (The annotation language)",
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
	if _, ok := layoutOf(t); ok {
		panic(fmt.Sprintf("vego: internal error: a refusal is classed by the type %s, which has a layout", t))
	}
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
		if isArray(u.Elem()) {
			return rPointerToArray
		}
		if holdsArray(u.Elem()) {
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

// fieldClass is typeClass for the type of a field, where an array of
// anything but numbers and booleans is not modelled (fieldLayout).
func fieldClass(t types.Type) refusal {
	if _, ok := arrayPointer(t); ok {
		return withDetail(rPointerToArray, t.String())
	}
	if isArray(t) {
		return withDetail(rTypeArrayStruct, t.String())
	}
	return typeClass(t)
}

// pointerClass returns the class of the address of, or new of, a value of
// a type that a pointer cannot point to.
func pointerClass(t types.Type) refusal {
	if isArray(t) {
		return withDetail(rPointerToArray, t.String())
	}
	return withDetail(rPointerTo, t.String())
}

// makeClass returns the class of a make that is not of a slice with a
// length.
func makeClass(t types.Type) refusal {
	_, isChan := t.Underlying().(*types.Chan)
	switch {
	case isChan:
		return withDetail(rChannel, t.String())
	case isMap(t):
		return mapClass(t)
	}
	return withDetail(rBuiltin, "make")
}

// elemClass is typeClass for the elements of a slice or a map, where an
// array is not modelled either (elemLayout).
func elemClass(t types.Type) refusal {
	if _, ok := arrayPointer(t); ok {
		return withDetail(rPointerToArray, t.String())
	}
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
// of a function type that has no contract. A call of a parameter of the
// function of an unnamed function type is one a Calls annotation on the
// function gives a contract, which is the project's to write.
func (v *fnVerifier) funcValueClass(fun ast.Expr, t types.Type) refusal {
	if named, ok := types.Unalias(t).(*types.Named); ok {
		return v.ownerClass(named.Obj().Pkg(), rFuncNoContract, rFuncNoContractOther, t.String())
	}
	if id, ok := ast.Unparen(fun).(*ast.Ident); ok && fun != nil {
		if variable, ok := v.info.Uses[id].(*types.Var); ok && slices.Contains(v.fn.params, variable) {
			if _, named := types.Unalias(t).(*types.Named); !named {
				return withDetail(rAnnotateCalls, t.String())
			}
		}
	}
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
	case callee.Pkg() != nil && v.pkgVerifier.inScope(callee.Pkg()) && isGeneric(callee):
		// A generic function of the project waits for generic functions
		// to be verified, not for an entry.
		return withDetail(rGenericCalled, name)
	case callee.Pkg() != nil && v.pkgVerifier.inScope(callee.Pkg()):
		return withDetail(rNoEntryModule, name)
	case callee.Pkg() == nil || v.pkgVerifier.stdPackage(callee.Pkg()):
		return withDetail(rNoEntryStd, name)
	}
	return withDetail(rNoEntryOther, name)
}

// unusableClass returns the class of a use of a contract that cannot be
// used: that of the Go it was refused for where it is declared, or else
// contract:unusable.
func unusableClass(view *contractView) refusal {
	if view.class != "" {
		return view.class
	}
	return rContractUnusable
}

// exprClass returns the class of an expression of a kind not supported:
// that of the type of its operand when the operand's type has no layout,
// as for *p of a p that points to a slice (F18 of the review of F41).
func (v *fnVerifier) exprClass(e ast.Expr) refusal {
	var operand ast.Expr
	switch e := ast.Unparen(e).(type) {
	case *ast.StarExpr:
		operand = e.X
	case *ast.UnaryExpr:
		operand = e.X
	case *ast.SelectorExpr:
		operand = e.X
	case *ast.IndexExpr:
		operand = e.X
	case *ast.SliceExpr:
		operand = e.X
	}
	if operand != nil {
		if t := v.info.TypeOf(operand); t != nil {
			if _, ok := layoutOf(t); !ok {
				return typeClass(t)
			}
		}
	}
	return withDetail(rExprOther, fmt.Sprintf("%T", e))
}

// ownerClass returns the class of what has no contract by the package that
// declares it: one of another module is the project's to give an entry,
// as no-entry:other is (F17 of the review of F41).
func (v *fnVerifier) ownerClass(pkg *types.Package, std, other refusal, detail string) refusal {
	if pkg != nil && !v.pkgVerifier.stdPackage(pkg) && !v.pkgVerifier.inScope(pkg) {
		return withDetail(other, detail)
	}
	return withDetail(std, detail)
}

// typePackage returns the package that declares a named type, or what a
// pointer points to, or nil.
func typePackage(t types.Type) *types.Package {
	if p, ok := t.Underlying().(*types.Pointer); ok {
		t = p.Elem()
	}
	if named, ok := types.Unalias(t).(*types.Named); ok {
		return named.Obj().Pkg()
	}
	return nil
}

// edgeClass returns the class of an edge of the call graph that it cannot
// follow, by the call that makes it: formatting, a call through a value, a
// call of an interface method, or a call of a function of another package
// that may run code it is handed, with what is called as the detail (F28
// of the review of F41).
func (pv *pkgVerifier) edgeClass(call *ast.CallExpr, text string) refusal {
	callee := pv.staticCalleeAt(call)
	if sel, ok := ast.Unparen(call.Fun).(*ast.SelectorExpr); ok {
		if s := pv.info.Selections[sel]; s != nil && s.Kind() == types.MethodVal && types.IsInterface(s.Recv()) {
			callee = s.Obj().(*types.Func)
		}
	}
	switch {
	case strings.HasPrefix(text, "formats with "):
		name := types.ExprString(call.Fun)
		if callee != nil {
			name = callee.FullName()
		}
		return withDetail(rRecursionFormat, name)
	case callee == nil:
		return withDetail(rRecursionValue, types.ExprString(call.Fun))
	case isIfaceMethod(callee):
		return withDetail(rRecursionMethod, callee.FullName())
	}
	return withDetail(rRecursionCall, callee.FullName())
}

// recursionClass returns the class of a cycle of calls that no Variant can
// be checked across: that of its first edge the call graph cannot follow.
func recursionClass(c *cycle) refusal {
	for _, step := range c.steps {
		if !step.resolved {
			if step.class != "" {
				return step.class
			}
			// A range over a function value.
			return withDetail(rRecursionValue, step.text)
		}
	}
	return rRecursionValue
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
func (pv *pkgVerifier) inScope(pkg *types.Package) bool {
	switch {
	case pv.census == nil || !pv.census.looked || pkg == nil:
		return false
	case pv.census.scope == "std":
		return pv.stdPackage(pkg)
	}
	return pkg.Path() == pv.census.scope || strings.HasPrefix(pkg.Path(), pv.census.scope+"/")
}

// stdPackage reports whether a package is one of the standard library's:
// its files are under the source of GOROOT. A path without a dot is no
// test of it, since a GOPATH package or a module may have one (F14 of the
// review of F41).
func (pv *pkgVerifier) stdPackage(pkg *types.Package) bool {
	if known, ok := stdPackages.Load(pkg.Path()); ok {
		return known.(bool)
	}
	std := false
	for _, name := range pkg.Scope().Names() {
		if file := pv.pass.Fset.Position(pkg.Scope().Lookup(name).Pos()).Filename; file != "" {
			std = inGoroot(file)
			break
		}
	}
	stdPackages.Store(pkg.Path(), std)
	return std
}

// stdPackages holds, by path, whether each package met is of the standard
// library.
var stdPackages sync.Map

// inGoroot reports whether a file lies in the source of GOROOT.
func inGoroot(file string) bool {
	return strings.HasPrefix(file, filepath.Join(build.Default.GOROOT, "src")+string(filepath.Separator))
}

// The census mode. A census looks at every function with a body of the
// packages of one module, without proving anything, and records what stops
// the verifier in each. It runs instead of verification, in the packages
// of the module -vego.census-scope names; every other package the driver
// loads is analysed as without it.
//
// A function is looked at in attempts. Each attempt is a fresh verifier
// that walks the function as verification does, with the weakest contract
// when the function has none, and with a solver that starts no Z3 and
// proves nothing (solver.Offline). A refusal ends the attempt, as it ends
// verification. The census records it and stubs what was being executed
// when it was made, the innermost expression with a layout or else the
// statement, and the next attempt walks the function again from the start
// with that stubbed: a stubbed expression is a value of its type about
// which nothing is known, and a stubbed statement gives such values to
// the variables it assigns, walks each body directly inside it once, and
// goes on. No attempt goes on after a panic, so nothing of a verifier
// outlives one; what does is the record: the causes, the stubs, and the
// statements entered.

// censusRun is the census of one package.
type censusRun struct {
	out, scope string
	// looked is set for a package of the module the census looks at;
	// any other is analysed offline for the facts its importers read.
	looked  bool
	records []*censusFunc
	byDecl  map[*ast.FuncDecl]*censusFunc
	// assumed holds the weakest contracts made for what of the module
	// has none, and assumedParams the parameters of an unnamed function
	// type of those contracts.
	assumed       map[assumedKey]*funcInfo
	assumedParams map[*types.Var]bool
	// ensures is the clause of the weakest contract.
	ensures *clause
}

// assumedKey names a weakest contract: of a function or a method called as
// one, of a method of an interface, of a function type, or of the type of a
// closure's variable; one object may be asked for as more than one.
type assumedKey struct {
	obj  types.Object
	kind string
}

// censusFunc is what the census found in one function declaration,
// together with the recursive closures inside it.
type censusFunc struct {
	fn      *funcInfo
	events  []censusEvent
	keys    map[string]bool
	seen    map[ast.Stmt]bool
	stubs   map[any]bool
	stopped bool
	// attempts counts the attempts, branches the branches they followed,
	// and took is the time they took.
	attempts, branches, steps int
	took                      time.Duration
	// stack holds what the attempt is executing: statements, expressions,
	// and the named checks of verify; at is its copy where the last
	// refusal was made.
	stack, at []any
	// walking counts the bodies of stubbed statements being walked, out of
	// which a labelled jump ends the path.
	walking int
}

// censusEvent is a refusal or another event the census met.
type censusEvent struct {
	Class   string `json:"class"`
	Detail  string `json:"detail,omitempty"`
	Pos     string `json:"pos"`
	Message string `json:"message,omitempty"`
	Kind    string `json:"kind"`
}

// censusFatal holds the classes after which an attempt cannot be helped by
// a stub: a body in type parameters and the bound on paths.
var censusFatal = map[refusal]bool{rGenericDeclared: true, rPaths: true, rFacts: true}

// censusMaxAttempts bounds the attempts of one function, and
// censusBranches the branches of all of them together.
const (
	censusMaxAttempts = 100
	censusBranches    = 4 * maxBranches
	censusSteps       = 200_000
	censusFacts       = 20_000
	censusTreeFacts   = 100_000
	censusTrees       = 300
)

// censusKind says how the summary counts an event of a class.
func censusKind(class refusal) string {
	group, _, _ := strings.Cut(string(class), ":")
	switch {
	case group == "assumed" || group == "declared" || group == "annotate":
		return group
	case group == "limit":
		return "stop"
	case group == "skip":
		return "skip"
	case proofClasses[class]:
		return "proof"
	}
	return "cause"
}

// censusPackage reports whether a pass is of a package a census looks at.
func censusPackage(pass *analysis.Pass, scope string) bool {
	path := pass.Pkg.Path()
	switch {
	case scope == "std":
		return len(pass.Files) > 0 && inGoroot(pass.Fset.Position(pass.Files[0].Pos()).Filename)
	case pass.Module != nil && pass.Module.Path != "":
		return pass.Module.Path == scope
	}
	// A package of GOPATH, as those of the corpus of the tests.
	return path == scope || strings.HasPrefix(path, scope+"/")
}

// note records an event once for each class, detail, and position.
func (cf *censusFunc) note(pv *pkgVerifier, pos token.Pos, class refusal, msg string) {
	where := "?"
	if pos.IsValid() {
		at := pv.pass.Fset.Position(pos)
		where = fmt.Sprintf("%s/%s:%d:%d", pv.pass.Pkg.Path(), filepath.Base(at.Filename), at.Line, at.Column)
	}
	key := string(class) + "\x00" + where
	if cf.keys[key] {
		return
	}
	cf.keys[key] = true
	_, detail, _ := strings.Cut(string(class), "|")
	cf.events = append(cf.events, censusEvent{Class: class.class(), Detail: detail, Pos: where, Message: msg, Kind: censusKind(refusal(class.class()))})
}

// push puts what is being executed on the stack, and returns the depth to
// cut it back to.
func (cf *censusFunc) push(x any) int {
	cf.stack = append(cf.stack, x)
	return len(cf.stack) - 1
}

// runCensus is the run of the analyzer on a package of a census.
func (pv *pkgVerifier) runCensus(out, scope, trustPath string, looked bool) (any, error) {
	pv.census = &censusRun{out: out, scope: scope, looked: looked, byDecl: map[*ast.FuncDecl]*censusFunc{}, assumed: map[assumedKey]*funcInfo{},
		assumedParams: map[*types.Var]bool{}}
	node, err := logic.ParseFormula("True")
	if err != nil {
		panic(err)
	}
	pv.census.ensures = &clause{kind: "Ensures", text: "True", node: node}
	pv.z3 = solver.Offline()
	pv.loadTrust(trustPath)
	// A census reports nothing, so a trust file with a problem, which the
	// ordinary run reports at the file and at each use, ends it (F20 of
	// the review of F41).
	if trustPath != "" && pv.projectTrust == nil {
		return nil, fmt.Errorf("the census cannot read the trust file %s", trustPath)
	}
	if f := pv.projectTrust; f != nil {
		var problems []string
		for _, problem := range f.problems {
			problems = append(problems, fmt.Sprintf("%s:%d: %s", f.path, problem.line, problem.msg))
		}
		for _, key := range slices.Sorted(maps.Keys(f.entries)) {
			if why := projectReplaces(f.entries[key]); why != "" {
				problems = append(problems, fmt.Sprintf("%s:%d: %s", f.path, f.entries[key].line, why))
			}
		}
		if len(problems) > 0 {
			return nil, fmt.Errorf("the trust file of the census has problems, so what the census found would rest on a file other than the one meant: %s", strings.Join(problems, "; "))
		}
	}
	pv.collect()
	pv.noteMemory()
	pv.noteInputs()
	pv.checkInvariantsDeclared()
	pv.checkGroupsInitialised()
	pv.precheckOptional()
	pv.checkValueInitialisers()
	pv.exportInvariants()
	for _, name := range pv.ownsOrder {
		if decl := pv.ownsSource[name]; !decl.broken {
			pv.pass.ExportObjectFact(name, &ownsFact{Fields: decl.fields})
		}
	}
	pv.checkTypeContracts()
	pv.exportTypeContracts()
	pv.exportStates()
	pv.pass.ExportPackageFact(&usageFact{Usage: *pv.usage})
	if !looked {
		return pv.usage, nil
	}
	// A function's line is written once the closures inside it, which
	// follow it in the order, are looked at too, so that a run that does
	// not finish keeps what it found.
	written := 0
	for _, fn := range pv.order {
		if fn.closure == nil {
			if err := pv.writeCensus(pv.census.records[written:]); err != nil {
				return nil, err
			}
			written = len(pv.census.records)
		}
		pv.censusLook(fn)
	}
	if err := pv.writeCensus(pv.census.records[written:]); err != nil {
		return nil, err
	}
	// What an annotated function of the package would publish, so that a
	// callee in another package of the module is what it is in its own:
	// its errors, its calls through values, and its summaries (F35 of the
	// review of F41). Nothing is verified; only a census reads these.
	for _, fn := range pv.order {
		// A function with an entry is called by its entry, as in the
		// standard library, whose shipped entries callers use.
		if fn.annotated() && fn.obj.Exported() && fn.decl != nil && fn.closure == nil && !fn.broken && pv.entryFor(fn.obj.FullName()) == nil {
			fact := pv.publishedContract(fn, false, true)
			fact.Census = fn.censusMade
			pv.pass.ExportObjectFact(fn.obj, fact)
		}
	}
	return pv.usage, nil
}

// synthesize gives every function of the package with a body and no
// annotations the weakest contract.
func (pv *pkgVerifier) synthesize() {
	for _, fn := range pv.order {
		// A generic function is refused where it is looked at, and has no
		// contract a call could use.
		if fn.decl != nil && fn.decl.Body != nil && !fn.annotated() && !fn.broken && !isGeneric(fn.obj) {
			fn.ensures = []*clause{pv.census.ensures}
			fn.censusMade = true
			pv.noteAssumedParams(fn)
		}
	}
}

// noteAssumedParams records the parameters of an unnamed function type of
// a weakest contract.
func (pv *pkgVerifier) noteAssumedParams(fn *funcInfo) {
	for _, param := range fn.params {
		if _, named := types.Unalias(param.Type()).(*types.Named); !named && isFunc(param.Type()) {
			pv.census.assumedParams[param] = true
		}
	}
}

// assumedContract returns the weakest contract of a function of the module
// that has none.
func (pv *pkgVerifier) assumedContract(callee *types.Func) *funcInfo {
	key := assumedKey{callee, "func"}
	if fn := pv.census.assumed[key]; fn != nil {
		return fn
	}
	fn := newFuncInfo(callee)
	fn.ensures = []*clause{pv.census.ensures}
	fn.censusMade = true
	pv.noteAssumedParams(fn)
	pv.census.assumed[key] = fn
	return fn
}

// assumedMethod returns the weakest contract of a method of an interface
// of the module that has none.
func (pv *pkgVerifier) assumedMethod(method *types.Func) *funcInfo {
	key := assumedKey{method, "method"}
	if fn := pv.census.assumed[key]; fn != nil {
		return fn
	}
	fn := newFuncInfo(withoutReceiver(method))
	fn.ensures = []*clause{pv.census.ensures}
	fn.methodOf = method
	fn.censusMade = true
	pv.census.assumed[key] = fn
	return fn
}

// assumedType returns the weakest contract of a function type of the
// module that has none.
func (pv *pkgVerifier) assumedType(name *types.TypeName) *funcInfo {
	key := assumedKey{name, "type"}
	if fn := pv.census.assumed[key]; fn != nil {
		return fn
	}
	sig := name.Type().Underlying().(*types.Signature)
	fn := newFuncInfo(types.NewFunc(name.Pos(), name.Pkg(), name.Name(), sig))
	fn.ensures = []*clause{pv.census.ensures}
	fn.valueOf = name
	fn.censusMade = true
	pv.census.assumed[key] = fn
	return fn
}

// assumedClosure returns the weakest contract of the type of a variable
// that holds a recursive closure.
func (pv *pkgVerifier) assumedClosure(variable *types.Var) *funcInfo {
	key := assumedKey{variable, "closure"}
	if fn := pv.census.assumed[key]; fn != nil {
		return fn
	}
	fn := newFuncInfo(types.NewFunc(variable.Pos(), variable.Pkg(), variable.Name(), variable.Type().Underlying().(*types.Signature)))
	fn.ensures = []*clause{pv.census.ensures}
	fn.censusMade = true
	pv.census.assumed[key] = fn
	return fn
}

// noteAssumed records, at a use, that a contract is the weakest one the
// census made.
func (v *fnVerifier) noteAssumed(pos token.Pos, fn *funcInfo, class refusal, what string) {
	if v.census != nil && fn != nil && fn.censusMade {
		v.census.note(v.pkgVerifier, pos, withDetail(class, what), "")
	}
}

// censusLook looks at one function, and at the recursive closures inside
// it into the same record.
func (pv *pkgVerifier) censusLook(fn *funcInfo) {
	if rc := fn.closure; rc != nil {
		cf := pv.census.byDecl[rc.outer]
		if cf == nil || cf.stopped {
			return
		}
		// A closure the function around it refuses is not verified as one;
		// its body is walked as a literal no attempt entered.
		if outer := pv.funcs[pv.info.Defs[rc.outer.Name].(*types.Func)]; rc.refused != "" || capturesBoxed(rc, pv.newVerifier(outer).findBoxed(rc.outer.Body)) != nil {
			return
		}
		pv.censusAttempts(cf, fn, (*fnVerifier).verify)
		return
	}
	if fn.decl == nil || fn.decl.Body == nil {
		return
	}
	cf := &censusFunc{fn: fn, keys: map[string]bool{}, seen: map[ast.Stmt]bool{}, stubs: map[any]bool{}}
	pv.census.records = append(pv.census.records, cf)
	pv.census.byDecl[fn.decl] = cf
	if fn.broken {
		cf.note(pv, fn.decl.Name.Pos(), rAnnotationBroken, "its annotations cannot be read")
		cf.stopped = true
		return
	}
	// Code a tool wrote is not what a project writes, and one generated
	// file can hold more functions than the rest of its module; its
	// functions are counted apart, not looked at.
	for _, file := range pv.pass.Files {
		if file.Pos() <= fn.decl.Pos() && fn.decl.End() <= file.End() && ast.IsGenerated(file) {
			cf.note(pv, fn.decl.Name.Pos(), rGenerated, "the file is generated")
			cf.stopped = true
			return
		}
	}
	pv.censusAttempts(cf, fn, (*fnVerifier).verify)
	pv.censusLiterals(cf, fn)
}

// censusLiterals walks each function literal of a function whose body no
// attempt entered, from the function's entry state, until every one has
// been entered or the census stopped.
func (pv *pkgVerifier) censusLiterals(cf *censusFunc, fn *funcInfo) {
	tried := map[*ast.FuncLit]bool{}
	for !cf.stopped {
		var next *ast.FuncLit
		ast.Inspect(fn.decl.Body, func(n ast.Node) bool {
			if lit, ok := n.(*ast.FuncLit); ok && next == nil && !tried[lit] && len(lit.Body.List) > 0 && !cf.seen[lit.Body.List[0]] {
				next = lit
			}
			return next == nil
		})
		if next == nil {
			return
		}
		tried[next] = true
		pv.censusAttempts(cf, fn, func(v *fnVerifier) {
			v.boxed = v.findBoxed(fn.decl.Body)
			v.looped = findLooped(fn.decl.Body)
			v.censusLiteral(next, v.enter())
		})
	}
}

// censusAttempts runs a task of the census in attempts until one ends
// without a refusal that a stub can help.
func (pv *pkgVerifier) censusAttempts(cf *censusFunc, fn *funcInfo, task func(*fnVerifier)) {
	start := time.Now()
	defer func() { cf.took += time.Since(start) }()
	for attempt := 0; !cf.stopped; attempt++ {
		cf.attempts++
		if attempt == censusMaxAttempts {
			cf.note(pv, fn.obj.Pos(), rLimitAttempts, fmt.Sprintf("more than %d refusals", censusMaxAttempts))
			cf.stopped = true
			return
		}
		if pv.censusAttempt(cf, fn, task) {
			return
		}
	}
}

// censusAttempt runs one attempt, and reports whether it ended for good.
func (pv *pkgVerifier) censusAttempt(cf *censusFunc, fn *funcInfo, task func(*fnVerifier)) (done bool) {
	v := pv.newVerifier(fn)
	v.census = cf
	cf.stack, cf.at, cf.walking = nil, nil, 0
	pv.current = fn
	defer func() { pv.current = nil }()
	defer pv.costing(fn)()
	defer func() {
		r := recover()
		if r == nil {
			done = true
			return
		}
		done = true
		switch r := r.(type) {
		case unsupported:
			cf.note(pv, r.pos, r.class, r.msg)
			if censusFatal[refusal(r.class.class())] {
				cf.stopped = true
				return
			}
			// The innermost entry not stubbed yet: a stub that did not help
			// gives way to the one around it, up to the statement (F34 of
			// the review of F41).
			var target any
			for i := len(cf.at) - 1; i >= 0 && target == nil; i-- {
				if !cf.stubs[cf.at[i]] {
					target = cf.at[i]
				}
			}
			if target == nil {
				cf.stopped = true
				return
			}
			cf.stubs[target] = true
			done = false
		case logic.TooLarge:
			cf.note(pv, fn.obj.Pos(), rFormulaLimit, "a formula built for it has grown beyond the limit")
			cf.stopped = true
		case abort:
			cf.note(pv, fn.obj.Pos(), rUnreadable, "an annotation it relies on cannot be read")
			cf.stopped = true
		default:
			cf.note(pv, fn.obj.Pos(), rInternal, fmt.Sprintf("%v; at %s", r, panicFrames()))
			cf.stopped = true
		}
	}()
	task(v)
	return true
}

// panicFrames returns the first functions of vego on the stack of a panic
// being recovered, for the message of a limit:internal event.
func panicFrames() string {
	var frames []string
	for _, line := range strings.Split(string(debug.Stack()), "\n") {
		const prefix = "github.com/spachava753/laas/vego."
		if strings.HasPrefix(line, prefix) && !strings.Contains(line, "panicFrames") && !strings.Contains(line, "censusAttempt") {
			name, _, _ := strings.Cut(strings.TrimPrefix(line, prefix), "(0x")
			frames = append(frames, strings.TrimSuffix(name, "("))
			if len(frames) == 8 {
				break
			}
		}
	}
	return strings.Join(frames, " < ")
}

// censusTrees stops a census in a function whose errors with a known tree
// and targets of errors.Is, gathered over every path it walks, have grown
// past what it follows: each pair is a fact, stated on the path where a
// tree or a target is met, so they grow with the square of the paths.
func (v *fnVerifier) censusTrees() {
	if v.census != nil && (len(v.trees) > censusTrees || len(v.trees)*len(v.isTargets) > censusTreeFacts) {
		v.unsupported(v.fn.decl.Pos(), rFacts, fmt.Sprintf("the census met %d errors of known tree and %d targets of errors.Is over the paths of the function", len(v.trees), len(v.isTargets)))
	}
}

// censusRefused is called where a refusal is made, before it panics: the
// census keeps what was being executed.
func (v *fnVerifier) censusRefused() {
	if v.census != nil {
		v.census.at = slices.Clone(v.census.stack)
	}
}

// censusRefuse records a refusal that the census goes on past without a
// panic, and reports whether it did: outside a census the caller panics.
func (v *fnVerifier) censusRefuse(pos token.Pos, class refusal, msg string) bool {
	if v.census == nil {
		return false
	}
	v.census.note(v.pkgVerifier, pos, class, msg)
	return true
}

// censusEval is the start of eval in a census. It returns a value for a
// stubbed expression, and puts any other with a layout on the stack until
// done is called.
func (v *fnVerifier) censusEval(e ast.Expr, st *state) (val value, done func()) {
	t := v.info.TypeOf(e)
	if _, ok := layoutOf(t); !ok {
		return nil, func() {}
	}
	if v.census.stubs[e] {
		// What the expression is made of is still looked at, so that a
		// refusal inside it is found (F15 of the review of F41).
		v.censusOperands(e, st)
		return v.unknown("census", t, st), nil
	}
	depth := v.census.push(e)
	return nil, func() { v.census.stack = v.census.stack[:depth] }
}

// censusConversion is the start of evalAs in a census, for a conversion
// to another type: a stubbed conversion looks at what it converts and is a
// value of the type converted to about which nothing is known, and any
// other is on the stack until done is called, so that a refusal of the
// conversion stubs the conversion (F34 of the review of F41).
func (v *fnVerifier) censusConversion(e ast.Expr, want types.Type, st *state) (val value, done func()) {
	if types.Identical(v.info.TypeOf(e), want) {
		return nil, func() {}
	}
	if _, ok := layoutOf(want); !ok {
		return nil, func() {}
	}
	key := censusConvert{e}
	if v.census.stubs[key] {
		// What is converted is evaluated as it stands, without the
		// conversion, which is what was refused.
		inner := ast.Unparen(e)
		if _, ok := layoutOf(v.info.TypeOf(e)); ok && !isFunc(v.info.TypeOf(e)) {
			v.converting[inner]++
			v.eval(e, st, nil)
			v.converting[inner]--
		} else {
			v.censusOperands(e, st)
		}
		return v.unknown("census", want, st), nil
	}
	depth := v.census.push(key)
	return nil, func() { v.census.stack = v.census.stack[:depth] }
}

// censusConvert is the key of a conversion on the stack of a census.
type censusConvert struct{ e ast.Expr }

// censusCheck runs a named check of verify in a census: a stubbed check is
// left out.
func (v *fnVerifier) censusCheck(name string, check func()) {
	if v.census == nil {
		check()
		return
	}
	key := fmt.Sprintf("%s@%d", name, v.fn.decl.Pos())
	if v.census.stubs[key] {
		return
	}
	depth := v.census.push(key)
	defer func() { v.census.stack = v.census.stack[:depth] }()
	check()
}

// censusStmt is seq's dispatch of one statement in a census. A stubbed
// statement is replaced by censusStub; any other is on the stack while its
// own part runs, and off it while what follows it runs.
func (v *fnVerifier) censusStmt(s ast.Stmt, st *state, c ctrl, k func(*state), run func(k func(*state))) {
	if v.census == nil {
		run(k)
		return
	}
	v.census.seen[s] = true
	if labeled, ok := s.(*ast.LabeledStmt); ok {
		v.census.seen[labeled.Stmt] = true
	}
	// The paths of a function, walked again in each attempt, are bounded
	// by the statements walked, which bounds the time and the memory.
	v.census.steps++
	if v.census.steps > censusSteps {
		v.unsupported(s.Pos(), rPaths, fmt.Sprintf("the census walked more than %d statements over the attempts of the function", censusSteps))
	}
	// What a state holds is bounded too: facts that relate every error made
	// on the paths walked to every target met grow with the square of the
	// paths, which a census walks more of than verification does.
	if len(st.hyps) > censusFacts {
		v.unsupported(s.Pos(), rFacts, fmt.Sprintf("a state of the census holds more than %d facts", censusFacts))
	}
	if v.census.stubs[s] {
		v.censusStub(s, st, c, k)
		return
	}
	depth := v.census.push(s)
	defer func() { v.census.stack = v.census.stack[:depth] }()
	run(func(next *state) {
		tail := slices.Clone(v.census.stack[depth:])
		v.census.stack = v.census.stack[:depth]
		defer func() { v.census.stack = append(v.census.stack[:depth], tail...) }()
		k(next)
	})
}

// censusStub executes a stubbed statement: the variables it assigns or
// declares get values about which nothing is known, each body directly
// inside it is walked once with every way out of it ending the path, and
// the path goes on unless the statement leaves the block.
func (v *fnVerifier) censusStub(s ast.Stmt, st *state, c ctrl, k func(*state)) {
	// The variables it declares get their values first, so that a
	// condition that reads one, as ok in if v, ok := x.(T); ok, has one.
	v.censusForget(s, st)
	v.evaluate(st, func() { v.censusStmtOperands(s, st) })
	end := func(*state) {}
	walk := func(list []ast.Stmt, from, to token.Pos) {
		if n := len(list); n > 0 {
			if last, ok := list[n-1].(*ast.BranchStmt); ok && last.Tok == token.FALLTHROUGH {
				list = list[:n-1]
			}
		}
		v.census.walking++
		defer func() { v.census.walking-- }()
		v.seq(list, from, to, st.clone(), ctrl{brk: end, cont: end}, end)
	}
	var bodies func(s ast.Stmt)
	bodies = func(s ast.Stmt) {
		switch s := s.(type) {
		case *ast.LabeledStmt:
			bodies(s.Stmt)
		case *ast.BlockStmt:
			walk(s.List, s.Lbrace, s.Rbrace)
		case *ast.IfStmt:
			walk(s.Body.List, s.Body.Lbrace, s.Body.Rbrace)
			if s.Else != nil {
				bodies(s.Else)
			}
		case *ast.ForStmt:
			walk(s.Body.List, s.Body.Lbrace, s.Body.Rbrace)
		case *ast.RangeStmt:
			walk(s.Body.List, s.Body.Lbrace, s.Body.Rbrace)
		case *ast.SwitchStmt:
			for _, clause := range s.Body.List {
				cc := clause.(*ast.CaseClause)
				walk(cc.Body, cc.Colon, cc.End())
			}
		case *ast.TypeSwitchStmt:
			for _, clause := range s.Body.List {
				cc := clause.(*ast.CaseClause)
				if implicit, ok := v.info.Implicits[cc].(*types.Var); ok {
					v.censusForgetVar(implicit, st)
				}
				walk(cc.Body, cc.Colon, cc.End())
			}
		case *ast.SelectStmt:
			for _, clause := range s.Body.List {
				cc := clause.(*ast.CommClause)
				walk(cc.Body, cc.Colon, cc.End())
			}
		}
	}
	bodies(s)
	if !leaves(s) {
		k(st)
	}
}

// censusOperands evaluates, and drops, each operand of a stubbed
// expression: the receiver and the arguments of a call, and the operands
// of any other expression. Each is an eval of its own, which an attempt
// can stub in turn.
func (v *fnVerifier) censusOperands(e ast.Expr, st *state) {
	var operands []ast.Expr
	switch e := ast.Unparen(e).(type) {
	case *ast.CallExpr:
		// What is called is not a value of the call: a function, a method
		// of a receiver, or a variable that holds a literal the walk calls
		// in place. Only what it is made of is looked at.
		switch fun := ast.Unparen(e.Fun).(type) {
		case *ast.SelectorExpr:
			operands = append(operands, fun.X)
		case *ast.Ident, *ast.FuncLit:
		default:
			v.censusOperands(fun, st)
		}
		operands = append(operands, e.Args...)
	case *ast.SelectorExpr:
		operands = []ast.Expr{e.X}
	case *ast.IndexExpr:
		operands = []ast.Expr{e.X, e.Index}
	case *ast.SliceExpr:
		operands = []ast.Expr{e.X, e.Low, e.High, e.Max}
	case *ast.StarExpr:
		operands = []ast.Expr{e.X}
	case *ast.UnaryExpr:
		operands = []ast.Expr{e.X}
	case *ast.BinaryExpr:
		operands = []ast.Expr{e.X, e.Y}
	case *ast.TypeAssertExpr:
		operands = []ast.Expr{e.X}
	case *ast.KeyValueExpr:
		operands = []ast.Expr{e.Key, e.Value}
	case *ast.CompositeLit:
		operands = e.Elts
	}
	for _, operand := range operands {
		v.censusDropped(operand, st)
	}
}

// censusDropped evaluates an expression whose value is dropped: a value
// with a layout by eval, and anything else by its operands. A function
// literal is left to be walked as one no attempt entered.
func (v *fnVerifier) censusDropped(e ast.Expr, st *state) {
	if e == nil {
		return
	}
	if kv, ok := e.(*ast.KeyValueExpr); ok {
		// The key of a struct literal is a field name.
		if _, isID := kv.Key.(*ast.Ident); !isID || v.info.Types[kv.Key].IsValue() {
			v.censusDropped(kv.Key, st)
		}
		v.censusDropped(kv.Value, st)
		return
	}
	if _, isLit := ast.Unparen(e).(*ast.FuncLit); isLit {
		return
	}
	tv, ok := v.info.Types[e]
	if !ok || !tv.IsValue() || tv.Value != nil {
		return
	}
	inner := ast.Unparen(e)
	if call, ok := inner.(*ast.CallExpr); ok {
		if _, builtin := typeutil.Callee(v.info, call).(*types.Builtin); builtin {
			// append, copy, and the like are refused out of place; what
			// they are given is what is looked at.
			v.censusOperands(e, st)
			return
		}
	}
	// A value of a function type is made where it is converted to the
	// type it is given, which is not here: a function or method named has
	// nothing inside it to look at, and anything else is looked at by what
	// it is made of.
	if _, ok := layoutOf(tv.Type); !ok || isFunc(tv.Type) {
		v.censusOperands(e, st)
		return
	}
	// An expression Go converts to an interface type is evaluated with the
	// conversion, as where it stands.
	if targets := v.findConversions().converted[inner]; len(targets) > 0 {
		v.evalAs(e, targets[0], st, nil)
		return
	}
	v.eval(e, st, nil)
}

// censusStmtOperands evaluates, and drops, the expressions of a stubbed
// statement, and those of its init and post statements: right-hand sides
// and what the targets are made of, conditions, the range expression, the
// tag and the cases, the call of go and defer, and a sent value.
func (v *fnVerifier) censusStmtOperands(s ast.Stmt, st *state) {
	if s == nil {
		return
	}
	target := func(e ast.Expr) {
		if _, isID := ast.Unparen(e).(*ast.Ident); !isID {
			v.censusOperands(e, st)
		}
	}
	switch s := s.(type) {
	case *ast.LabeledStmt:
		v.censusStmtOperands(s.Stmt, st)
	case *ast.ExprStmt:
		v.censusDropped(s.X, st)
	case *ast.AssignStmt:
		for _, lhs := range s.Lhs {
			target(lhs)
		}
		for _, rhs := range s.Rhs {
			v.censusDropped(rhs, st)
		}
	case *ast.IncDecStmt:
		target(s.X)
	case *ast.SendStmt:
		v.censusDropped(s.Chan, st)
		v.censusDropped(s.Value, st)
	case *ast.GoStmt:
		v.censusDropped(s.Call, st)
	case *ast.DeferStmt:
		v.censusDropped(s.Call, st)
	case *ast.ReturnStmt:
		for _, r := range s.Results {
			v.censusDropped(r, st)
		}
	case *ast.DeclStmt:
		if gen, ok := s.Decl.(*ast.GenDecl); ok {
			for _, spec := range gen.Specs {
				if vs, ok := spec.(*ast.ValueSpec); ok {
					for _, value := range vs.Values {
						v.censusDropped(value, st)
					}
				}
			}
		}
	case *ast.IfStmt:
		v.censusStmtOperands(s.Init, st)
		v.censusDropped(s.Cond, st)
		if next, ok := s.Else.(*ast.IfStmt); ok {
			v.censusStmtOperands(next, st)
		}
	case *ast.ForStmt:
		v.censusStmtOperands(s.Init, st)
		v.censusDropped(s.Cond, st)
		v.censusStmtOperands(s.Post, st)
	case *ast.RangeStmt:
		v.censusDropped(s.X, st)
	case *ast.SwitchStmt:
		v.censusStmtOperands(s.Init, st)
		v.censusDropped(s.Tag, st)
		for _, clause := range s.Body.List {
			for _, e := range clause.(*ast.CaseClause).List {
				v.censusDropped(e, st)
			}
		}
	case *ast.TypeSwitchStmt:
		v.censusStmtOperands(s.Init, st)
		switch a := s.Assign.(type) {
		case *ast.ExprStmt:
			v.censusDropped(a.X.(*ast.TypeAssertExpr).X, st)
		case *ast.AssignStmt:
			v.censusDropped(a.Rhs[0].(*ast.TypeAssertExpr).X, st)
		}
	case *ast.SelectStmt:
		for _, clause := range s.Body.List {
			v.censusStmtOperands(clause.(*ast.CommClause).Comm, st)
		}
	}
}

// leaves reports whether a statement never goes on to the next one.
func leaves(s ast.Stmt) bool {
	switch s := s.(type) {
	case *ast.ReturnStmt, *ast.BranchStmt:
		return true
	case *ast.LabeledStmt:
		return leaves(s.Stmt)
	case *ast.ExprStmt:
		if call, ok := ast.Unparen(s.X).(*ast.CallExpr); ok {
			if id, ok := ast.Unparen(call.Fun).(*ast.Ident); ok && id.Name == "panic" {
				return true
			}
		}
	}
	return false
}

// censusForget gives every local variable a statement assigns or declares,
// outside the function literals in it, a value about which nothing is
// known.
func (v *fnVerifier) censusForget(s ast.Stmt, st *state) {
	ast.Inspect(s, func(n ast.Node) bool {
		var ids []ast.Expr
		switch n := n.(type) {
		case *ast.FuncLit:
			return false
		case *ast.AssignStmt:
			ids = n.Lhs
		case *ast.IncDecStmt:
			ids = []ast.Expr{n.X}
		case *ast.RangeStmt:
			ids = []ast.Expr{n.Key, n.Value}
		case *ast.ValueSpec:
			for _, id := range n.Names {
				ids = append(ids, id)
			}
		}
		for _, e := range ids {
			if id, ok := e.(*ast.Ident); ok && e != nil {
				if variable, ok := v.info.ObjectOf(id).(*types.Var); ok {
					v.censusForgetVar(variable, st)
				}
			}
		}
		return true
	})
}

// censusForgetVar gives a local variable a value about which nothing is
// known, or none when its type has no layout, so that its uses refuse
// with the class of its type.
func (v *fnVerifier) censusForgetVar(variable *types.Var, st *state) {
	if variable.IsField() || variable.Pkg() == nil || variable.Parent() == variable.Pkg().Scope() || variable.Name() == "_" {
		return
	}
	if _, ok := layoutOf(variable.Type()); !ok {
		delete(st.vals, variable)
		return
	}
	v.bind(st, variable, v.unknown(variable.Name(), variable.Type(), st))
}

// censusLiteral walks the body of a function literal that no attempt
// entered, as madeLiteral walks a literal made into a value, under the
// weakest contract of its own signature; what it captures is a value of
// its type about which nothing is known.
func (v *fnVerifier) censusLiteral(lit *ast.FuncLit, st *state) {
	sig := v.info.TypeOf(lit).(*types.Signature)
	fn := newFuncInfo(types.NewFunc(lit.Pos(), v.pass.Pkg, "func literal", sig))
	fn.decl = &ast.FuncDecl{Name: &ast.Ident{NamePos: lit.Pos(), Name: "func literal"}, Type: lit.Type, Body: lit.Body}
	fn.ensures = []*clause{v.pkgVerifier.census.ensures}
	site := v.site(lit.Pos(), "in the function literal at %s", v.placeOf(lit.Pos()))
	sv, entry, _ := v.subVerifier(fn, st, nil, site)
	ast.Inspect(lit.Body, func(n ast.Node) bool {
		id, ok := n.(*ast.Ident)
		if !ok {
			return true
		}
		variable, ok := v.info.Uses[id].(*types.Var)
		if ok && !variable.IsField() && variable.Pkg() == v.pass.Pkg && variable.Parent() != v.pass.Pkg.Scope() &&
			(variable.Pos() < lit.Pos() || variable.Pos() >= lit.End()) && entry.vals[variable] == nil {
			// One that lives in memory gets a box of its own.
			if _, ok := layoutOf(variable.Type()); ok {
				sv.bind(entry, variable, sv.unknown(variable.Name(), variable.Type(), entry))
			}
		}
		return true
	})
	sv.looped = findLooped(lit.Body)
	sv.censusCheck("classifyLiterals", sv.classifyLiterals)
	sv.seq(lit.Body.List, lit.Body.Lbrace, lit.Body.Rbrace, entry, ctrl{}, func(end *state) {
		sv.censusCheck("end", func() { sv.returned(end, nil, lit.Body.Rbrace) })
	})
}

// censusReported records a report of a census package that refuses.
func (pv *pkgVerifier) censusReported(pos token.Pos, class refusal, msg string) {
	if class == rObligation || class == rAnnotationFault {
		return
	}
	if fn := pv.current; fn != nil {
		decl := fn.decl
		if fn.closure != nil {
			decl = fn.closure.outer
		}
		if cf := pv.census.byDecl[decl]; cf != nil {
			cf.note(pv, pos, class, msg)
		}
	}
}

// censusLine is one line of the file a census writes: a function with what
// stopped it.
type censusLine struct {
	Module     string        `json:"module"`
	Package    string        `json:"package"`
	Function   string        `json:"function"`
	Pos        string        `json:"pos"`
	Statements int           `json:"statements"`
	Unseen     int           `json:"unseen"`
	UnseenAt   []string      `json:"unseen_at,omitempty"`
	Stopped    bool          `json:"stopped,omitempty"`
	Attempts   int           `json:"attempts"`
	Millis     int64         `json:"ms"`
	Events     []censusEvent `json:"events,omitempty"`
}

// censusOut serialises the writes of the packages of one process.
var censusOut sync.Mutex

// writeCensus appends the lines of functions to the census file.
func (pv *pkgVerifier) writeCensus(records []*censusFunc) error {
	if len(records) == 0 {
		return nil
	}
	// The standard library comes with no module, or one with an empty
	// path.
	module := "std"
	if pv.pass.Module != nil && pv.pass.Module.Path != "" {
		module = pv.pass.Module.Path
	}
	var text []byte
	for _, cf := range records {
		statements, unseen := 0, 0
		var unseenAt []string
		// A statement after one that never goes on, in the same list, is
		// one Go never reaches, and no attempt enters it (F10 of the review
		// of F41).
		count := func(list []ast.Stmt) {
			reached := true
			for _, s := range list {
				switch s.(type) {
				case *ast.CaseClause, *ast.CommClause:
					// The clauses of a switch or select body, whose own
					// statements are counted.
					continue
				}
				statements++
				if reached && !cf.seen[s] {
					unseen++
					if len(unseenAt) < 5 {
						at := pv.pass.Fset.Position(s.Pos())
						unseenAt = append(unseenAt, fmt.Sprintf("%s:%d", filepath.Base(at.Filename), at.Line))
					}
				}
				reached = reached && !pv.terminates(s)
			}
		}
		ast.Inspect(cf.fn.decl.Body, func(n ast.Node) bool {
			switch n := n.(type) {
			case *ast.BlockStmt:
				count(n.List)
			case *ast.CaseClause:
				count(n.Body)
			case *ast.CommClause:
				count(n.Body)
			}
			return true
		})
		at := pv.pass.Fset.Position(cf.fn.decl.Name.Pos())
		// A function is named F, and a method (T).M or (*T).M.
		name := cf.fn.obj.Name()
		if recv := cf.fn.obj.Type().(*types.Signature).Recv(); recv != nil {
			name = "(" + types.TypeString(recv.Type(), types.RelativeTo(cf.fn.obj.Pkg())) + ")." + name
		}
		line := censusLine{Module: module, Package: pv.pass.Pkg.Path(), Function: name,
			Pos:        fmt.Sprintf("%s/%s:%d", pv.pass.Pkg.Path(), filepath.Base(at.Filename), at.Line),
			Statements: statements, Unseen: unseen, UnseenAt: unseenAt, Stopped: cf.stopped, Attempts: cf.attempts, Millis: cf.took.Milliseconds(), Events: cf.events}
		b, err := json.Marshal(line)
		if err != nil {
			return err
		}
		text = append(append(text, b...), '\n')
	}
	censusOut.Lock()
	defer censusOut.Unlock()
	f, err := os.OpenFile(pv.census.out, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0o644)
	if err != nil {
		return err
	}
	if _, err := f.Write(text); err != nil {
		f.Close()
		return err
	}
	return f.Close()
}

// terminates reports whether a statement is terminating, as the Go
// specification defines it, or a call of a function whose contract says it
// never returns.
func (pv *pkgVerifier) terminates(s ast.Stmt) bool {
	switch s := s.(type) {
	case *ast.ReturnStmt:
		return true
	case *ast.BranchStmt:
		return s.Tok == token.GOTO || s.Tok == token.FALLTHROUGH
	case *ast.ExprStmt:
		call, ok := ast.Unparen(s.X).(*ast.CallExpr)
		if !ok {
			return false
		}
		if isBuiltin(pv.info, call, "panic") {
			return true
		}
		if callee := pv.calleeAt(call); callee != nil && !isGeneric(callee) {
			return neverReturns(pv.contractOf(callee))
		}
	case *ast.BlockStmt:
		return len(s.List) > 0 && pv.terminates(s.List[len(s.List)-1])
	case *ast.IfStmt:
		return s.Else != nil && pv.terminates(s.Body) && pv.terminates(s.Else)
	case *ast.LabeledStmt:
		return !breaks(s.Stmt, s.Stmt, s.Label) && pv.terminates(s.Stmt)
	case *ast.ForStmt:
		return s.Cond == nil && !breaks(s.Body, s, nil)
	case *ast.SwitchStmt, *ast.TypeSwitchStmt, *ast.SelectStmt:
		var body *ast.BlockStmt
		switch s := s.(type) {
		case *ast.SwitchStmt:
			body = s.Body
		case *ast.TypeSwitchStmt:
			body = s.Body
		case *ast.SelectStmt:
			body = s.Body
		}
		hasDefault := false
		for _, clause := range body.List {
			var list []ast.Stmt
			switch cc := clause.(type) {
			case *ast.CaseClause:
				list, hasDefault = cc.Body, hasDefault || cc.List == nil
			case *ast.CommClause:
				list, hasDefault = cc.Body, true
			}
			if len(list) == 0 || !pv.terminates(list[len(list)-1]) || breaks(&ast.BlockStmt{List: list}, s, nil) {
				return false
			}
		}
		return hasDefault
	}
	return false
}

// breaks reports whether a body holds a break that leaves the statement
// target: one without a label outside any nested for, switch, or select,
// or one that names target's label.
func breaks(body ast.Node, target ast.Stmt, label *ast.Ident) bool {
	found := false
	var walk func(n ast.Node, nested bool)
	walk = func(n ast.Node, nested bool) {
		ast.Inspect(n, func(m ast.Node) bool {
			switch m := m.(type) {
			case *ast.FuncLit:
				return false
			case *ast.BranchStmt:
				if m.Tok == token.BREAK && (m.Label == nil && !nested || m.Label != nil && label != nil && m.Label.Name == label.Name) {
					found = true
				}
			case *ast.ForStmt, *ast.RangeStmt, *ast.SwitchStmt, *ast.TypeSwitchStmt, *ast.SelectStmt:
				if m != n {
					walk(m, true)
					return false
				}
			}
			return true
		})
	}
	walk(body, false)
	return found
}
