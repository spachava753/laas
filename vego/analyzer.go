// Package vego is a deductive verifier for Go. A function states what it
// must do in // @ comments, and vego proves that it does so for every input,
// or reports the obligation it could not prove. It follows the VeGo paper
// (Masoudi and Dutchyn, "VeGo: A Lightweight Deductive Verification System
// for Go", arXiv:2608.22630): specifications live in comments, so an
// annotated file stays ordinary Go.
//
//	// Divide computes quotient and remainder by repeated subtraction.
//	//
//	// @Requires n >= 0 And d > 0
//	// @Ensures n = d*q + r And 0 <= r And r < d
//	func Divide(n, d int) (q, r int) {
//		q, r = 0, n
//		// @Invariant n = d*q + r And 0 <= r
//		// @Variant r
//		for d <= r {
//			q, r = q+1, r-d
//		}
//		return q, r
//	}
//
// vego is experimental. It is built to accept only what is true, and much
// ordinary Go is still outside what it supports.
//
// # Running it
//
// The package provides [Analyzer], a go/analysis analyzer. The command
// github.com/spachava753/laas/cmd/laas runs it together with the other
// analyzers of the module:
//
//	laas ./...
//
// A function is verified when it carries at least one annotation; every
// other function is left alone. vego does not run under go vet -vettool,
// whose cache does not know about trust files; see [RefuseCachedRuns].
//
// # What is proved
//
// For an annotated function, from any state that satisfies its Requires
// clauses: every return establishes the Ensures clauses; every Assert
// holds; every loop keeps its Invariant and terminates by its Variant, and
// every recursive call decreases the function's Variant; no index is out of range, no
// nil pointer is followed, no divisor is zero, no integer operation
// overflows, and no panic is reachable; nothing a caller can see is written
// except what the Modifies clauses list; and every call goes to a function
// with a contract, whose Requires the caller proves and whose Ensures it
// may then rely on.
//
// The function is executed symbolically, and each obligation is written as
// an SMT-LIB problem and handed to Z3, which runs as a separate program; see
// the internal solver package. An obligation is proved only when Z3 shows
// that its negation has no model. Z3 may fail to prove something true; an
// Assert with an intermediate step or a stronger invariant usually helps.
//
// # Z3
//
// vego uses exactly the version of Z3 named by the internal solver
// package, 5.4.1, and refuses any other, since another version may prove
// different things. It is looked up only for a package that has something
// to prove, as z3 on PATH or at the path -vego.z3 names. Without it such a
// package fails with an error that says how to install it.
//
// # Annotations
//
// An annotation is a comment line of the form "// @Keyword ...", with one
// space between the slashes and the @ and none after it. In the doc comment of a function:
// Requires, Ensures, Modifies, and, for a recursive function, Variant.
// Directly above a loop: Invariant and Variant. Anywhere in a body: Assert.
// In the doc comment of a struct type: Invariant. At the top level:
// Predicate, which names a formula. A contract refers to the results of a
// function by their names, so a verified function names all of them.
// docs/verification.md in the module is a guide to writing verified Go. It
// describes the language of the formulas and each annotation in full.
//
// # Calling code that is not verified
//
// Verified code may only call a function that has a contract: one that is
// itself verified, or one with a trusted contract in the file named by
// [TrustFileName], next to go.mod. A trusted contract is used and not
// checked, so that file holds every assumption a proof rests on.
// [TrustReport] lists what the proofs of a set of packages take on trust.
//
// # Flags
//
// The analyzer has these flags, prefixed with the analyzer name when it is
// run by a multichecker:
//
//	-vego.audit       also probe each contract with degenerate implementations
//	-vego.rlimit      Z3's resource limit for one obligation
//	-vego.trusted     path of the trust file, instead of the one next to go.mod
//	-vego.z3          path of the Z3 binary, instead of the z3 on PATH
//
// The laas command adds -vego.trust, which prints the trust report.
package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"iter"
	"maps"
	"path/filepath"
	"reflect"
	"regexp"
	"slices"
	"sort"
	"strings"
	"sync"
	"time"
	"unicode"
	"unicode/utf8"

	"github.com/spachava753/laas/vego/internal/logic"
	"github.com/spachava753/laas/vego/internal/solver"
	"golang.org/x/tools/go/analysis"
	"golang.org/x/tools/go/ssa"
)

// Analyzer verifies annotated functions and reports every proof obligation it
// cannot discharge.
var Analyzer = newAnalyzer()

// refuseCache makes the analyzer decline to verify; see RefuseCachedRuns.
var refuseCache bool

// RefuseCachedRuns must be called by a driver whose results are cached by
// something that does not know about trust files, as go vet does with its
// -vettool. Such a cache would keep a proof, and the contract a package
// published from it, after the trusted contracts it rests on have changed.
// The analyzer then verifies nothing and reports every package that has
// annotations instead.
func RefuseCachedRuns() { refuseCache = true }

// observers holds, by analyzer, what tests are told of each package the
// analyzer verified: the costs of its functions, which the tests of the
// corpus compare with a table, and the verifier, whose instantiations a test
// reads. Keying them by the analyzer keeps tests that run side by side from
// seeing each other's packages.
var observers sync.Map // *analysis.Analyzer to *observer

type observer struct {
	costs    func(pass *analysis.Pass, costs []*fnCost)
	verifier func(pv *pkgVerifier)
}

// testCache is the default of -vego.cache, which only the tests set: from
// VEGO_CACHE, so that a run of the tests without it never depends on what a
// directory holds.
var testCache string

// newAnalyzer builds the analyzer with its flags. A run loads the trusted
// contracts, collects the annotations of the package, verifies every
// annotated function, applies the always-fails rule, and publishes the
// verified contracts and the trust the proofs rest on. For a caching driver
// it only reports that nothing was verified.
func newAnalyzer() *analysis.Analyzer {
	effort, audit, trustPath, otherTags, z3Path, printCost, cacheDir, ahead := 0, false, "", "", "", false, "", true
	analyzer := &analysis.Analyzer{
		Name: "vego",
		Doc: `verifies functions against their // @ specifications

vego proves that functions annotated with // @Requires, // @Ensures,
// @Modifies, // @Invariant, // @Variant, and // @Assert comments
meet their contracts, terminate, write only what they say they write, and
cannot index out of bounds, follow a nil pointer, divide by zero, or reach a
panic. Functions without annotations are not analyzed. With the audit flag
it also reports postconditions weak enough for a degenerate implementation.`,
		URL: "https://github.com/spachava753/laas#vego",
	}
	analyzer.Flags.IntVar(
		&effort,
		"rlimit",
		solver.DefaultEffort,
		"Z3 resource limit (rlimit) for one proof obligation",
	)
	analyzer.Flags.StringVar(
		&z3Path,
		"z3",
		"",
		"path of the Z3 "+solver.Version+" binary, instead of the z3 found on PATH",
	)
	analyzer.Flags.StringVar(
		&cacheDir,
		"cache",
		testCache,
		"directory that keeps the answers of Z3 between runs, outside any module or repository; off when empty",
	)
	analyzer.Flags.BoolVar(
		&ahead,
		"speculate",
		true,
		"verify functions of a package ahead on Z3 processes that would be idle, which changes only the time; false saves the memory of up to three more verifiers",
	)
	analyzer.Flags.BoolVar(
		&audit,
		"audit",
		false,
		"also report postconditions that degenerate implementations satisfy",
	)
	analyzer.Flags.StringVar(
		&trustPath,
		"trusted",
		"",
		"file of trusted contracts to use instead of "+TrustFileName+" next to go.mod",
	)
	analyzer.Flags.BoolVar(
		&printCost,
		"cost",
		false,
		"print what verifying each function asked of Z3, and where questions stopped at a limit, on standard error",
	)
	analyzer.Flags.StringVar(
		&otherTags,
		"other-tags",
		"",
		"comma-separated words that other tools read after \"// @\", as in Summary,Param; any other unknown word there is an error",
	)
	analyzer.ResultType = reflect.TypeFor[*Usage]()
	analyzer.FactTypes = []analysis.Fact{new(contractFact), new(predicatesFact), new(usageFact), new(invariantFact), new(sentinelsFact), new(sentinelWritesFact), new(sentinelRelianceFact), new(stateFact), new(ownsFact), new(fixedFact), new(coversFact), new(writesFact), new(initialisersFact)}
	analyzer.Run = func(pass *analysis.Pass) (result any, err error) {
		foreignTags, err := parseOtherTags(otherTags)
		if err != nil {
			return nil, err
		}
		if effort <= 0 || effort > solver.MaxEffort {
			return nil, fmt.Errorf("-vego.rlimit must be from 1 to %d, not %d", solver.MaxEffort, effort)
		}
		// A package that has something to prove and no Z3 to prove it with
		// fails as a whole, and so does one for which Z3 failed.
		defer func() {
			switch r := recover().(type) {
			case nil:
			case solverUnavailable:
				result, err = nil, r.err
			case *solver.Fault:
				result, err = nil, fmt.Errorf("Z3 failed: %v", r)
			case *solver.CacheError:
				result, err = nil, r
			case *solver.InternalError:
				result, err = nil, r
			case logic.TooLarge:
				result, err = nil, fmt.Errorf("a formula built for an annotation of the package has grown beyond %d nodes, which is the limit", logic.MaxSize)
			default:
				panic(r)
			}
		}()
		// verifier makes the verifier of the package for a pass, which
		// is the package's own or that of a speculative verifier.
		verifier := func(pass *analysis.Pass) *pkgVerifier {
			return &pkgVerifier{
				otherTags:       foreignTags,
				pass:            pass,
				info:            pass.TypesInfo,
				res:             logic.NewResolver(),
				funcs:           map[*types.Func]*funcInfo{},
				reported:        map[string]bool{},
				outcomes:        map[*funcInfo]*outcome{},
				trusted:         map[*types.Func]*funcInfo{},
				origins:         map[*ast.BlockStmt]*origins{},
				knownReturns:    map[*funcInfo]bool{},
				isParameter:     map[*types.Var]bool{},
				invariants:      map[*types.TypeName]*invariantSet{},
				funcTypes:       map[*types.TypeName]*funcInfo{},
				importedTypes:   map[*types.TypeName]*funcInfo{},
				ifaceMethods:    map[*types.Func]*funcInfo{},
				importedMethods: map[*types.Func]*funcInfo{},
				typeEntries:     map[string]*funcInfo{},
				unentered:       map[string]bool{},
				ownStates:       map[*types.TypeName][]ifaceState{},
				foreignBroken:   map[*types.Package]bool{},
				imported:        map[*types.Func]*funcInfo{},
				foreign:         map[*types.Package]*logic.Resolver{},
				plain:           logic.NewResolver(),
				trustSources:    map[*trustFile]*token.File{},
				z3Path:          z3Path,
				cacheDir:        cacheDir,
				effort:          effort,
				printCost:       printCost,
			}
		}
		pv := verifier(pass)
		if refuseCache {
			pv.usage = &Usage{}
			pv.collect()
			// A package without annotations has nothing to verify and
			// draws no report.
			for _, fn := range pv.order {
				if fn.annotated() {
					pv.report(fn.decl.Name.Pos(), "verification does not run under go vet, whose cache would keep "+
						"proofs after the trusted contracts they rest on have changed; run laas directly")
					break
				}
			}
			return pv.usage, nil
		}
		pv.loadTrust(trustPath)
		pv.collect()
		var sp *speculation
		if ahead && countFuncs(pv.order, func(fn *funcInfo) bool { return fn.annotated() && !fn.broken }) >= 2 {
			sp = speculate(pass, verifier, trustPath)
		}
		pv.checkInvariantsDeclared()
		pv.checkGroupsInitialised()
		pv.checkValueInitialisers()
		if sp != nil {
			// What the initialisers showed, for the speculative verifiers,
			// which take it instead of asking Z3 the same again.
			sp.inits = &initResults{why: maps.Clone(pv.initWhy), inert: maps.Clone(pv.inert), facts: maps.Clone(pv.initFacts),
				loggerMade: maps.Clone(pv.loggerMade), loggerInert: maps.Clone(pv.loggerInert)}
			close(sp.initialised)
		}
		pv.exportInvariants()
		// What the types of this package own, for importing packages.
		for _, name := range pv.ownsOrder {
			if decl := pv.ownsSource[name]; !decl.broken {
				pv.pass.ExportObjectFact(name, &ownsFact{Fields: decl.fields})
			}
		}
		pv.checkTypeContracts()
		pv.exportTypeContracts()
		pv.exportStates()
		if verifying != nil {
			verifying(pv, "begin")
		}
		for i, fn := range pv.order {
			// A speculative verifier takes no function the verification
			// has begun.
			if sp != nil {
				sp.at.Store(int64(i))
			}
			if !fn.annotated() || fn.broken {
				continue
			}
			pv.verified(fn)
			if audit {
				pv.run(fn, (*fnVerifier).audit)
			}
		}
		if verifying != nil {
			verifying(pv, "end")
		}
		// The speculative verifiers of the package stop before it is
		// reported, so that an error they met, which nobody else reads,
		// fails the package; see end.
		if sp != nil {
			if err := sp.end(); err != nil {
				panic(err)
			}
		}
		if err := sp.untrusted(pv.z3); err != nil {
			panic(err)
		}
		pv.exportContracts(pv.reportAlwaysFailing())
		pv.reportSentinelWrites()
		pv.noteLookups()
		if pv.printCost {
			pv.printCosts(costStderr)
		}
		pv.noteStored(costStderr)
		if found, ok := observers.Load(analyzer); ok {
			o := found.(*observer)
			if o.costs != nil {
				o.costs(pass, pv.costOrder)
			}
			if o.verifier != nil {
				o.verifier(pv)
			}
		}
		// The proofs of this package also rest on whatever the packages it
		// depends on took on trust.
		pass.ExportPackageFact(&usageFact{Usage: *pv.usage})
		total := &Usage{}
		total.add(pv.usage)
		for _, published := range pass.AllPackageFacts() {
			if dependency, ok := published.Fact.(*usageFact); ok && published.Package != pass.Pkg {
				total.add(&dependency.Usage)
			}
		}
		pv.reportTwoEntries(total)
		return total, nil
	}
	return analyzer
}

// clause is one annotation: a keyword followed by a formula, possibly
// continued over several comment lines.
type clause struct {
	kind string
	text string
	pos  token.Pos
	// misplaced is set, in place of a kind, for something that looks like
	// an annotation but is written where annotations are not read.
	misplaced string
	node      *logic.Node
	// snapshot is the name a Snapshot clause gives its value, which node is.
	snapshot string
	// res is set for a clause written in another package, which has its
	// own predicates.
	res *logic.Resolver
}

// funcInfo is a function declaration together with its bound annotations.
type funcInfo struct {
	decl        *ast.FuncDecl
	obj         *types.Func
	requires    []*clause
	ensures     []*clause
	measure     *clause
	body        []*clause // Invariant, Variant, and Assert clauses in source order
	params      []*types.Var
	results     []*types.Var
	paramNames  map[string]*types.Var
	resultNames map[string]int
	// runs holds the parameters of a trusted function whose code its
	// contract says it may run.
	runs byParam[bool]
	// keeps holds, for each parameter of a trusted function whose code its
	// contract says it keeps, the results and parameters it keeps it in;
	// see keeps.go.
	keeps byParam[[]string]
	// vouches holds the indices of the error results of a trusted function
	// whose errors its contract vouches for, or, for a contract of a type,
	// those a Vouches annotation lists; see knownError. vouchClauses holds
	// those annotations.
	vouches      map[int]bool
	vouchClauses []*clause
	// formatted is the parameter of a trusted function whose values its
	// contract says it formats as package fmt does, and format the string
	// it uses as the format, if any; see formatting.go.
	formatted, format *types.Var
	// encoded is the parameter of a trusted function whose value its
	// contract says it encodes as package encoding/json does; see json.go.
	encoded *types.Var
	// decoded is the parameter of a trusted function into which its
	// contract says it decodes as package encoding/json does, and
	// decodedFrom the []byte it decodes; see jsondecode.go.
	decoded, decodedFrom *types.Var
	// prints is the writer parameter of a trusted function that formats,
	// to which it writes, with one call of Write, what printsAs, a function
	// of its package, returns for its other arguments; see prints.go.
	prints   *types.Var
	printsAs *types.Func
	// vouchedWrites holds the parameters of a trusted function under
	// whose memory its contract vouches for the function values and
	// interface values it writes.
	vouchedWrites byParam[bool]
	// calls holds the contracts a trusted function gives its function
	// parameters; see callbacks.go.
	calls  byParam[*callback]
	broken bool // an annotation failed to parse; verification is skipped
	// genericTypes is set for the contract of an instantiation of a
	// generic function: the type of each of its parameters and results,
	// and of the parameters its calls names, in the generic signature;
	// see throughTypeParam.
	genericTypes map[*types.Var]types.Type
	// faulted is set for the contract of a type or of a method of an
	// interface that was refused for something other than a clause that
	// cannot be read, as a contradiction; see viewOf.
	faulted bool
	// modifies lists what the function may write, from its Modifies clauses.
	modifies []*modTarget
	// trust is set for a function whose contract comes from a trust file
	// instead of annotations; such a function is not verified.
	trust   *trustEntry
	defects []string  // what is wrong with a trusted or imported contract
	// atTypes holds the defects found at the types of the parameters; see
	// typeDefect.
	atTypes map[string]bool
	use     *EntryUse // the report entry of a trusted contract in use
	// receiver is set for the contract of a method of an interface that
	// names its receiver, with a Receiver annotation or receiver in an entry, so that
	// the contract can speak of its states; see ifacestate.go. It is not
	// among params.
	receiver *types.Var
	// imported is set for a function verified in another package, whose
	// contract was published by that package.
	imported *contractFact
	// failed is set when verifying the function reported a problem, and
	// reportedHere when one of them lies in its declaration.
	failed       bool
	reportedHere bool
	// forces caches whether a trusted contract forces success for some
	// input; see forcesSuccess.
	forces *bool
	// valueOf is set for the contract of a named function type, which a
	// call through a value of the type is checked against; see
	// funcvalues.go. Such a contract is not verified, and is treated where
	// that matters like a trusted one.
	valueOf *types.TypeName
	// methodOf is set for the contract of a method of an interface type,
	// which a call of the method through an interface value is checked
	// against; see interfaces.go. Like the contract of a function type, it
	// is not verified, and is treated where that matters like a trusted
	// one.
	methodOf *types.Func
	// ownParams is set for a function literal verified against the
	// contract of a function type: the contract names its parameters as the
	// type does, and old(x) in its body names its own parameter x.
	ownParams map[string]*types.Var
	// spelled is set for a function literal verified against the contract
	// of a function type: the names in that contract other than its
	// parameters and results mean what they mean where the contract was
	// written, in the package that declares the type or in a trust file.
	spelled *funcInfo
}

// spelling returns the contract whose clauses a function's annotations
// were written as: the contract of the type a literal is made into, or the
// function's own.
func (f *funcInfo) spelling() *funcInfo {
	if f.spelled != nil {
		return f.spelled
	}
	return f
}

// writtenIn returns the package whose source or trust file the contract of
// a function was written in, which decides the unexported fields it may
// name; nil for a contract shipped with vego, which may name none.
func (f *funcInfo) writtenIn() *types.Package {
	f = f.spelling()
	switch {
	case f.trust != nil && f.trust.file != nil && f.trust.file.shipped:
		return nil
	case f.valueOf != nil:
		return f.valueOf.Pkg()
	case f.methodOf != nil:
		return f.methodOf.Pkg()
	}
	return f.obj.Pkg()
}

func (f *funcInfo) annotated() bool {
	return len(f.requires)+len(f.ensures)+len(f.body)+len(f.modifies) > 0 || f.measure != nil
}

type pkgVerifier struct {
	pass     *analysis.Pass
	info     *types.Info
	res      *logic.Resolver
	funcs    map[*types.Func]*funcInfo
	order    []*funcInfo
	reported map[string]bool
	// reports counts the calls of report, a repeated report included,
	// which tells whether a stretch of verification met one.
	reports int
	// instances holds the instantiations of each generic function that
	// calls in the package make, and instanceOf what is known of each by
	// its function object; see generics.go.
	instances  map[*types.Func][]*instance
	instanceOf map[*types.Func]*instance
	// encoderInners holds the calls json.NewEncoder(w) that are the
	// receiver of an Encode written in the same expression; see json.go.
	encoderInners map[*ast.CallExpr]bool
	// z3Path names the Z3 binary, z3 the solver once started, and effort
	// the resource limit of a proof.
	z3Path string
	z3     *solver.Solver
	effort int
	// cacheDir is the directory of the answer cache, or "" for none.
	cacheDir string
	// speculative is set for a verifier that only fills the solver's
	// cache; stopSpeculation reports when its package is verified, and
	// speculationStop is closed then; see speculate.go.
	speculative     bool
	stopSpeculation func() bool
	speculationStop <-chan struct{}
	// searchLimit is the last limit a question of a search for an input
	// stopped at while the current function was verified, and searching
	// counts the searches under way.
	searchLimit solver.Result
	searching   int
	// costs holds what verifying each function has asked of Z3, in
	// costOrder in the order first asked; costFn is the function that
	// questions count against now, askAt the place they come from, and
	// purpose their kind when purposeSet; nested is the time spent on
	// other functions since costFn was set. See cost.go.
	costs      map[*funcInfo]*fnCost
	costOrder  []*fnCost
	costFn     *funcInfo
	askAt      token.Pos
	purpose    question
	purposeSet bool
	nested     time.Duration
	// printCost is set by -vego.cost.
	printCost bool
	// otherTags holds the words that the user declared to be read by other
	// tools when they follow "// @".
	otherTags map[string]bool
	outcomes  map[*funcInfo]*outcome
	// projectTrust is the project's file of trusted contracts, trusted the
	// contracts built from it and from the shipped ones, and usage what the
	// proofs of this package rely on.
	projectTrust *trustFile
	trusted      map[*types.Func]*funcInfo
	trustSources map[*trustFile]*token.File
	usage        *Usage
	// imported holds the contracts of functions verified in other
	// packages, and foreign the predicates of those packages.
	imported map[*types.Func]*funcInfo
	foreign  map[*types.Package]*logic.Resolver
	// plain resolves trusted contracts, which may use no predicates.
	plain *logic.Resolver
	// predicateTexts are the predicate definitions of this package, and
	// predicatesBroken is set when one of them could not be accepted.
	// foreignBroken holds the packages whose predicates could not be read.
	predicateTexts   []string
	predicatesBroken bool
	// unread is set when collecting the annotations of the package drew a
	// report: a comment looked like an annotation and was not read as one,
	// or a clause was dropped or stood where it has no effect.
	unread        bool
	foreignBroken map[*types.Package]bool
	// current is the function being verified, which a diagnostic counts
	// against.
	current *funcInfo
	// sentinels are the stable error variables of the package that hold a
	// sentinel of this package or a variable of another, and so no code of
	// this package; reliedKeys holds the keys of the error variables a proof
	// has relied on. unsettled holds the stable variables that would be
	// usable if no code of the package could run before they are
	// initialised, with what stands in the way.
	sentinels  map[*types.Var]bool
	reliedKeys map[string]bool
	// writes holds the assignments to error variables of other packages
	// and the places that take their address, and buildWrites those of
	// this package and of every package it is built with, by key; see
	// writtenInBuild.
	writes      []sentinelWrite
	buildWrites map[string]sentinelWrite
	// candidates holds what is known of the stable variables of the
	// package, whether or not code of the package can run before they are
	// set; published holds what other packages published of theirs.
	candidates map[*types.Var]sentinelInfo
	published  map[*types.Package]*sentinelsFact
	// homemade holds the sentinels whose origin is known: nothing but plain
	// values and other such sentinels went into the error.
	homemade  map[*types.Var]bool
	unsettled map[*types.Var]string
	// reassigned holds the package-level variables that the package
	// changes, changeOf says for each how and where first, and ownChanges
	// the same for those of the package; escapes says where a use first
	// does more than read a value out of a variable. See findChanges.
	reassigned map[*types.Var]bool
	// addressSite holds, for each variable whose address the package
	// takes, where it first does.
	addressSite map[*types.Var]string
	// openAt holds, for each variable whose address the package takes in
	// a way that is not closed, why, at the first such use.
	openAt map[*types.Var]string
	// addressRuns holds, for a variable whose address is closed, where a
	// sink runs a function it is handed while it has the address; runsAt
	// is where the use being classified does.
	addressRuns map[*types.Var]string
	runsAt      string
	changeOf   map[*types.Var]string
	ownChanges map[*types.Var]string
	escapes    map[*types.Var]string
	// changeKinds holds, for each package-level variable the build
	// changes, how: assigned, its address taken, named by a directive or
	// from assembly (see assigned.go).
	changeKinds map[*types.Var]changeKind
	// asValues holds the functions of the package named other than as the
	// function of a call; see callableElsewhere.
	asValues map[types.Object]bool
	// ownCovers is what the state of the package covers; see covers.
	ownCovers []string
	// varGroups are the groups of package-level variables with invariants,
	// groupOf the group of each variable, and touched the groups each
	// function touches (varinv.go).
	varGroups []*varGroup
	groupOf   map[*types.Var]*varGroup
	touched   map[*funcInfo][]*varGroup
	touchedAt map[*callNode]map[*varGroup]bool
	// touchedAtBoundary holds, for each node, the groups that a function it
	// may reach touches, of those that code outside the package's verified
	// code can enter; see lockBoundary.
	touchedAtBoundary map[*callNode]map[*varGroup]bool
	// letOutNodes are the code of the package that it lets out into memory
	// it did not make; see letOut.
	letOutNodes []*callNode
	letOutDone  bool
	// initWhy holds, for each variable whose initialiser checkValueInitialisers
	// checked and found wanting, why, which a read of the variable reports;
	// initOf what other packages published of theirs. capturing, when set,
	// takes the reports of such a check in place of the pass.
	initWhy   map[*types.Var]string
	initOf    map[*types.Package]*initialisersFact
	capturing *[]string
	// initFacts holds, for each fixed variable of the package whose
	// initialiser runs as code, what the run shows of its value; see
	// initcalls.go.
	initFacts map[*types.Var][]*logic.Term
	// initFactsOf holds what other packages published of the initialisers
	// of their variables, rebuilt; see publishedInitFacts.
	initFactsOf map[*types.Var][]*logic.Term
	// initRunning is set while an initialiser runs as code, which reads
	// only variables Go initialised before it, whatever hidden init code
	// may run.
	initRunning bool
	// loggerMade, loggerInert, and loggerUse hold, for each logger in a
	// variable, that its initialiser is a call of log.New that verified,
	// whether the writer it gives is inert, and why it cannot be read; see
	// loggers.go.
	loggerMade, loggerInert map[*types.Var]bool
	loggerUse               map[*types.Var]string
	// inert holds the variables whose checked initialiser converts a value
	// whose footprint stays empty and that has no states; see inertFixed.
	inert map[*types.Var]bool
	// fixed holds what is known of the package-level variables of the
	// package that are not errors and that nothing changes, fixedOf what
	// other packages published of theirs, and hidden the code that may run
	// while the variables of the package are initialised, or ""; see
	// findFixed. reliedValues holds the keys of such variables whose
	// values a proof has relied on.
	fixed    map[*types.Var]knownValue
	readOnly map[*types.Var]bool
	// readOnlyRefs holds, by the name of the constant of its reference,
	// the key of each variable whose contents are only read and that a
	// function has read; see table.
	readOnlyRefs map[string]string
	// fixedRefs holds, by the name of its constant, the reference of a
	// fixed variable that a function has read, with the variable as this
	// package spells it; see checkWriteOr.
	fixedRefs map[string]string
	// returnedBy holds, by the name of its constant, the reference of a
	// pointer or slice that a trusted function returned, with the name of
	// the function; see checkWriteOr.
	returnedBy   map[string]returned
	fixedOf      map[*types.Package]*fixedFact
	hidden       string
	reliedValues map[string]bool
	// namedByContract caches the package-level variables each contract
	// names; see contractVariables.
	namedByContract map[*funcInfo][]*types.Var
	// origins caches what the variables of each function body are assigned,
	// knownReturns holds the functions that only return errors of known
	// origin, and isParameter the parameters of all functions.
	origins      map[*ast.BlockStmt]*origins
	knownReturns map[*funcInfo]bool
	isParameter  map[*types.Var]bool
	// invariants holds the invariants of struct types, nil for a type known
	// to have none.
	invariants map[*types.TypeName]*invariantSet
	// funcTypes holds the contracts of the named function types of this
	// package, and importedTypes those of other packages, nil for a type
	// known to have none; mayCall caches whether running a function may
	// make a call through a function value. See funcvalues.go.
	funcTypes     map[*types.TypeName]*funcInfo
	importedTypes map[*types.TypeName]*funcInfo
	mayCall       map[*types.Func]bool
	// summaries holds what each verified function of the package returns
	// and stores, by where it came from; see memSummary.
	summaries map[*types.Func]memSummary
	// ownSummaries are the summaries of ownership; see ownSummaryOf.
	ownSummaries map[*types.Func]*ownSummary
	// valueReasons holds, for a function of this package that may make a
	// call through a value, why; see valueReason.
	valueReasons map[*types.Func]valueReason
	// ifaceMethods holds the contracts of the methods of the interface
	// types of this package, and importedMethods those of other packages,
	// nil for a method known to have none. See interfaces.go.
	ifaceMethods    map[*types.Func]*funcInfo
	importedMethods map[*types.Func]*funcInfo
	// typeEntries holds the contracts that the trust files give methods of
	// interface types and function types, by key, nil for a key with none;
	// see typeentries.go.
	typeEntries map[string]*funcInfo
	// lookedUp holds the type entries the package looked up and could use,
	// and unentered the keys it looked up and found no entry for, with
	// whether the type is of this module; see noteLookups.
	lookedUp  []*funcInfo
	unentered map[string]bool
	// ownStates holds the states that interface types declare themselves,
	// by type, nil for one that declares none, and stateUses the state
	// declarations of trust files the package looked up; see
	// ifacestate.go.
	ownStates map[*types.TypeName][]ifaceState
	stateUses []*EntryUse
	// importedStateNames holds the names of the states that the facts of
	// other packages declare.
	importedStateNames map[string]bool
	// conversions lists the conversions to interface types in the package,
	// once something asks; see conversions.go.
	conversions *conversions
	// copies holds what go/ssa copies of values that hold a state, by
	// function; see findCopies.
	copies map[*ast.FuncDecl][]ssaCopy
	// ssaProg is the package built in go/ssa; see ssaProgram.
	ssaProg *ssa.Program
	// graph is the call graph of the package; see callgraph.go.
	graph *callGraph
	// views holds what a use of each contract may rely on; see viewOf.
	views map[*funcInfo]*contractView
	// caseTails holds the annotations that follow the last statement of a
	// case clause, with that clause; see scopeAt.
	caseTails map[token.Pos]*ast.CaseClause
	// snapshotEnds holds where the scope of each Snapshot ends; see
	// snapshotScope.
	snapshotEnds map[*clause]token.Pos
	// below holds the statement directly below each annotation of a body
	// that one was looked for; see statementAfter.
	below map[*clause]ast.Stmt
	// assignedIn holds, for the body of each declared function, the
	// variables that something other than their declaration assigns; see
	// final.
	assignedIn map[*ast.BlockStmt]map[*types.Var]bool
	// ownsSource holds the Owns declarations of the package while it is
	// collected, in ownsOrder; see owns.go.
	ownsSource map[*types.TypeName]*ownsDeclSource
	ownsOrder  []*types.TypeName
}

// report emits a diagnostic once per position and message. Symbolic execution
// visits a statement once per path, so the same failure can be found often.
func (pv *pkgVerifier) report(pos token.Pos, format string, args ...any) {
	if pv.capturing != nil {
		at := pv.pass.Fset.Position(pos)
		*pv.capturing = append(*pv.capturing, fmt.Sprintf("%s:%d:%d\x00%s", filepath.Base(at.Filename), at.Line, at.Column, fmt.Sprintf(format, args...)))
		return
	}
	pv.reports++
	if pv.current != nil {
		pv.current.failed = true
		// A report within the declaration, its doc comment included, is
		// one of the function's own.
		if decl := pv.current.decl; decl != nil {
			start := decl.Pos()
			if decl.Doc != nil {
				start = decl.Doc.Pos()
			}
			if start <= pos && pos < decl.End() {
				pv.current.reportedHere = true
			}
		}
	}
	msg := "vego: " + fmt.Sprintf(format, args...)
	key := fmt.Sprintf("%d %s", pos, msg)
	if pv.reported[key] {
		return
	}
	pv.reported[key] = true
	pv.pass.Report(analysis.Diagnostic{Pos: pos, Message: msg})
}

var (
	// Space is any character that looks like one, so that an annotation
	// behind a no-break space is not taken for an ordinary comment.
	annotationLine = regexp.MustCompile(`^//([\s\p{Z}]*)@([\s\p{Z}]*)(.*)$`)
	// anyAnnotation finds the word after an @ wherever it stands, with
	// whatever is not a letter in between.
	anyAnnotation = regexp.MustCompile(`@[^\pL]*(\pL+)`)
	// leadingAt finds an @ that is the first thing on a line but for signs,
	// with the word that follows it.
	leadingAt   = regexp.MustCompile(`(?m)^[^\pL\pN@\n]*@[^\pL\pN\s]*(\S*)`)
	clauseKinds = map[string]bool{
		"Requires": true, "Ensures": true, "Invariant": true, "Variant": true,
		"Predicate": true, "Assert": true, "Modifies": true, "State": true, "Receiver": true, "Snapshot": true, "Vouches": true,
		"Visited": true, "Owns": true,
	}
	// retiredKinds are keywords that earlier versions read, with what to
	// write now.
	retiredKinds = map[string]string{"Measure": "Variant"}
	// plannedKinds are annotations of the VeGo paper that this implementation
	// does not support yet.
	plannedKinds = map[string]bool{"Preserves": true, "Immutable": true, "Cost": true, "Library": true}
)

// extractClauses splits a comment group into annotation clauses. A line that
// starts with a keyword opens a clause, and following annotation lines that do
// not start with a keyword continue it. An annotation is written
// "// @Keyword ...", a form gofmt leaves alone, and a line that continues one
// "// @ ...". Any other spacing is reported, so that there is one form to look
// for. A //
// inside an annotation line starts an ordinary comment.
//
// Whatever follows "// @" is taken to be meant for this tool, so an unknown
// word there is returned as a clause without a kind, to be reported,
// instead of being skipped: a keyword that is wrong must not switch
// verification off by passing for the tag of another tool. The words that
// other tools do read there, as in "// @Summary", have to be declared with
// the other-tags flag, and are then ordinary comment. A keyword in a /* */
// comment is reported too, since annotations are only read from //
// comments, and so is an @ with a keyword that is not at the start of its
// line, and an ordinary comment line directly after an annotation, which
// its author may have meant as the rest of it.
func extractClauses(group *ast.CommentGroup, otherTags map[string]bool) []*clause {
	var clauses []*clause
	var current *clause
	for _, comment := range group.List {
		// A character that takes no room, such as a zero-width space, is
		// not there for a reader, so it is not there when the scanner looks
		// for annotations. What a clause says is taken from the comment as
		// it is written, since such a character may be part of a string in
		// a formula.
		written := visible(comment.Text)
		// Some characters end a line on the screen and not for Go. Behind
		// one, an annotation looks as if it stood on a line of its own
		// while it is read as the rest of the line before it.
		// A carriage return is one of them, but Go takes every one of those
		// out of a comment before it gets here; see checkCarriageReturns.
		if strings.Contains(written, "@") && strings.ContainsAny(written, "\u2028\u2029\u0085\v\f") {
			clauses = append(clauses, &clause{pos: comment.Pos(),
				misplaced: "this comment has an @ and a character that ends a line on the screen but not for Go, such as U+2028; remove the character, so that what is read is what is seen"})
			current = nil
			continue
		}
		if strings.HasPrefix(written, "/*") {
			// A keyword after an @ anywhere in the comment, or any word
			// after one that starts a line.
			if stray(written) || leading(written, otherTags) {
				clauses = append(clauses, &clause{pos: comment.Pos(),
					misplaced: "annotations are only read from // comments, not from /* */ comments"})
			}
		}
		match := annotationLine.FindStringSubmatch(written)
		if match == nil {
			text := strings.TrimPrefix(written, "//")
			block := strings.HasPrefix(written, "/*")
			switch {
			case !block && (stray(text) || leading(text, otherTags)):
				clauses = append(clauses, &clause{pos: comment.Pos(),
					misplaced: `an annotation is written "// @Keyword ...", with nothing but one space between // and @`})
			case current != nil && (block || strings.TrimSpace(text) != ""):
				// A clause is continued with "// @", so this line would be
				// left out of it without a word.
				clauses = append(clauses, &clause{pos: comment.Pos(),
					misplaced: afterAnnotation})
			}
			current = nil
			continue
		}
		// The line as it is written, from where the @ and the space after
		// it end. Where the comment that ends the line begins is decided
		// there, so that a character that takes no room cannot make two
		// slashes out of what is written as something else.
		payload, trailing, _ := strings.Cut(comment.Text[unhidden(comment.Text, len(written)-len(match[3])):], "//")
		line, aside := strings.TrimSpace(visible(payload)), visible(trailing)
		// A tag that was declared to be another tool's makes the line an
		// ordinary comment, with all that holds for one: an annotation
		// further along it is out of place unless it is shown behind
		// slashes of its own, and the line may not follow an annotation
		// directly. A keyword of this language is never such a tag.
		if tag, letters := leadingWord(line); match[2] == "" && !protected(letters) && (otherTags[tag] || otherTags[letters]) {
			switch text := strings.TrimPrefix(written, "//"); {
			case stray(strings.Replace(text, "@", " ", 1)):
				clauses = append(clauses, &clause{pos: comment.Pos(),
					misplaced: `an annotation is written "// @Keyword ...", with nothing but one space between // and @`})
			case current != nil:
				clauses = append(clauses, &clause{pos: comment.Pos(), misplaced: afterAnnotation})
			}
			current = nil
			continue
		}
		// The comment an annotation line ends in is not read, so an
		// annotation written there would go unnoticed.
		if stray(aside) {
			clauses = append(clauses, &clause{pos: comment.Pos(),
				misplaced: `an annotation is written "// @Keyword ...", with nothing but one space between // and @`})
		}
		// The keyword is the run of letters the line starts with, so that
		// one written without a space before its formula is still one.
		word, keyword := leadingWord(line)
		known := clauseKinds[keyword] || plannedKinds[keyword] || retiredKinds[keyword] != ""
		switch {
		case match[1] != " ", known && match[2] != "":
			// One spelling: a space before the @, and the keyword directly
			// after it.
			current = nil
			clauses = append(clauses, &clause{pos: comment.Pos(),
				misplaced: `an annotation is written "// @Keyword ...", with one space before the @ and none after it`})
		case retiredKinds[keyword] != "":
			current = nil
			clauses = append(clauses, &clause{pos: comment.Pos(),
				misplaced: fmt.Sprintf("there is no %s annotation; write %s", keyword, retiredKinds[keyword])})
		case known:
			current = &clause{kind: keyword, text: strings.TrimSpace(payload[unhidden(payload, len(keyword)):]), pos: comment.Pos()}
			clauses = append(clauses, current)
		case current != nil && match[2] != "":
			// "// @ ..." continues the clause above it.
			current.text += " " + strings.TrimSpace(payload)
		case keyword == "" && stray("@"+match[3]):
			// Signs, or a second @, between the @ and a keyword.
			current = nil
			clauses = append(clauses, &clause{pos: comment.Pos(),
				misplaced: `an annotation is written "// @Keyword ...", with nothing but one space between // and @`})
		default:
			// Whatever else follows "// @" is taken to be meant for this
			// tool: a keyword that is wrong must not pass for the tag of
			// another tool and switch a check off.
			current = nil
			clauses = append(clauses, &clause{text: word, pos: comment.Pos()})
		}
	}
	return clauses
}

// visible returns a text without the characters that take no room.
func visible(text string) string {
	return strings.Map(func(r rune) rune {
		if unicode.Is(unicode.Cf, r) {
			return -1
		}
		return r
	}, text)
}

// withoutShown returns a comment text without the annotations it shows
// behind slashes of their own, and without the strings that follow such an
// annotation on its line: they belong to the formula being shown, and an @
// in one of them is no annotation. It goes through each line once, from the
// left, so that what is a string and what is not is decided as a reader
// decides it, a quote behind a backslash being part of its string.
func withoutShown(text string) string {
	var kept strings.Builder
	for n, line := range strings.Split(text, "\n") {
		if n > 0 {
			kept.WriteByte('\n')
		}
		shown, inString := false, false
		// No shown annotation starts before this place; it saves looking
		// again from every slash of a long run of them.
		none := 0
		for i := 0; i < len(line); {
			// An annotation may be shown inside a string, as in a sentence
			// that quotes the form; the string goes on after it.
			if i >= none && !(shown && inString) && strings.HasPrefix(line[i:], "//") {
				end, found := shownAt(line, i)
				if found {
					// A space stands for what is left out, so that the
					// words on its two sides stay two words.
					kept.WriteByte(' ')
					shown = true
					i = end
					continue
				}
				none = end
			}
			switch c := line[i]; {
			case inString && c == '\\' && i+1 < len(line):
				if !shown {
					kept.WriteString(line[i : i+2])
				}
				i += 2
			case inString || c == '"':
				// A string before any shown annotation is ordinary text,
				// and is kept; one after it is left out.
				if shown && !inString {
					kept.WriteByte(' ')
				}
				inString = !inString || c != '"'
				if !shown {
					kept.WriteByte(c)
				}
				i++
			default:
				kept.WriteByte(c)
				i++
			}
		}
	}
	return kept.String()
}

// shownAt looks for an annotation shown behind the two slashes at place i
// of a line: the slashes, then anything but letters, an @, and the word
// after it, if there is one. A quote or a backslash ends the search, so
// that a shown annotation never reaches out of a string or takes half of
// an escaped character with it. It returns where the shown annotation
// ends, or else how far it looked.
func shownAt(line string, i int) (end int, found bool) {
	j := i + 2
	for j < len(line) {
		r, size := utf8.DecodeRuneInString(line[j:])
		if r == '@' {
			break
		}
		if unicode.IsLetter(r) || r == '"' || r == '\\' {
			return j, false
		}
		j += size
	}
	if j >= len(line) {
		return j, false
	}
	j++
	letters := false
	for j < len(line) {
		r, size := utf8.DecodeRuneInString(line[j:])
		if r == '"' || r == '\\' || r == '@' || (letters && !unicode.IsLetter(r)) {
			break
		}
		letters = letters || unicode.IsLetter(r)
		j += size
	}
	return j, true
}

// unhidden returns how far into a text one gets by passing n bytes of it
// that are not of a character that takes no room: the place in the text as
// written that corresponds to place n in the text without such characters.
func unhidden(text string, n int) int {
	for i, r := range text {
		if n <= 0 {
			return i
		}
		if !unicode.Is(unicode.Cf, r) {
			n -= utf8.RuneLen(r)
		}
	}
	return len(text)
}

// afterAnnotation is the report for a comment that follows an annotation
// directly.
const afterAnnotation = `a comment directly after an annotation is not read as part of it; continue an annotation with "// @ ...", or put an empty // line before a comment`

// parseOtherTags reads the words that other tools read after "// @". A
// word that is a keyword of this language, or close enough to one to be a
// misspelling of it, cannot be declared: that would switch the report of
// the misspelling off.
func parseOtherTags(list string) (map[string]bool, error) {
	tags := map[string]bool{}
	for tag := range strings.SplitSeq(list, ",") {
		tag = strings.TrimSpace(tag)
		switch {
		case tag == "":
		case strings.ContainsFunc(tag, unicode.IsSpace) || strings.Contains(tag, "@"):
			return nil, fmt.Errorf("-vego.other-tags: %q is not a single word", tag)
		case !unicode.IsLetter([]rune(tag)[0]):
			return nil, fmt.Errorf("-vego.other-tags: %q does not start with a letter", tag)
		case protected(tag) || slices.ContainsFunc(strings.FieldsFunc(tag, func(r rune) bool { return !unicode.IsLetter(r) }), protected):
			return nil, fmt.Errorf("-vego.other-tags: %q is a keyword of vego's annotations or too close to one to be declared as another tool's", tag)
		default:
			tags[tag] = true
		}
	}
	return tags, nil
}

// leading reports whether a piece of comment text has a line that starts,
// but for signs, with an @ and a word that was not declared as another
// tool's. That is the place of an annotation with something small in the
// way, a third slash or the star of a block comment, so the word is judged
// as it would be after "// @": whatever it is, it is taken to be meant for
// this tool. An annotation that follows its own // is one being shown.
func leading(text string, otherTags map[string]bool) bool {
	shown := withoutShown(text)
	return slices.ContainsFunc(leadingAt.FindAllStringSubmatch(shown, -1), func(found []string) bool {
		_, letters := leadingWord(found[1])
		return protected(letters) || (!otherTags[found[1]] && !otherTags[letters])
	})
}

// checkCarriageReturns reports a carriage return that does not end a line
// together with a newline, in a file whose comments have an @. An editor
// may show what follows one as a line of its own, while Go reads on in the
// same line, so that an annotation behind it would look right and not be
// read. Go removes carriage returns from the text of a comment, so they
// are looked for in the file itself.
func (pv *pkgVerifier) checkCarriageReturns(file *ast.File) {
	if !slices.ContainsFunc(file.Comments, func(group *ast.CommentGroup) bool {
		return slices.ContainsFunc(group.List, func(c *ast.Comment) bool { return strings.Contains(c.Text, "@") })
	}) {
		return
	}
	position := pv.pass.Fset.File(file.Pos())
	content, err := pv.pass.ReadFile(position.Name())
	if err != nil {
		// What cannot be read again cannot be vouched for.
		pv.report(file.Pos(), "cannot read %s to look for line ends that are not shown as such: %v", position.Name(), err)
		return
	}
	for i, b := range content {
		if b == '\r' && (i+1 == len(content) || content[i+1] != '\n') && i < position.Size() {
			pv.report(position.Pos(i), "this file has annotations and a carriage return that does not end a line; "+
				"remove it, so that what is read is what is seen")
			return
		}
	}
}

// stray reports whether a piece of comment text has an @ followed by a
// keyword, or by something close to one, where no annotation is read. An
// annotation that follows its own //, as in an example in a doc comment, a
// message of this tool that a comment quotes, or a line that was commented
// out, is one being shown and does not count.
func stray(text string) bool {
	shown := withoutShown(text)
	return slices.ContainsFunc(anyAnnotation.FindAllStringSubmatch(shown, -1), func(found []string) bool {
		return plannedKinds[found[1]] || retiredKinds[found[1]] != "" || nearKeyword(found[1])
	})
}

// nearKeyword reports whether a word is an annotation keyword, or so close
// to one that it was most likely meant as one: the same but for case, or one
// or two letters away.
func nearKeyword(word string) bool {
	for keyword := range clauseKinds {
		if strings.EqualFold(word, keyword) || distance(word, keyword) <= 2 {
			return true
		}
	}
	return false
}

// protected reports whether a word belongs to this language beyond doubt,
// so that it cannot be declared as another tool's: a keyword or something
// near one, or a planned or retired keyword in any case.
func protected(word string) bool {
	if nearKeyword(word) {
		return true
	}
	for _, kinds := range []iter.Seq[string]{maps.Keys(plannedKinds), maps.Keys(retiredKinds)} {
		for keyword := range kinds {
			if strings.EqualFold(word, keyword) {
				return true
			}
		}
	}
	return false
}

// leadingWord returns what a line starts with up to the first space, and
// the run of letters it starts with, which is where a keyword would be: one
// written without a space before its formula is still one.
func leadingWord(line string) (word, letters string) {
	word, letters = line, line
	if end := strings.IndexFunc(line, unicode.IsSpace); end >= 0 {
		word = line[:end]
	}
	if end := strings.IndexFunc(line, func(r rune) bool { return !unicode.IsLetter(r) }); end >= 0 {
		letters = line[:end]
	}
	return word, letters
}

// distance returns how many letters have to be added, dropped, or replaced
// to turn one word into the other.
func distance(first, second string) int {
	// Letters, not bytes: a letter with an accent is one letter.
	a, b := []rune(first), []rune(second)
	row := make([]int, len(b)+1)
	for j := range row {
		row[j] = j
	}
	for i := 1; i <= len(a); i++ {
		diagonal := row[0]
		row[0] = i
		for j := 1; j <= len(b); j++ {
			above := row[j]
			if a[i-1] != b[j-1] {
				diagonal++
			}
			row[j] = min(diagonal, above+1, row[j-1]+1)
			diagonal = above
		}
	}
	return row[len(b)]
}

// collect records every function of the package, parses all annotations, and
// binds each clause to the function it specifies.
func (pv *pkgVerifier) collect() {
	// Whatever is reported while the annotations are collected is about an
	// annotation that was dropped, misread, or put where it has no effect.
	// The package is then not what its author wrote, so none of its
	// contracts is handed to other packages as verified; this holds for
	// every such report, also one that a later change adds here.
	before := len(pv.reported)
	defer func() {
		if len(pv.reported) > before {
			pv.unread = true
		}
	}()
	pv.importOwns()
	pv.ownsSource, pv.ownsOrder = nil, nil
	defer pv.checkOwnsDeclared()
	var predicates []*logic.PredDecl
	predicateClauses := map[*logic.PredDecl]*clause{}
	for _, file := range pv.pass.Files {
		for _, decl := range file.Decls {
			if fd, ok := decl.(*ast.FuncDecl); ok {
				pv.addFunc(fd)
			}
		}
		pv.checkCarriageReturns(file)
		for _, group := range file.Comments {
			for _, c := range extractClauses(group, pv.otherTags) {
				// An annotation that was not read may have been meant for
				// any function of the package, so none of them is handed
				// to other packages as verified.
				if c.misplaced != "" || c.kind == "" || plannedKinds[c.kind] {
					pv.unread = true
				}
				if c.misplaced != "" {
					pv.report(c.pos, "%s", c.misplaced)
					continue
				}
				if c.kind == "" {
					pv.report(c.pos, "unknown annotation %q; an annotation starts with one of "+
						"Requires, Ensures, Modifies, Invariant, Owns, Variant, Visited, Assert, Snapshot, Predicate, State, Receiver, Vouches. "+
						"If another tool reads this comment, declare the word with -vego.other-tags", c.text)
					continue
				}
				if plannedKinds[c.kind] {
					pv.report(c.pos, "%s annotations are not supported yet", c.kind)
					continue
				}
				if fd := enclosingFunc(file, c.pos); fd != nil && fd.Body != nil && localTypeAt(fd.Body, c.pos, c.kind == "Assert" || c.kind == "Snapshot") {
					// It may have been meant as the contract of anything
					// in the type; nothing reads it.
					pv.unread = true
					pv.report(c.pos, "%s annotation stands on a type declared inside %s; a type declared inside a function cannot have annotations, "+
						"so declare it at package level to give it an invariant or a contract", c.kind, fd.Name.Name)
					if fn := pv.funcs[pv.info.Defs[fd.Name].(*types.Func)]; fn != nil {
						fn.broken = true
					}
					continue
				}
				if method, defined, ok := pv.methodDocumented(file, group); ok {
					pv.addMethodContract(method, defined, c)
					continue
				}
				if name, ok := pv.typeDocumented(file, group); ok {
					switch {
					case name != nil && isFunc(name.Type().Underlying()):
						pv.addTypeContract(name, c)
					case c.kind == "State":
						pv.addState(name, c)
					case c.kind == "Owns" && name != nil:
						pv.addOwns(name, c)
					default:
						pv.addInvariant(name, c)
					}
					continue
				}
				switch c.kind {
				case "State":
					pv.report(c.pos, "a State annotation belongs in the doc comment of a defined interface type, as in // @State closed")
					continue
				case "Owns":
					pv.report(c.pos, "an Owns annotation belongs in the doc comment of a struct type, where it names the fields whose memory a value of the type owns, as in // @Owns items")
					continue
				case "Receiver":
					pv.report(c.pos, "a Receiver annotation belongs in the doc comment of a method in an interface type, "+
						"where it names the receiver for the contract of the method, as in // @Receiver c")
					continue
				}
				if gen, spec, vars, ok := pv.varDocumented(file, group); ok {
					pv.addVarInvariant(gen, spec, vars, c)
					continue
				}
				owner := pv.place(file, group, c)
				if c.kind == "Predicate" {
					decl, err := logic.ParsePredicate(c.text)
					if err != nil {
						pv.report(c.pos, "syntax error in Predicate annotation: %v", err)
						pv.predicatesBroken = true
						continue
					}
					predicates = append(predicates, decl)
					predicateClauses[decl] = c
					pv.predicateTexts = append(pv.predicateTexts, c.text)
					continue
				}
				if c.kind == "Modifies" {
					targets, err := logic.ParseTargets(c.text)
					switch {
					case err != nil:
						pv.report(c.pos, "syntax error in Modifies annotation: %v", err)
						if owner != nil {
							owner.broken = true
						}
					case owner != nil:
						owner.modifies = append(owner.modifies, newModTargets(targets, c)...)
					}
					continue
				}
				var node *logic.Node
				var err error
				switch c.kind {
				case "Snapshot":
					c.snapshot, node, err = logic.ParseSnapshot(c.text)
				case "Visited":
					node, err = logic.ParseVisited(c.text)
				default:
					node, err = logic.ParseFormula(c.text)
				}
				if err != nil {
					pv.report(c.pos, "syntax error in %s annotation: %v", c.kind, err)
					if owner != nil {
						owner.broken = true
					}
					continue
				}
				c.node = node
			}
		}
	}
	for _, defineErr := range pv.res.Define(predicates) {
		pv.report(predicateClauses[defineErr.Decl].pos, "%v", defineErr.Err)
		// A predicate that could not be defined stands for nothing, so no
		// proof of this package that may have used it counts.
		pv.predicatesBroken = true
	}
	pv.checkReceivers()
	pv.findSentinels()
	pv.findFixed()
	pv.checkVarGroups()
	pv.exportCovers()
	pv.findKnownReturns()
	// A contract speaks of the results by the names the function gives
	// them, so a verified function has to give each of them one.
	for _, fn := range pv.order {
		if !fn.annotated() {
			continue
		}
		for _, result := range fn.results {
			if result.Name() == "" || result.Name() == "_" {
				pv.report(fn.decl.Name.Pos(), "%s has annotations, so each of its results needs a name, as in %s",
					fn.obj.Name(), pv.namedSignature(fn))
				fn.broken = true
				break
			}
		}
	}
	for _, fn := range pv.order {
		if fn.annotated() && pv.entryFor(fn.obj.FullName()) != nil && !isIfaceMethod(fn.obj) {
			pv.report(fn.decl.Name.Pos(), "%s has annotations and a trusted contract; "+
				"a function is either verified or trusted, not both", fn.obj.Name())
		}
	}
	for _, fn := range pv.order {
		sort.Slice(fn.body, func(i, j int) bool { return fn.body[i].pos < fn.body[j].pos })
		if fn.decl.Body == nil {
			continue
		}
		pv.checkPlacement(fn)
		pv.checkSnapshots(fn)
		pv.checkVisited(fn)
	}
}

// namedSignature writes the signature of a function with a name for each
// result that has none: err for an error, ok for a boolean, and otherwise
// the first letter of the type, each made unique. A name is never one that
// an identifier anywhere in the declaration or its annotations has, so
// that it shadows nothing the body or the contract uses, and never a word
// of the annotation language.
func (pv *pkgVerifier) namedSignature(fn *funcInfo) string {
	taken := map[string]bool{"True": true, "False": true, "nil": true, "result": true}
	for _, word := range logic.Reserved {
		taken[word] = true
	}
	// The name of a field after a dot shadows nothing.
	var visit func(n ast.Node) bool
	visit = func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.SelectorExpr:
			ast.Inspect(n.X, visit)
			return false
		case *ast.Ident:
			taken[n.Name] = true
		}
		return true
	}
	ast.Inspect(fn.decl, visit)
	// The words of the annotations count whether or not they could be
	// read: a name that an annotation uses for something else, such as an
	// error variable or a predicate, would change what it means.
	clauses := slices.Concat(fn.requires, fn.ensures, fn.body)
	if fn.measure != nil {
		clauses = append(clauses, fn.measure)
	}
	for _, m := range fn.modifies {
		taken[m.name] = true
	}
	// A word of an annotation that names something where the function is
	// declared, as an error variable or a predicate does, would mean the
	// result instead; one that names nothing is likely the name meant for
	// a result, and is free.
	scope := pv.pass.Pkg.Scope().Innermost(fn.decl.Pos())
	for _, c := range clauses {
		for _, word := range strings.FieldsFunc(c.text, func(r rune) bool { return !unicode.IsLetter(r) && !unicode.IsDigit(r) && r != '_' }) {
			if _, obj := scope.LookupParent(word, fn.decl.Pos()); obj != nil || pv.res.Preds[word] != nil {
				taken[word] = true
			}
		}
	}
	qualifier := types.RelativeTo(pv.pass.Pkg)
	var parts []string
	for _, result := range fn.results {
		name := result.Name()
		if name == "" || name == "_" {
			base := "r"
			switch {
			case isError(result.Type()):
				base = "err"
			case types.Identical(result.Type().Underlying(), types.Typ[types.Bool]):
				base = "ok"
			default:
				shown := types.TypeString(result.Type(), qualifier)
				for _, r := range shown {
					if unicode.IsLetter(r) {
						base = strings.ToLower(string(r))
						break
					}
				}
			}
			name = base
			for i := 1; taken[name]; i++ {
				name = fmt.Sprintf("%s%d", base, i)
			}
		}
		taken[name] = true
		parts = append(parts, name+" "+types.TypeString(result.Type(), qualifier))
	}
	recv := ""
	var paramText []string
	for _, field := range fn.decl.Type.Params.List {
		var names []string
		for _, name := range field.Names {
			names = append(names, name.Name)
		}
		text := types.ExprString(field.Type)
		if len(names) > 0 {
			text = strings.Join(names, ", ") + " " + text
		}
		paramText = append(paramText, text)
	}
	if fn.decl.Recv != nil {
		var recvText []string
		for _, field := range fn.decl.Recv.List {
			text := types.ExprString(field.Type)
			if len(field.Names) > 0 {
				text = field.Names[0].Name + " " + text
			}
			recvText = append(recvText, text)
		}
		recv = "(" + strings.Join(recvText, ", ") + ") "
	}
	return fmt.Sprintf("func %s%s(%s) (%s)", recv, fn.decl.Name.Name, strings.Join(paramText, ", "), strings.Join(parts, ", "))
}

// rangesByCalling reports whether a range over a value of the type may call
// a function: the type is a function type, or a type parameter whose
// constraint lets it stand for one. Everything else that can be ranged over
// is data.
//
// For a constraint this errs towards yes. It does not work out which types
// meet all the elements of a constraint at once, so a constraint whose
// elements each allow some function type, but no function type in common,
// is taken to allow one. The cost is that such a range counts as a call.
func rangesByCalling(t types.Type) bool {
	if param, ok := types.Unalias(t).(*types.TypeParam); ok {
		t = param.Constraint()
	}
	switch u := t.Underlying().(type) {
	case *types.Basic, *types.Slice, *types.Array, *types.Pointer, *types.Map, *types.Chan:
		return false
	case *types.Union:
		for term := range u.Terms() {
			if rangesByCalling(term.Type()) {
				return true
			}
		}
		return false
	case *types.Interface:
		// A type must meet everything a constraint embeds, so one embedded
		// element that only lets data through is enough. A constraint that
		// embeds nothing of the kind says nothing.
		for embedded := range u.EmbeddedTypes() {
			if !rangesByCalling(embedded) {
				return false
			}
		}
		return true
	}
	return true
}

// addFunc records a function declaration with the names annotations may use
// for its parameters and results. Blank and unnamed parameters get no name;
// unnamed results, which only a trusted function can have, are called
// result, or result1, result2, ... when there are several.
func (pv *pkgVerifier) addFunc(decl *ast.FuncDecl) {
	obj, ok := pv.info.Defs[decl.Name].(*types.Func)
	if !ok {
		return
	}
	fn := newFuncInfo(obj)
	fn.decl = decl
	pv.funcs[obj] = fn
	pv.order = append(pv.order, fn)
}

// newFuncInfo describes a function by its signature, with the names
// annotations and trusted contracts may use for its parameters and results.
// The receiver of a method is its first parameter.
func newFuncInfo(obj *types.Func) *funcInfo {
	fn := &funcInfo{obj: obj, paramNames: map[string]*types.Var{}, resultNames: map[string]int{}, vouches: map[int]bool{}}
	sig := obj.Type().(*types.Signature)
	inputs := slices.Collect(sig.Params().Variables())
	if sig.Recv() != nil {
		inputs = append([]*types.Var{sig.Recv()}, inputs...)
	}
	for _, param := range inputs {
		fn.params = append(fn.params, param)
		// A blank or unnamed parameter cannot be referred to.
		if param.Name() != "" && param.Name() != "_" {
			fn.paramNames[param.Name()] = param
		}
	}
	for i := range sig.Results().Len() {
		result := sig.Results().At(i)
		fn.results = append(fn.results, result)
		if result.Name() != "" && result.Name() != "_" {
			fn.resultNames[result.Name()] = i
		}
	}
	// Unnamed results are called result, or result1, result2, ... when
	// there are several.
	for i := range sig.Results().Len() {
		name := fmt.Sprintf("result%d", i+1)
		if sig.Results().Len() == 1 {
			name = "result"
		}
		// A name the function itself gives to a result always wins.
		_, taken := fn.resultNames[name]
		if declared := sig.Results().At(i).Name(); (declared == "" || declared == "_") && !taken {
			fn.resultNames[name] = i
		}
	}
	return fn
}

// ambiguous reports whether an annotation of the function would read the
// name of a Go variable as something else: True, False, and nil are words of
// the annotation language, and result, or result1, result2, ..., is how an
// unnamed result is referred to.
//
// Only a name that an annotation actually uses is in doubt, and only an
// annotation that can see the variable: the contract sees the parameters
// and results, the annotations inside the body see the local variables too.
func (fn *funcInfo) ambiguous(name string, local bool) bool {
	// Inside a body result is not a name for anything, so a local variable
	// of that name is simply the variable.
	index, isResult := fn.resultNames[name]
	if name != "True" && name != "False" && name != "nil" && (local || !isResult || fn.results[index].Name() == name) {
		return false
	}
	used, clauses := false, fn.body
	if !local {
		used = slices.ContainsFunc(fn.modifies, func(m *modTarget) bool { return m.name == name })
		clauses = slices.Concat(fn.requires, fn.ensures, fn.body)
		if fn.measure != nil {
			clauses = append(clauses, fn.measure)
		}
	}
	for _, c := range clauses {
		c.node.Walk(func(n *logic.Node) {
			switch {
			case n.Kind == logic.NBool:
				used = used || name == map[int64]string{0: "False", 1: "True"}[n.Val]
			case n.Kind == logic.NNil:
				used = used || name == "nil"
			case n.Kind == logic.NIdent:
				used = used || name == n.Name
			}
		})
	}
	return used
}

// contractOf returns the contract that calls to a function are checked
// against: its annotations when it is verified, otherwise its trusted
// contract. It returns nil for a function that has neither.
func (pv *pkgVerifier) contractOf(callee *types.Func) *funcInfo {
	if pv.instanceOf[callee] != nil {
		// A generic function is never verified, so an instantiation has
		// only the contract of its entry.
		return pv.trustedContract(callee)
	}
	if own := pv.funcs[callee]; own != nil && own.annotated() {
		return own
	}
	// A generic function has no contract of its own: only an instantiation
	// that calleeAt made has one.
	if isGeneric(callee) {
		return nil
	}
	if imported := pv.importedContract(callee); imported != nil {
		if pv.trustedContract(callee) != nil {
			imported.defect("it is verified in its own package and also has a trusted contract")
		}
		return imported
	}
	return pv.trustedContract(callee)
}

// place binds a clause to a function and returns that function. Clauses inside
// a body annotate statements. Outside, a clause belongs to the function in
// whose doc comment it stands. A Variant in a doc comment is the measure by
// which the function's recursion ends; one inside the body is a loop's.
func (pv *pkgVerifier) place(file *ast.File, group *ast.CommentGroup, c *clause) *funcInfo {
	var next *ast.FuncDecl
	for _, decl := range file.Decls {
		fd, _ := decl.(*ast.FuncDecl)
		if decl.End() <= c.pos {
			continue
		}
		if decl.Pos() > c.pos {
			next = fd
			break
		}
		if fd == nil || fd.Body == nil {
			break
		}
		fn := pv.funcs[pv.info.Defs[fd.Name].(*types.Func)]
		switch c.kind {
		case "Invariant", "Variant", "Assert", "Snapshot", "Visited":
			fn.body = append(fn.body, c)
		case "Predicate":
		case "Vouches":
			pv.report(c.pos, "%s", misplacedVouches)
			fn.broken = true
		default:
			pv.report(c.pos, "%s annotation stands inside %s; put it in the doc comment of the function", c.kind, fn.obj.Name())
			fn.broken = true
		}
		return fn
	}
	if c.kind == "Predicate" {
		return nil
	}
	var fn *funcInfo
	switch {
	case next != nil && next.Doc == group:
		fn = pv.funcs[pv.info.Defs[next.Name].(*types.Func)]
	case c.kind == "Invariant" || c.kind == "Assert" || c.kind == "Snapshot" || c.kind == "Visited":
		pv.unread = true
		pv.report(c.pos, "%s annotation is not attached to anything; "+
			"it stands inside a function body, or, for an Invariant, in the doc comment of a struct type", c.kind)
		return nil
	default:
		pv.unread = true
		pv.report(c.pos, "%s annotation is not attached to a function; "+
			"put it in the comment directly above the function", c.kind)
		return nil
	}
	switch c.kind {
	case "Modifies":
	case "Vouches":
		pv.report(c.pos, "%s", misplacedVouches)
		fn.broken = true
	case "Requires":
		fn.requires = append(fn.requires, c)
	case "Ensures":
		fn.ensures = append(fn.ensures, c)
	case "Variant":
		if fn.measure != nil {
			// One of the two is dropped, so the function is not what its
			// author wrote.
			pv.report(c.pos, "function %s already has a Variant", fn.obj.Name())
			fn.broken = true
		}
		fn.measure = c
	default:
		pv.report(c.pos, "%s annotations belong inside a function body", c.kind)
		fn.broken = true
	}
	return fn
}

// enclosingFunc returns the function declaration of a file that holds a
// position, or nil.
func enclosingFunc(file *ast.File, pos token.Pos) *ast.FuncDecl {
	for _, decl := range file.Decls {
		if fd, ok := decl.(*ast.FuncDecl); ok && fd.Pos() <= pos && pos < fd.End() {
			return fd
		}
	}
	return nil
}

// localTypeAt reports whether a position lies in a type declaration inside
// a body, its doc comment and the comments of its fields and methods
// included. With bodyKeyword, for an Assert or a Snapshot, the doc comment
// does not count: such an annotation belongs in a body, and one directly
// above a local type is read there, between the statements around it.
func localTypeAt(body *ast.BlockStmt, pos token.Pos, bodyKeyword bool) bool {
	found := false
	ast.Inspect(body, func(n ast.Node) bool {
		decl, ok := n.(*ast.GenDecl)
		if !ok || decl.Tok != token.TYPE {
			return !found && n != nil
		}
		start := decl.Pos()
		if decl.Doc != nil && !bodyKeyword {
			start = decl.Doc.Pos()
		}
		found = found || (start <= pos && pos < decl.End())
		return false
	})
	return found
}

// misplacedVouches is the report for a Vouches annotation anywhere but in
// the contract of a type.
const misplacedVouches = "a Vouches annotation belongs in the doc comment of a method of an interface type or of a function type, " +
	"where it vouches for the errors that values of the type return; the errors of a verified function are judged from its body, " +
	"and those of a trusted function are vouched for in the trust file"

// checkPlacement rejects body annotations that are not written between
// statements. Symbolic execution only meets annotations at statement
// boundaries, so one inside an expression or between the cases of a switch
// would otherwise never be checked.
func (pv *pkgVerifier) checkPlacement(fn *funcInfo) {
	for _, c := range fn.body {
		var innermost, parent ast.Node
		ast.Inspect(fn.decl.Body, func(n ast.Node) bool {
			if n == nil || c.pos < n.Pos() || c.pos >= n.End() {
				return false
			}
			innermost, parent = n, innermost
			return true
		})
		between := false
		switch n := innermost.(type) {
		case *ast.BlockStmt:
			switch parent.(type) {
			case *ast.SwitchStmt:
				// A clause's annotations run from its colon to the next
				// clause, so one after its last statement belongs to it.
				if clause := trailedClause(n, c.pos); clause != nil {
					between = true
					if pv.caseTails == nil {
						pv.caseTails = map[token.Pos]*ast.CaseClause{}
					}
					pv.caseTails[c.pos] = clause
				}
			case *ast.TypeSwitchStmt, *ast.SelectStmt:
			default:
				between = true
			}
		case *ast.CaseClause:
			between = c.pos > n.Colon
		}
		if !between {
			pv.report(c.pos, "%s annotation must stand between statements, on a line of its own", c.kind)
			fn.broken = true
		}
	}
}

// clauseEnd returns where the annotations of the i-th clause of a switch
// end: at the next clause, or at the closing brace. gofmt indents a comment
// after the last statement of a clause with that clause's statements, so it
// is read as part of the clause.
func clauseEnd(body *ast.BlockStmt, i int) token.Pos {
	if i+1 < len(body.List) {
		return body.List[i+1].Pos()
	}
	return body.Rbrace
}

// trailedClause returns the clause of a switch whose last statement a
// position follows, before the next clause begins, or nil.
func trailedClause(body *ast.BlockStmt, pos token.Pos) *ast.CaseClause {
	for i, stmt := range body.List {
		clause := stmt.(*ast.CaseClause)
		if pos >= clause.End() && pos < clauseEnd(body, i) && pos > clause.Colon {
			return clause
		}
	}
	return nil
}

// scopeAt returns the innermost scope of a position in a body. An
// annotation after the last statement of a case clause lies outside the
// clause's scope as go/types records it, and is read in that scope.
func (pv *pkgVerifier) scopeAt(pos token.Pos) *types.Scope {
	if clause := pv.caseTails[pos]; clause != nil {
		return pv.info.Scopes[clause]
	}
	return pv.pass.Pkg.Scope().Innermost(pos)
}

func isBuiltin(info *types.Info, call *ast.CallExpr, name string) bool {
	id, ok := ast.Unparen(call.Fun).(*ast.Ident)
	if !ok {
		return false
	}
	builtin, ok := info.Uses[id].(*types.Builtin)
	return ok && builtin.Name() == name
}
