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
// There is no external solver. The function is executed symbolically, and
// the obligations are discharged by a deduction engine written in Go, in
// the internal solver package. The engine is sound and deliberately
// incomplete: when it cannot prove something true, an Assert with an
// intermediate step or a stronger invariant usually helps.
//
// # Annotations
//
// An annotation is a comment line of the form "// @Keyword ...", with one
// space between the slashes and the @ and none after it. In the doc comment of a function:
// Requires, Ensures, Modifies, and, for a recursive function, Variant.
// Directly above a loop: Invariant and Variant. Anywhere in a body: Assert.
// In the doc comment of a struct type: Invariant. At the top level:
// Predicate, which names a formula. A contract refers to the results of a
// function by their names, so a verified function names all of them. The README of the module describes the language of the
// formulas and each annotation in full, and docs/verification.md in the
// module is a guide to writing verified Go.
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
//	-vego.max-steps   how much effort the solver spends on one obligation
//	-vego.trusted     path of the trust file, instead of the one next to go.mod
//
// The laas command adds -vego.trust, which prints the trust report.
package vego

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"reflect"
	"regexp"
	"slices"
	"sort"
	"strings"
	"unicode"
	"unicode/utf8"

	"github.com/spachava753/laas/vego/internal/logic"
	"golang.org/x/tools/go/analysis"
	"golang.org/x/tools/go/types/typeutil"
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

// newAnalyzer builds the analyzer with its flags. A run loads the trusted
// contracts, collects the annotations of the package, verifies every
// annotated function, applies the always-fails rule, and publishes the
// verified contracts and the trust the proofs rest on. For a caching driver
// it only reports that nothing was verified.
func newAnalyzer() *analysis.Analyzer {
	maxSteps, audit, trustPath, otherTags := 0, false, "", ""
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
		&maxSteps,
		"max-steps",
		0,
		"arithmetic checks the solver may spend on one proof obligation (0 selects the default)",
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
	analyzer.Flags.StringVar(
		&otherTags,
		"other-tags",
		"",
		"comma-separated words that other tools read after \"// @\", as in Summary,Param; any other unknown word there is an error",
	)
	analyzer.ResultType = reflect.TypeFor[*Usage]()
	analyzer.FactTypes = []analysis.Fact{new(contractFact), new(predicatesFact), new(usageFact), new(invariantFact), new(sentinelFact)}
	analyzer.Run = func(pass *analysis.Pass) (any, error) {
		foreignTags, err := parseOtherTags(otherTags)
		if err != nil {
			return nil, err
		}
		pv := &pkgVerifier{
			otherTags:     foreignTags,
			pass:          pass,
			info:          pass.TypesInfo,
			res:           logic.NewResolver(),
			funcs:         map[*types.Func]*funcInfo{},
			reported:      map[string]bool{},
			outcomes:      map[*funcInfo]*outcome{},
			trusted:       map[*types.Func]*funcInfo{},
			origins:       map[*ast.BlockStmt]*origins{},
			knownReturns:  map[*funcInfo]bool{},
			isParameter:   map[*types.Var]bool{},
			invariants:    map[*types.TypeName]*invariantSet{},
			foreignBroken: map[*types.Package]bool{},
			imported:      map[*types.Func]*funcInfo{},
			foreign:       map[*types.Package]*logic.Resolver{},
			plain:         logic.NewResolver(),
			trustSources:  map[*trustFile]*token.File{},
			maxSteps:      maxSteps,
		}
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
		pv.checkInvariantsDeclared()
		pv.exportInvariants()
		for _, fn := range pv.order {
			if !fn.annotated() || fn.broken {
				continue
			}
			pv.verified(fn)
			if audit {
				pv.run(fn, (*fnVerifier).audit)
			}
		}
		pv.exportContracts(pv.reportAlwaysFailing())
		for variable := range pv.relied {
			pass.ExportObjectFact(variable, new(sentinelFact))
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
	runs    map[*types.Var]bool
	broken  bool // an annotation failed to parse; verification is skipped
	callees []*funcInfo
	// modifies lists what the function may write, from its Modifies clauses.
	modifies []*modTarget
	// trust is set for a function whose contract comes from a trust file
	// instead of annotations; such a function is not verified.
	trust   *trustEntry
	defects []string  // what is wrong with a trusted or imported contract
	use     *EntryUse // the report entry of a trusted contract in use
	// imported is set for a function verified in another package, whose
	// contract was published by that package.
	imported *contractFact
	// failed is set when verifying the function reported a problem.
	failed bool
	// forces caches whether a trusted contract forces success for some
	// input; see forcesSuccess.
	forces *bool
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
	maxSteps int
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
	foreignBroken    map[*types.Package]bool
	// current is the function being verified, which a diagnostic counts
	// against.
	current *funcInfo
	// sentinels are the package-level error variables known to be non-nil,
	// and relied those among them a proof has used. unsettled holds the
	// ones that would be sentinels if no code of the package could run
	// before they are initialised, with what stands in the way.
	sentinels map[*types.Var]bool
	relied    map[*types.Var]bool
	// homemade holds the sentinels whose origin is known: nothing but plain
	// values and other such sentinels went into the error.
	homemade  map[*types.Var]bool
	unsettled map[*types.Var]string
	// reassigned holds the variables that are assigned, addressed, or
	// ranged into somewhere in the package.
	reassigned map[*types.Var]bool
	// origins caches what the variables of each function body are assigned,
	// knownReturns holds the functions that only return errors of known
	// origin, and isParameter the parameters of all functions.
	origins      map[*ast.BlockStmt]*origins
	knownReturns map[*funcInfo]bool
	isParameter  map[*types.Var]bool
	// invariants holds the invariants of struct types, nil for a type known
	// to have none.
	invariants map[*types.TypeName]*invariantSet
}

// report emits a diagnostic once per position and message. Symbolic execution
// visits a statement once per path, so the same failure can be found often.
func (pv *pkgVerifier) report(pos token.Pos, format string, args ...any) {
	if pv.current != nil {
		pv.current.failed = true
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
	// quotedComment matches an annotation shown with its own //, inside
	// a comment.
	quotedComment = regexp.MustCompile(`//[^\pL@]*@[^\pL]*\pL+`)
	// anyAnnotation finds the word after an @ wherever it stands, with
	// whatever is not a letter in between.
	anyAnnotation = regexp.MustCompile(`@[^\pL]*(\pL+)`)
	// leadingAt finds an @ that is the first thing on a line but for signs,
	// with the word that follows it.
	leadingAt   = regexp.MustCompile(`(?m)^[^\pL\pN@\n]*@[^\pL\pN\s]*(\S*)`)
	clauseKinds = map[string]bool{
		"Requires": true, "Ensures": true, "Invariant": true, "Variant": true,
		"Predicate": true, "Assert": true, "Modifies": true,
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
		written := strings.Map(func(r rune) rune {
			if unicode.Is(unicode.Cf, r) {
				return -1
			}
			return r
		}, comment.Text)
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
		line, aside, _ := strings.Cut(match[3], "//")
		line = strings.TrimSpace(line)
		// The comment an annotation line ends in is not read, so an
		// annotation written there would go unnoticed.
		if stray(aside) {
			clauses = append(clauses, &clause{pos: comment.Pos(),
				misplaced: `an annotation is written "// @Keyword ...", with nothing but one space between // and @`})
		}
		// The keyword is the run of letters the line starts with, so that
		// one written without a space before its formula is still one.
		keyword := line
		if end := strings.IndexFunc(line, func(r rune) bool { return !unicode.IsLetter(r) }); end >= 0 {
			keyword = line[:end]
		}
		word := line
		if end := strings.IndexFunc(line, unicode.IsSpace); end >= 0 {
			word = line[:end]
		}
		known := clauseKinds[keyword] || plannedKinds[keyword] || retiredKinds[keyword] != ""
		// The same line as it is written, from where the @ and the space
		// after it end.
		payload, _, _ := strings.Cut(comment.Text[unhidden(comment.Text, len(written)-len(match[3])):], "//")
		switch {
		case match[2] == "" && (otherTags[word] || otherTags[keyword]):
			// A tag that was declared to be another tool's is an ordinary
			// comment line, and like one it may not follow an annotation
			// directly.
			switch {
			case stray(line):
				clauses = append(clauses, &clause{pos: comment.Pos(),
					misplaced: `an annotation is written "// @Keyword ...", with nothing but one space between // and @`})
			case current != nil:
				clauses = append(clauses, &clause{pos: comment.Pos(), misplaced: afterAnnotation})
			}
			current = nil
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
		case plannedKinds[tag] || retiredKinds[tag] != "" || nearKeyword(tag):
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
	shown := quotedComment.ReplaceAllString(text, "")
	return slices.ContainsFunc(leadingAt.FindAllStringSubmatch(shown, -1), func(found []string) bool {
		letters := found[1]
		if end := strings.IndexFunc(letters, func(r rune) bool { return !unicode.IsLetter(r) }); end >= 0 {
			letters = letters[:end]
		}
		return !otherTags[found[1]] && !otherTags[letters]
	})
}

// stray reports whether a piece of comment text has an @ followed by a
// keyword, or by something close to one, where no annotation is read. An
// annotation that follows its own //, as in an example in a doc comment, a
// message of this tool that a comment quotes, or a line that was commented
// out, is one being shown and does not count.
func stray(text string) bool {
	shown := quotedComment.ReplaceAllString(text, "")
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
	var predicates []*logic.PredDecl
	predicateClauses := map[*logic.PredDecl]*clause{}
	for _, file := range pv.pass.Files {
		for _, decl := range file.Decls {
			if fd, ok := decl.(*ast.FuncDecl); ok {
				pv.addFunc(fd)
			}
		}
		for _, group := range file.Comments {
			for _, c := range extractClauses(group, pv.otherTags) {
				if c.misplaced != "" {
					pv.report(c.pos, "%s", c.misplaced)
					continue
				}
				if c.kind == "" {
					pv.report(c.pos, "unknown annotation %q; an annotation starts with one of "+
						"Requires, Ensures, Modifies, Invariant, Variant, Assert, Predicate. "+
						"If another tool reads this comment, declare the word with -vego.other-tags", c.text)
					continue
				}
				if plannedKinds[c.kind] {
					pv.report(c.pos, "%s annotations are not supported yet", c.kind)
					continue
				}
				if name, ok := pv.typeDocumented(file, group); ok {
					pv.addInvariant(name, c)
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
				node, err := logic.ParseFormula(c.text)
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
	pv.findSentinels()
	pv.findKnownReturns()
	// A contract speaks of the results by the names the function gives
	// them, so a verified function has to give each of them one.
	for _, fn := range pv.order {
		if !fn.annotated() {
			continue
		}
		for _, result := range fn.results {
			if result.Name() == "" || result.Name() == "_" {
				pv.report(fn.decl.Name.Pos(), "%s has annotations, so each of its results needs a name, as in func %s(...) (n int, err error)",
					fn.obj.Name(), fn.obj.Name())
				fn.broken = true
				break
			}
		}
	}
	for _, fn := range pv.order {
		if fn.annotated() && pv.trustedContract(fn.obj) != nil {
			pv.report(fn.decl.Name.Pos(), "%s has annotations and a trusted contract; "+
				"a function is either verified or trusted, not both", fn.obj.Name())
		}
	}
	// A call of a function value or of an interface method may go to any
	// function of the package that some code has got hold of: one that is
	// named anywhere but as the function of a call, and for a method called
	// through an interface, any method of that name. Where such a value
	// ends up is not followed; any call that cannot be resolved may reach
	// any of them.
	called := map[*ast.Ident]bool{}
	var escaped []*funcInfo
	for _, file := range pv.pass.Files {
		ast.Inspect(file, func(n ast.Node) bool {
			if call, ok := n.(*ast.CallExpr); ok {
				switch fun := ast.Unparen(call.Fun).(type) {
				case *ast.Ident:
					called[fun] = true
				case *ast.SelectorExpr:
					called[fun.Sel] = true
				}
			}
			return true
		})
		// Inside a function literal every function counts, called or
		// not: the literal is itself a value that may be called from
		// anywhere. A method of an interface that is named as a value
		// stands for every method of that name.
		var visit func(n ast.Node, inLiteral bool)
		visit = func(root ast.Node, inLiteral bool) {
			ast.Inspect(root, func(n ast.Node) bool {
				switch n := n.(type) {
				case *ast.FuncLit:
					if !inLiteral {
						visit(n.Body, true)
						return false
					}
				case *ast.Ident:
					named, ok := pv.info.Uses[n].(*types.Func)
					if !ok || (called[n] && !inLiteral) {
						break
					}
					if pv.funcs[named.Origin()] != nil {
						escaped = append(escaped, pv.funcs[named.Origin()])
					}
					if recv := named.Type().(*types.Signature).Recv(); recv != nil && types.IsInterface(recv.Type()) {
						escaped = append(escaped, pv.methodsNamed(named.Name())...)
					}
				}
				return true
			})
		}
		visit(file, false)
	}
	for _, fn := range pv.order {
		sort.Slice(fn.body, func(i, j int) bool { return fn.body[i].pos < fn.body[j].pos })
		if fn.decl.Body == nil {
			continue
		}
		pv.checkPlacement(fn)
		ast.Inspect(fn.decl.Body, func(n ast.Node) bool {
			switch n := n.(type) {
			case *ast.Ident:
				// A function that is named here may be called from here.
				if named, ok := pv.info.Uses[n].(*types.Func); ok && pv.funcs[named.Origin()] != nil {
					fn.callees = append(fn.callees, pv.funcs[named.Origin()])
				}
			case *ast.RangeStmt:
				// Ranging over a function calls it; which one is not
				// followed here either.
				if rangesByCalling(pv.info.TypeOf(n.X)) {
					fn.callees = append(fn.callees, escaped...)
				}
			case *ast.CallExpr:
				tv := pv.info.Types[n.Fun]
				if tv.IsType() || tv.IsBuiltin() || typeutil.StaticCallee(pv.info, n) != nil {
					break
				}
				fn.callees = append(fn.callees, escaped...)
				if sel, ok := ast.Unparen(n.Fun).(*ast.SelectorExpr); ok {
					fn.callees = append(fn.callees, pv.methodsNamed(sel.Sel.Name)...)
				}
			}
			return true
		})
	}
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

// methodsNamed returns the methods of the package with the given name, any
// of which a call of an interface method of that name may reach.
func (pv *pkgVerifier) methodsNamed(name string) []*funcInfo {
	var methods []*funcInfo
	for _, method := range pv.order {
		if method.obj.Name() == name && method.obj.Type().(*types.Signature).Recv() != nil {
			methods = append(methods, method)
		}
	}
	return methods
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
	fn := &funcInfo{obj: obj, paramNames: map[string]*types.Var{}, resultNames: map[string]int{}, runs: map[*types.Var]bool{}}
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
	if own := pv.funcs[callee]; own != nil && own.annotated() {
		return own
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
		case "Invariant", "Variant", "Assert":
			fn.body = append(fn.body, c)
		case "Predicate":
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
	case c.kind == "Invariant" || c.kind == "Assert":
		pv.report(c.pos, "%s annotation is not attached to anything; "+
			"it stands inside a function body, or, for an Invariant, in the doc comment of a struct type", c.kind)
		return nil
	default:
		pv.report(c.pos, "%s annotation is not attached to a function; "+
			"put it in the comment directly above the function", c.kind)
		return nil
	}
	switch c.kind {
	case "Modifies":
	case "Requires":
		fn.requires = append(fn.requires, c)
	case "Ensures":
		fn.ensures = append(fn.ensures, c)
	case "Variant":
		if fn.measure != nil {
			pv.report(c.pos, "function %s already has a Variant", fn.obj.Name())
		}
		fn.measure = c
	default:
		pv.report(c.pos, "%s annotations belong inside a function body", c.kind)
		fn.broken = true
	}
	return fn
}

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
			case *ast.SwitchStmt, *ast.TypeSwitchStmt, *ast.SelectStmt:
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

// reaches reports whether a call chain leads from one function to another.
func (pv *pkgVerifier) reaches(from, to *funcInfo) bool {
	seen := map[*funcInfo]bool{}
	var visit func(fn *funcInfo) bool
	visit = func(fn *funcInfo) bool {
		if fn == to {
			return true
		}
		if seen[fn] {
			return false
		}
		seen[fn] = true
		for _, callee := range fn.callees {
			if visit(callee) {
				return true
			}
		}
		return false
	}
	return visit(from)
}

func isBuiltin(info *types.Info, call *ast.CallExpr, name string) bool {
	id, ok := ast.Unparen(call.Fun).(*ast.Ident)
	if !ok {
		return false
	}
	builtin, ok := info.Uses[id].(*types.Builtin)
	return ok && builtin.Name() == name
}
