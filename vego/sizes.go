package vego

import (
	"fmt"
	"go/token"
	"go/types"
	"maps"
	"math/big"
	"regexp"
	"slices"
	"strings"
	"sync"

	"github.com/spachava753/laas/vego/internal/logic"
	"github.com/spachava753/laas/vego/internal/solver"
	"gopkg.in/yaml.v3"
)

// The facts that a value fits in memory are bounds whose right side is a
// marked literal: the same number as the literal every other bound uses,
// so that a problem prints as it would without the mark, but a term of its
// own, so that the bound can be told from a bound on a number that a user
// or an entry wrote, by pointer. Only the places named at each mark make
// it.
type limitMarks struct {
	// mapCount bounds the number of keys of a map by MaxInt, and mapBytes
	// bounds what the entries of a map take by MaxAlloc (noteMap). Both
	// rest on memory alone: no obligation is asked where a key is added.
	mapCount, mapBytes *logic.Term
	// strLen bounds the length of a string by MaxAlloc or MaxInt, the
	// smaller (typeFact), and arrayEnd bounds the array of a slice, from
	// the start of its allocation to the end of its capacity, by MaxAlloc
	// (wellFormed). Each rests on the checks of what grows strings and
	// slices, which the declared memory discharges (sizesOf).
	strLen, arrayEnd *logic.Term
}

// marks returns the marked limits of the package's platform. They are made
// once for each platform and shared, so that a verifier copied for another
// platform, as the tests of 32-bit edges make, has the marks of its own.
func (pv *pkgVerifier) marks() *limitMarks {
	_, maxInt, _ := pv.intRange(types.Typ[types.Int])
	key := maxInt.String() + "/" + pv.maxAlloc().String()
	if found, ok := platformMarks.Load(key); ok {
		return found.(*limitMarks)
	}
	longest := pv.maxAlloc()
	if maxInt.Cmp(longest) < 0 {
		longest = maxInt
	}
	found, _ := platformMarks.LoadOrStore(key, &limitMarks{mapCount: logic.BigLit(maxInt), mapBytes: logic.BigLit(pv.maxAlloc()),
		strLen: logic.BigLit(longest), arrayEnd: logic.BigLit(pv.maxAlloc())})
	return found.(*limitMarks)
}

// platformMarks holds the marks of each platform, by its MaxInt and
// MaxAlloc.
var platformMarks sync.Map

// rewriteMarked rewrites each atom Le(t, mark) of a hypothesis, for a mark
// in marks, by with, where the atom stands only under And, Or, the
// consequent of Implies, and the body of a quantifier, the places where a
// weaker atom gives a weaker hypothesis and a stronger atom a stronger one.
// It reports false when a mark stands anywhere else, and the hypothesis is
// then to be left out (when weakening) or kept as it is (when
// strengthening).
func rewriteMarked(t *logic.Term, marks map[*logic.Term]bool, with func(*logic.Term) *logic.Term) (*logic.Term, bool) {
	if !holdsMark(t, marks) {
		return t, true
	}
	switch t.Op {
	case logic.OpLe:
		if marks[t.Args[1]] && !holdsMark(t.Args[0], marks) {
			return with(t), true
		}
		return t, false
	case logic.OpAnd, logic.OpOr:
		args := make([]*logic.Term, len(t.Args))
		for i, arg := range t.Args {
			rewritten, ok := rewriteMarked(arg, marks, with)
			if !ok {
				return t, false
			}
			args[i] = rewritten
		}
		if t.Op == logic.OpAnd {
			return logic.And(args...), true
		}
		return logic.Or(args...), true
	case logic.OpImplies:
		if holdsMark(t.Args[0], marks) {
			return t, false
		}
		rewritten, ok := rewriteMarked(t.Args[1], marks, with)
		if !ok {
			return t, false
		}
		return logic.Implies(t.Args[0], rewritten), true
	case logic.OpForall, logic.OpExists:
		if holdsMark(t.Args[0], marks) {
			return t, false
		}
		rewritten, ok := rewriteMarked(t.Args[1], marks, with)
		if !ok {
			return t, false
		}
		return logic.WithArgs(t, []*logic.Term{t.Args[0], rewritten}), true
	}
	return t, false
}

// holdsMark reports whether a term holds one of the marks.
func holdsMark(t *logic.Term, marks map[*logic.Term]bool) bool {
	if marks[t] {
		return true
	}
	for _, arg := range t.Args {
		if holdsMark(arg, marks) {
			return true
		}
	}
	return false
}

// hypsFor returns the hypotheses a proof of the goal being asked uses:
// all of them, clipped, or, while unmarked is set, each with the marked
// bounds dropped (an atom Le(t, mark) where it stands only to weaken
// becomes True, and a hypothesis that holds a mark anywhere else is left
// out). What follows from the result follows from the hypotheses. Without
// a mark among them the result is the hypotheses themselves.
func (v *fnVerifier) hypsFor(hyps []*logic.Term) []*logic.Term {
	v.unmarkedHit = false
	if v.unmarked == nil {
		return slices.Clip(hyps)
	}
	if v.dropped == nil {
		v.dropped = map[*logic.Term]*logic.Term{}
	}
	out := make([]*logic.Term, 0, len(hyps))
	for _, hyp := range hyps {
		rewritten, seen := v.dropped[hyp]
		if !seen {
			var ok bool
			rewritten, ok = rewriteMarked(hyp, v.unmarked, func(*logic.Term) *logic.Term { return logic.True() })
			if !ok {
				rewritten = nil
			}
			v.dropped[hyp] = rewritten
		}
		if rewritten != hyp {
			v.unmarkedHit = true
		}
		if rewritten != nil {
			out = append(out, rewritten)
		}
	}
	return out
}

// withoutMemory runs check, which asks goals of a Variant or a loop
// invariant, with the facts that only memory makes true left out of every
// proof it makes: those with no obligation behind them where a value grows,
// the marked bounds on the keys of a map. A loop that grows a map until
// memory runs out would otherwise be proved to end, directly or through an
// invariant that carries the bound to the head, and Go never returns from
// it (F1 of the design review of F38).
func (v *fnVerifier) withoutMemory(check func()) {
	saved, savedHit := v.unmarked, v.unmarkedHit
	m := v.marks()
	v.unmarked, v.unmarkedHit = map[*logic.Term]bool{m.mapCount: true, m.mapBytes: true}, false
	// Under the declared memory the checks of what grows strings and
	// slices are discharged by it, so their bounds rest on memory alone
	// too (F5 of the design review of F38).
	if v.sizesOf() != nil {
		v.unmarked[m.strLen], v.unmarked[m.arrayEnd] = true, true
	}
	defer func() { v.unmarked, v.unmarkedHit = saved, savedHit }()
	check()
}

// memoryNote is what the report of a goal that withoutMemory did not prove
// adds when the goal holds with the facts it left out: that the goal holds
// only because a run cannot hold more than memory. It asks the plain
// problem only when a fact was left out.
func (v *fnVerifier) memoryNote(st *state, guard []*logic.Term, goal *logic.Term) string {
	if v.unmarked == nil || !v.unmarkedHit {
		return ""
	}
	saved := v.unmarked
	v.unmarked = nil
	plain := v.attempt(st, guard, goal)
	v.unmarked = saved
	if plain != solver.Proved {
		return ""
	}
	if v.sizesOf() != nil {
		return "; it holds only because a map cannot have more keys, and a string or the array of a slice cannot be longer, than memory can hold, " +
			"which does not show that a loop or a recursion ends: one that grows a value until memory runs out does not end"
	}
	return "; it holds only because a map cannot have more keys than memory can hold, which does not show that a loop or a recursion ends: " +
		"one that adds keys until memory runs out does not end"
}

// checkVariant proves a goal of a Variant, bounded below or decreasing, as
// check does, with the facts that only memory makes true left out.
func (v *fnVerifier) checkVariant(st *state, guard []*logic.Term, goal *logic.Term, pos token.Pos, format string, args ...any) {
	v.withoutMemory(func() { v.check(st, guard, goal, pos, format, args...) })
}

// sizesDecl is a project's declaration that the machines the program runs
// on never hold memory bytes of its data at once, in memory and swap
// together, however it is stored, as its trust file states it under sizes.
type sizesDecl struct {
	memory *big.Int
	// written is the memory as the file writes it, as in 256GB.
	written string
	reason  string
	line    int
}

// sizesSlack is what the bound on the array of a slice adds to five times
// the memory: the page that growslice may round a new array up by.
const sizesSlack = 1 << 16

// arrayBound is R, the most bytes the array of a slice takes under the
// declaration: 5 * M + 65536 (see Sizes under a declared memory, in the
// ROADMAP).
func (d *sizesDecl) arrayBound() *big.Int {
	r := new(big.Int).Mul(d.memory, big.NewInt(5))
	return r.Add(r, big.NewInt(sizesSlack))
}

// addSizes reads the declaration of the memory of the machines.
func (f *trustFile) addSizes(key, value *yaml.Node) {
	if f.shipped {
		f.problem(key.Line, "sizes may be declared only in the trust file of a project")
		return
	}
	const shape = "sizes must be a mapping with a memory, the most of the program's data that the machines it runs on can hold at once, " +
		"in memory and swap together, however it is stored, as in 256GB, and a reason, which says why they never hold more"
	if value.Kind != yaml.MappingNode {
		f.problem(value.Line, shape)
		return
	}
	decl := &sizesDecl{line: key.Line}
	for i := 0; i+1 < len(value.Content); i += 2 {
		field, text := value.Content[i], value.Content[i+1]
		if text.Kind != yaml.ScalarNode {
			f.problem(text.Line, "%s of sizes must be text", field.Value)
			return
		}
		switch field.Value {
		case "memory":
			memory, err := parseMemory(text.Value)
			if err != nil {
				f.problem(text.Line, "the memory of sizes %s", err)
				return
			}
			decl.memory, decl.written = memory, strings.TrimSpace(text.Value)
		case "reason":
			decl.reason = strings.TrimSpace(text.Value)
		default:
			f.problem(field.Line, "unknown field %q of sizes; expected memory and reason", field.Value)
			return
		}
	}
	switch {
	case decl.memory == nil || decl.reason == "":
		f.problem(value.Line, shape)
	default:
		f.sizes = decl
	}
}

// memoryUnits are the units a declared memory may be written in.
var memoryUnits = map[string]int64{
	"": 1, "B": 1,
	"KB": 1e3, "MB": 1e6, "GB": 1e9, "TB": 1e12,
	"KiB": 1 << 10, "MiB": 1 << 20, "GiB": 1 << 30, "TiB": 1 << 40,
}

// parseMemory reads a number of bytes with an optional unit, as 256GB or
// 64GiB or 1000000000.
func parseMemory(text string) (*big.Int, error) {
	text = strings.TrimSpace(text)
	digits := strings.TrimRightFunc(text, func(r rune) bool { return r < '0' || r > '9' })
	unit, known := memoryUnits[strings.TrimSpace(text[len(digits):])]
	n, ok := new(big.Int).SetString(digits, 10)
	switch {
	case digits == "" || !ok || strings.IndexFunc(digits, func(r rune) bool { return r < '0' || r > '9' }) >= 0:
		return nil, fmt.Errorf("must be a whole number of bytes with an optional unit, as 256GB or 64GiB, not %q", text)
	case !known:
		return nil, fmt.Errorf("has the unit %q; write B, KB, MB, GB, TB, KiB, MiB, GiB, or TiB", strings.TrimSpace(text[len(digits):]))
	case n.Sign() <= 0:
		return nil, fmt.Errorf("must be more than 0 bytes")
	}
	return n.Mul(n, big.NewInt(unit)), nil
}

// SizesUse records a package whose trust file declares the memory of the
// machines: the declaration, as the file writes it, and the number of
// obligations of the package that only the declaration proved. Unused says
// why the declaration proves nothing on the platform, or is empty.
type SizesUse struct {
	File    string
	Line    int
	Memory  string
	Bytes   string
	Bound   string
	Reason  string
	Package string
	Proved  int
	Unused  string
}

// noteSizes records the declaration of the project's file in the usage of
// the package, which the trust report shows with the count of what only
// it proved (countSized).
func (pv *pkgVerifier) noteSizes(path string) {
	decl := pv.projectTrust.sizes
	if decl == nil {
		return
	}
	use := SizesUse{File: path, Line: decl.line, Memory: decl.written, Bytes: decl.memory.String(), Bound: decl.arrayBound().String(),
		Reason: decl.reason, Package: pv.pass.Pkg.Path()}
	// Where the bound on arrays is not below what one allocation can be,
	// every fact it would bound is bounded more tightly by the platform,
	// and it proves nothing more.
	if decl.arrayBound().Cmp(pv.maxAlloc()) >= 0 {
		use.Unused = fmt.Sprintf("it proves nothing on this platform, where one allocation is at most %s bytes, less than the %s bytes it would bound an array by",
			pv.maxAlloc(), decl.arrayBound())
	}
	pv.usage.Sizes = append(pv.usage.Sizes, use)
}

// sizesReport renders the section of the trust report on the declared
// memory: for each file that declares it, the claim, the reason, and how
// many obligations of each package only it proved.
func sizesReport(uses []SizesUse, relative func(string) string) string {
	if len(uses) == 0 {
		return ""
	}
	byFile := map[string][]SizesUse{}
	for _, use := range uses {
		byFile[use.File] = append(byFile[use.File], use)
	}
	var b strings.Builder
	fmt.Fprintf(&b, "Memory declared in sizes: %d\n", len(byFile))
	for _, file := range slices.Sorted(maps.Keys(byFile)) {
		listed := byFile[file]
		slices.SortFunc(listed, func(a, b SizesUse) int { return strings.Compare(a.Package, b.Package) })
		first := listed[0]
		fmt.Fprintf(&b, "  %s:%d\n", relative(file), first.Line)
		fmt.Fprintf(&b, "    claims:  the machines the program runs on never hold %s (%s bytes) of its data at once, in memory and swap together, "+
			"however it is stored; a run that would hold more runs out of memory, which no proof covers; so every string, and the entries "+
			"of every map, take at most %s bytes, and the array of every slice at most %s bytes\n", first.Memory, first.Bytes, first.Bytes, first.Bound)
		b.WriteString("    leaves:  every size that a number gives, as the length of make, Grow, slices.Grow, and the count of Repeat, " +
			"and every product of lengths, as strings.Join and Replace over a slice, to be proved; a Variant may not rest on it\n")
		fmt.Fprintf(&b, "    reason:  %s\n", first.Reason)
		var counts []string
		for _, use := range listed {
			if use.Unused != "" {
				counts = append(counts, fmt.Sprintf("none in %s: %s", use.Package, use.Unused))
				continue
			}
			counts = append(counts, fmt.Sprintf("%d in %s", use.Proved, use.Package))
		}
		fmt.Fprintf(&b, "    obligations only it proved: %s\n", strings.Join(counts, "; "))
	}
	b.WriteString("\n")
	return b.String()
}

// MemoryUse records the memory that the trust file of a package with
// verified functions declares under sizes: File is the trust file, or
// empty, and Memory and Bytes are empty when it declares none.
type MemoryUse struct {
	Package string
	File    string
	Memory  string
	Bytes   string
}

// noteMemory records the declared memory of a package with verified
// functions. A package with none is code that is not verified, and what it
// hands over is assumed within the bound.
func (pv *pkgVerifier) noteMemory() {
	if !slices.ContainsFunc(pv.order, func(fn *funcInfo) bool { return fn.annotated() }) {
		return
	}
	use := MemoryUse{Package: pv.pass.Pkg.Path()}
	if pv.projectTrust != nil {
		use.File = pv.projectTrust.path
		if decl := pv.projectTrust.sizes; decl != nil {
			use.Memory, use.Bytes = decl.written, decl.memory.String()
		}
	}
	pv.usage.Memories = append(pv.usage.Memories, use)
}

// reportTwoMemories reports two packages with verified functions, built
// together, whose trust files declare different memories, or of which one
// declares and the other does not (F13 of the review of F38). The bound on
// every value holds only if every reservation by a number in verified code
// was checked against one bound, so a value that one of them made can
// break what the other assumes. It is reported in every package that the
// two are built with.
func (pv *pkgVerifier) reportTwoMemories(total *Usage) {
	uses := slices.Clone(total.Memories)
	slices.SortFunc(uses, func(a, b MemoryUse) int { return strings.Compare(a.Package, b.Package) })
	said := func(use MemoryUse) string {
		file := "no trust file"
		if use.File != "" {
			file = use.File
		}
		if use.Bytes == "" {
			return fmt.Sprintf("package %s (%s) declares no memory", use.Package, file)
		}
		return fmt.Sprintf("package %s (%s) declares %s", use.Package, file, use.Memory)
	}
	for i, a := range uses {
		for _, b := range uses[i+1:] {
			if a.Bytes == b.Bytes {
				continue
			}
			pv.report(pv.pass.Files[0].Package, "the verified packages of this build declare different memories under sizes: %s, and %s; "+
				"a reservation that the proofs of one checked against its bound can break what the proofs of the other assume of every value. "+
				"Declare the same memory in both trust files, or none in either, or run laas with -vego.trusted naming one file", said(a), said(b))
			return
		}
	}
}


// sizesOf returns the declaration in effect for the package, or nil: the
// project's, when its bound on arrays is below what one allocation can be
// on the platform. Above that, every fact it would bound is bounded more
// tightly by the platform, and it proves nothing more.
func (pv *pkgVerifier) sizesOf() *sizesDecl {
	decl := pv.projectTrust
	if decl == nil || decl.sizes == nil || decl.sizes.arrayBound().Cmp(pv.maxAlloc()) >= 0 {
		return nil
	}
	return decl.sizes
}

// replacedHyps returns the hypotheses with each marked bound on a size made
// the declared one: a string and the entries of a map at most M bytes, the
// array of a slice at most R. A bound is replaced only where a smaller bound
// gives a stronger hypothesis (rewriteMarked); a hypothesis with a mark
// anywhere else is kept as it is. What follows from the result follows from
// the hypotheses together with the declaration.
func (v *fnVerifier) replacedHyps(hyps []*logic.Term, decl *sizesDecl) (replaced []*logic.Term, changed bool) {
	m := v.marks()
	memory, bound := logic.BigLit(decl.memory), logic.BigLit(decl.arrayBound())
	marks := map[*logic.Term]bool{m.strLen: true, m.mapBytes: true, m.arrayEnd: true}
	with := func(atom *logic.Term) *logic.Term {
		if atom.Args[1] == m.arrayEnd {
			return logic.Le(atom.Args[0], bound)
		}
		return logic.Le(atom.Args[0], memory)
	}
	if v.replaced == nil {
		v.replaced = map[*logic.Term]*logic.Term{}
	}
	out := make([]*logic.Term, len(hyps))
	for i, hyp := range hyps {
		rewritten, seen := v.replaced[hyp]
		if !seen {
			rewritten, _ = rewriteMarked(hyp, marks, with)
			v.replaced[hyp] = rewritten
		}
		out[i] = rewritten
		changed = changed || rewritten != hyp
	}
	return out, changed
}

// sizedAttempt proves a size goal: a goal that what an operation allocates
// can be allocated. It is asked as today; when that fails and the package
// declares the memory of its machines, it is asked once more on the
// hypotheses with the declared bounds (replacedHyps). declared reports a
// goal that only the declaration proved, which is then neither reported
// nor assumed: what it rests on holds only under the declaration, and no
// other goal may see it. A goal proved so on hypotheses that the
// declaration contradicts is reported where it stands, since there the
// declaration was used against what the path knows. While unmarked is set
// it is asked only as before.
func (v *fnVerifier) sizedAttempt(st *state, guard []*logic.Term, goal *logic.Term, pos token.Pos) (result solver.Result, declared bool) {
	result = v.attempt(st, guard, goal)
	decl := v.sizesOf()
	// A goal whose proof a Variant may rest on gets no second try: what
	// only the declaration proves holds only because a value cannot grow
	// past what the machines hold (F18 of the review of step 2a).
	if result == solver.Proved || decl == nil || v.unmarked != nil {
		return result, false
	}
	// Where no bound is replaced, the second problem is the first.
	replaced, changed := v.replacedHyps(st.hyps, decl)
	if !changed {
		return result, false
	}
	hyps := append(replaced, guard...)
	if v.solver().Prove(hyps, goal, v.options(0, obligation)) != solver.Proved {
		return result, false
	}
	if v.sizedProved != nil {
		v.sizedProved.Add(1)
	}
	if v.proves(hyps, logic.False(), quickEffort) {
		v.report(pos, "what is known here contradicts the declared memory: a string, the entries of a map, or the array of a slice here would be larger than "+
			"the declaration allows (%s bytes for a string or the entries of a map, %s for the array of a slice), so the declaration proves nothing here; "+
			"bound what is passed here, or declare more memory", decl.memory, decl.arrayBound())
	}
	return solver.Proved, true
}

// checkSized is check for size goals: each conjunct is asked by
// sizedAttempt, and one that only the declaration proved is not assumed.
func (v *fnVerifier) checkSized(st *state, guard []*logic.Term, goal *logic.Term, pos token.Pos, format string, args ...any) {
	for _, conjunct := range logic.Conjuncts(goal) {
		if conjunct.Op == logic.OpTrue {
			continue
		}
		done := v.at(pos)
		result, declared := v.sizedAttempt(st, guard, conjunct, pos)
		done()
		if !declared {
			note := ""
			if result != solver.Proved {
				note = v.sizeNote(st, guard, conjunct)
			}
			v.answered(st, guard, conjunct, result, true, pos, format+"%s", append(slices.Clip(args), note)...)
		}
	}
}

// exampleMemory is the memory that the hint of a size goal names, the
// guide's example; a hint is given only where declaring it would prove the
// goal (D5 of the design of F38).
var exampleMemory = &sizesDecl{memory: big.NewInt(256_000_000_000), written: "256GB"}

// sizeNote is what the report of a size goal that was not proved adds
// about a declared memory. Under one, that it does not cover the goal:
// what is asked depends on a number, a product of lengths, or a bound the
// declaration does not give. Without one, a hint to declare the memory,
// only where the second try with exampleMemory proves the goal on
// hypotheses that it does not contradict, so that it never points at a
// declaration that would not help (F9 of the design review). It asks one
// or two problems more, only after a failed size goal. None while a
// Variant's guard is on.
func (v *fnVerifier) sizeNote(st *state, guard []*logic.Term, goal *logic.Term) string {
	if v.unmarked != nil {
		return ""
	}
	if v.sizesOf() != nil {
		return "; the declared memory does not cover this: what it asks for depends on a number, a product of lengths, or a bound that the memory declared does not give"
	}
	if !v.wouldDeclare() {
		return v.idleNote()
	}
	replaced, changed := v.replacedHyps(st.hyps, exampleMemory)
	if !changed {
		return ""
	}
	hyps := append(replaced, guard...)
	if v.solver().Prove(hyps, goal, v.options(0, obligation)) != solver.Proved || v.proves(hyps, logic.False(), quickEffort) {
		return ""
	}
	// What the declaration would ask at the same site beside the goal, of
	// class N, must hold too, or the hint points at a declaration whose
	// first message is another refusal (F29 of the review of step 4).
	if v.alsoDeclared != nil {
		if also := v.alsoDeclared(exampleMemory); also != nil && v.solver().Prove(hyps, also, v.options(0, obligation)) != solver.Proved {
			return ""
		}
	}
	return v.declareOffer("which proves this")
}

// wouldDeclare reports whether a hint to declare a memory could help: the
// project declares none, and on the platform the bound of the guide's
// example is below what one allocation can be (F28 of the review of 3b).
func (v *fnVerifier) wouldDeclare() bool {
	return (v.projectTrust == nil || v.projectTrust.sizes == nil) && exampleMemory.arrayBound().Cmp(v.maxAlloc()) < 0
}

// idleNote says, for a project that declares a memory that proves nothing
// on the platform, that it does not, as the trust report says; otherwise
// it is empty.
func (v *fnVerifier) idleNote() string {
	if v.projectTrust == nil || v.projectTrust.sizes == nil || v.sizesOf() != nil {
		return ""
	}
	return fmt.Sprintf("; the memory declared under sizes proves nothing on this platform, where one allocation is at most %s bytes, less than the %s bytes it would bound an array by",
		v.maxAlloc(), v.projectTrust.sizes.arrayBound())
}

// declareOffer is the clause of a message that offers to declare a memory
// for what it allows, where that would take effect, or says that the one
// declared does not take effect; or is empty.
func (v *fnVerifier) declareOffer(allows string) string {
	if v.wouldDeclare() {
		return "; or, if the machines the program runs on never hold 256GB of its data at once, declare that under sizes in " + TrustFileName + ", " + allows
	}
	return v.idleNote()
}

// checkDeclared asks a goal that only a declared memory makes, a bound on
// what a reservation by a number may reserve. It may be proved from the
// hypotheses as they are or with the declared bounds (replacedHyps), since
// it is asked only under the declaration; one that is not proved is
// reported and then assumed, as check assumes a goal, and one proved is not
// assumed, since it may hold only under the declaration.
func (v *fnVerifier) checkDeclared(st *state, guard []*logic.Term, goal *logic.Term, pos token.Pos, format string, args ...any) {
	done := v.at(pos)
	result, _ := v.sizedAttempt(st, guard, goal, pos)
	done()
	if result != solver.Proved {
		v.answered(st, guard, goal, result, true, pos, format, args...)
	}
}

// uncaptured runs check with the reports of an initialiser not captured:
// what an initialiser reserves is reported where it stands, while the rest
// of what an initialiser that does not verify draws only keeps its variable
// from being known (F12 of the review of F38).
func (v *fnVerifier) uncaptured(check func()) {
	if !v.inInitialiser {
		check()
		return
	}
	saved := v.capturing
	v.capturing = nil
	defer func() { v.capturing = saved }()
	check()
}

// declaredMemory is the name the declared clauses of the shipped files
// give the memory declared.
var declaredMemory = regexp.MustCompile(`\bMemory\b`)

// declaredText returns a declared clause with the memory written out.
func declaredText(text string, memory *big.Int) string {
	return declaredMemory.ReplaceAllString(text, memory.String())
}

// checkDeclaredClauses asks, at a call of a trusted function under a
// declared memory, the clauses its entry declares for that case: what it
// reserves by a number must keep the bound on the array of every slice,
// given that what it copies is at most the memory (class N).
//
// It reports whether every declared clause was proved: with I's bounds a
// declared clause implies the size conjuncts of its entry, so when one is
// not proved those conjuncts are assumed and not reported beside it, with
// a hint that does not meet the declaration (F22 of the review of 2c).
func (v *fnVerifier) checkDeclaredClauses(fn *funcInfo, name string, pre *specEnv, st *state, guard []*logic.Term, pos token.Pos) bool {
	decl := v.sizesOf()
	if decl == nil || fn.trust == nil {
		return true
	}
	held := v.reports
	for _, formula := range fn.trust.declared {
		text := v.withInputsText(declaredText(formula.text, decl.memory))
		node, err := logic.ParseFormula(text)
		if err != nil {
			panic("vego: internal error: a declared clause cannot be read: " + err.Error())
		}
		c := &clause{kind: "requires", text: text, node: node, pos: pos}
		v.checkDeclared(st, guard, v.formula(c, node, pre), pos,
			"precondition of %s may not hold under the declared memory: %s, with Memory the %s declared; what it reserves by a number "+
				"is not bounded by what the machines hold, so bound it", name, strings.Join(strings.Fields(formula.text), " "), decl.written)
	}
	return v.reports == held
}

// declaredClauses returns the clauses an entry declares for a memory, as
// they read with that memory, or nil for an entry with none.
func (v *fnVerifier) declaredClauses(fn *funcInfo, pre *specEnv, decl *sizesDecl) *logic.Term {
	if fn.trust == nil || len(fn.trust.declared) == 0 {
		return nil
	}
	var all []*logic.Term
	for _, formula := range fn.trust.declared {
		text := v.withInputsText(declaredText(formula.text, decl.memory))
		node, err := logic.ParseFormula(text)
		if err != nil {
			panic("vego: internal error: a declared clause cannot be read: " + err.Error())
		}
		var goal *logic.Term
		v.quietly(func() { goal = v.formula(&clause{kind: "requires", text: text, node: node}, node, pre) })
		all = append(all, goal)
	}
	return logic.And(all...)
}
