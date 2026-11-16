// Package rejected holds annotations and programs outside the supported
// fragment, which must be reported rather than silently accepted.
package rejected

// @Modifies A
// @Ensures |A'| = |A|
func write(A, B []int) {
	if len(A) > 0 && len(B) > 0 {
		A[0] = B[0]
	}
}

// @Requires |A| > 0
// @Modifies A
func PassesTwice(A []int) {
	write(A, A) // want `vego: the slices passed to write as A and B may overlap`
}

func unverified(A []int) []int { return A }

// @Requires |A| > 0
func UsesUnverifiedSlice(A []int) (result int) {
	B := unverified(A)
	return B[0] // want `vego: index may be out of range`
}

// @Requires x > // want `vego:\ syntax\ error\ in\ Requires\ annotation:\ expected\ an\ expression,\ found\ "end\ of\ annotation"`
func SyntaxError(x int) (result int) {
	return x
}

// @Requires y > 0 // want `vego:\ in\ Requires\ annotation:\ unknown\ name\ y`
func UnknownName(x int) (result int) {
	return x
}

// @Requires x' > 0 // want `vego:\ in\ Requires\ annotation:\ x'\ describes\ the\ state\ on\ return\ and\ is\ only\ allowed\ in\ Ensures`
func PrimeInRequires(x int) (result int) {
	return x
}

// @Ensures x' = y // want `vego: in Ensures annotation: x is passed by value, so only its value on entry is visible to callers; drop the prime`
func PrimeOnValue(x int) (y int) {
	return x
}

// @Requires A > 0 // want `vego:\ in\ Requires\ annotation:\ cannot\ compare\ A\ \(string\ or\ \[\]int\)\ with\ 0\ \(int\)`
func SliceAsInteger(A []int) (result int) {
	return 0
}

// @Predicate liar(x) ::= ~liar(x) // want `vego:\ recursive\ use\ of\ predicate\ liar\ must\ not\ occur\ under\ negation,\ on\ the\ left\ of\ \->,\ or\ under\ <\->`

// @Predicate twice(x) ::= x > 0
// @Predicate twice(x) ::= x < 0 // want `vego:\ predicate\ twice\ is\ already\ defined`

// @Requires undefined(x) // want `vego:\ in\ Requires\ annotation:\ unknown\ predicate\ undefined`
func UnknownPredicate(x int) (result int) {
	return x
}

// @Ensures y = x // want `vego:\ in\ Ensures\ annotation:\ operator\ =\ cannot\ be\ applied\ to\ float\ values`
func Floats(x float64) (y float64) {
	return x
}

func MisplacedInvariant(x int) (result int) {
	// @Invariant x > 0 // want `vego:\ Invariant\ annotation\ must\ be\ directly\ above\ a\ for\ loop`
	return x
}

func InvariantInsideBody(n int) (s int) {
	// @Variant n - i
	for i := 0; i < n; i++ {
		// @Requires i >= 0 // want `vego:\ Requires\ annotation\ stands\ inside\ InvariantInsideBody;\ put\ it\ in\ the\ doc\ comment\ of\ the\ function`
		s++
	}
	return s
}

// @Requires x > 0 // want `vego:\ Requires\ annotation\ is\ not\ attached\ to\ a\ function;\ put\ it\ in\ the\ comment\ directly\ above\ the\ function`

var global int

// @Requires x > 0
func ReadsGlobal(x int) (result int) {
	return x + global // want `vego:\ cannot\ verify\ ReadsGlobal:\ global\ is\ not\ a\ local\ variable\ of\ a\ supported\ type`
}

// @Requires x > 0
func Closure(x int) (result int) {
	f := func() int { return x } // want `vego: cannot verify Closure: f has unsupported type func\(\) int`
	return f()
}

// @Preserves |A| // want `vego:\ Preserves\ annotations\ are\ not\ supported\ yet`

// @Requires x > 0
func Goes(x int) {
	go Goes(x) // want `vego:\ cannot\ verify\ Goes:\ go\ statements\ are\ not\ supported\ yet`
}

// @Requires n >= 0
func Labeled(n int) {
outer: // want `vego:\ cannot\ verify\ Labeled:\ labeled\ statements\ are\ not\ supported\ yet`
	for i := 0; i < n; i++ {
		continue outer
	}
}

func InsideInitializer() (result int) {
	x := (
	// @Assert False // want `vego:\ Assert\ annotation\ must\ stand\ between\ statements,\ on\ a\ line\ of\ its\ own`
	0)
	return x
}

func InsideSwitch(n int) (result int) {
	switch n {
	// @Assert False // want `vego:\ Assert\ annotation\ must\ stand\ between\ statements,\ on\ a\ line\ of\ its\ own`
	case 0:
		return 0
	default:
		// @Assert n != 0
		return 1
	}
}

// @Ensures	False
func TabSeparator() (result int) { return 0 } // want `vego:\ postcondition\ may\ not\ hold:\ False`

// @ Ensure result = 1 // want `vego:\ unknown\ annotation\ "Ensure";\ an\ annotation\ starts\ with\ one\ of\ Requires,\ Ensures,\ Modifies,\ Invariant,\ Variant,\ Assert,\ Predicate`
func MisspeltKeyword() int { return 0 }

// @Summary comments of other tools are not annotations.
func OtherTool() int { return 0 }

// @Ensures result = // want `vego:\ syntax\ error\ in\ Ensures\ annotation:\ expected\ an\ expression,\ found\ "end\ of\ annotation"`
func malformed() (result int) { return 0 }

// @Ensures result = 0
func CallsMalformed() (result int) { return malformed() } // want `vego:\ cannot\ verify\ CallsMalformed:\ malformed\ has\ a\ contract\ that\ could\ not\ be\ understood`

// @Predicate negate(b) ::= ~b
// @Predicate hiddenLiar(n) ::= negate(hiddenLiar(n)) // want `vego:\ recursive\ use\ of\ predicate\ hiddenLiar\ must\ not\ occur\ under\ negation,\ on\ the\ left\ of\ \->,\ or\ under\ <\->`

// @Ensures result = 1
func MultipleVariants() (result int) {
	i := 0
	// @Invariant 0 <= i <= 1
	// @Variant 0
	// @Variant 1 - i // want `vego:\ loop\ already\ has\ a\ Variant;\ give\ it\ exactly\ one`
	for i < 1 { // want `vego:\ loop\ variant\ may\ not\ decrease:\ 0`
		i++
	}
	return i
}

// @Ensures result = ١ // want `vego:\ syntax\ error\ in\ Ensures\ annotation:\ unexpected\ character\ '١'`
func ArabicDigit() (result int) { return 1 }

type shape interface{ Area() int }

// @Requires s != nil
func Interfaces(s shape) (result int) { // want `vego: cannot verify Interfaces: parameter s has unsupported type rejected.shape`
	return s.Area()
}

type cell struct{ value int }

// @Requires c != nil
// @Modifies c.missing // want `vego: in Modifies annotation: c\.missing: rejected.cell has no field missing`
func MissingField(c *cell) {
	c.value = 1
}

// @Requires c != nil
// @Modifies c[0] // want `vego: in Modifies annotation: c: a \*rejected.cell cannot be indexed`
func BadTarget(c *cell) {
	c.value = 1
}

// @Requires c.value.size > 0 // want `vego: in Requires annotation: c\.value\.size: a int has no fields`
func FieldOfNumber(c *cell) (result int) {
	return 0
}

// @Requires c > 0 // want `vego: in Requires annotation: cannot compare c \(pointer\) with 0 \(int\)`
func PointerAsNumber(c *cell) (result int) {
	return 0
}

// @Requires p != nil
func PointerToNumber(p *int) (result int) { // want `vego: cannot verify PointerToNumber: parameter p has unsupported type \*int`
	return *p
}

// @Requires c != nil
func Embedded(c *cell) (result int) {
	m := make(chan int, 1) // want `vego: cannot verify Embedded: m has unsupported type chan int`
	return len(m) + c.value
}

// @Requires c != nil
// @Modifies c.value + 1 // want `vego: syntax error in Modifies annotation: unexpected "\+"`
func BadSyntax(c *cell) {
	c.value = 1
}

// @Requires c != nil
// @Modifies old(c) // want `vego: syntax error in Modifies annotation: a Modifies clause lists what is reached from the parameters, as in "A, s\.items, cs\[0\]"`
func BadKind(c *cell) {
	c.value = 1
}

// Impossible has a precondition nothing satisfies, from which anything
// would follow.
//
// @Requires |A| < 0
// @Ensures result = 42 And result = 43
func Impossible(A []int) (result int) { // want `vego: nothing can satisfy the Requires clauses of Impossible together with what the types of its parameters guarantee, so verifying it would prove nothing`
	return A[7]
}

// ResultParameter has a result without a name, which a contract cannot
// speak of.
//
// @Requires result = 7
// @Ensures result = 7
func ResultParameter(result int) int { // want `vego: ResultParameter has annotations, so each of its results needs a name, as in func ResultParameter\(...\) \(n int, err error\)`
	return 5
}

// FalseParameter has a parameter with the name of a word of the language.
//
// @Ensures r = False
func FalseParameter(False bool) (r bool) { // want `vego: cannot verify FalseParameter: the variable False has a name that means something else in annotations; rename it`
	return false
}

// NamedResult calls its result result, which is a name like any other.
//
// @Ensures result = 3
func NamedResult() (result int) {
	return 3
}

// SpacedOut has a contract and an assertion that both fail.
//
// @Requires x >= 0
// @Ensures result <= 0
func SpacedOut(x int) (result int) {
	// @Assert x >= 1 // want `vego: assertion may not hold: x >= 1`
	return x // want `vego: postcondition may not hold: result <= 0`
}

// Misspelt has keywords that are almost right.
//
// @Requires x >= 0
func Misspelt(x int) (result int) {
	//@assert False // want `vego: an annotation is written "// @Keyword ...", with one space before the @ and none after it`
	// @ assert False // want `vego: unknown annotation "assert"; an annotation starts with one of .*`
	return x
}

//@Ensure result > 100 // want `vego: an annotation is written "// @Keyword ...", with one space before the @ and none after it`

/*@ Ensures result > 100 */ // want `vego: annotations are only read from // comments, not from /\* \*/ comments`

// ResultField takes a struct with a field named like the result, which is
// no clash: a field is always written with what it is a field of.
//
// @Ensures result = 0
func ResultField(x struct{ result int }) (result int) {
	return 0
}

// @Requires True
/* // want `vego: annotations are only read from // comments, not from /\* \*. comments` `vego: a comment directly after an annotation is not read as part of it; continue an annotation with "// @ ...", or put an empty // line before a comment`
InBlock has an annotation inside a block comment, after other text.
@Ensures result = 0
*/
func InBlock() (result int) { return 1 }

// LocalTrue has a local variable named like a word of the language, which
// an annotation inside the body uses.
//
// @Ensures result <-> a > 0
// @Ensures result = a
func LocalTrue(a int8) (result bool) {
	True := a > 0 // want `vego: cannot verify LocalTrue: the variable True has a name that means something else in annotations; rename it`
	// @Assert True
	return True
}

// @Requires True
/* InBlockLater has a note @ Ensures result = 0 that comes after other text on its line. */ // want `vego: annotations are only read from // comments, not from /\* \*. comments` `vego: a comment directly after an annotation is not read as part of it; continue an annotation with "// @ ...", or put an empty // line before a comment`
func InBlockLater() (result int) { return 1 }

// OldPrefix writes an annotation without the space after the slashes.
//
//@ Requires x > 0 // want `vego: an annotation is written "// @Keyword ...", with one space before the @ and none after it`
func OldPrefix(x int) (r int) {
	return x
}

// WidePrefix writes one with two spaces.
//
//  @ Requires x > 0 // want `vego: an annotation is written "// @Keyword ...", with one space before the @ and none after it`
func WidePrefix(x int) (r int) {
	return x
}

// AfterBrace has its postcondition behind it, where annotations are no
// longer read from.
//
// @Requires x > 0
func AfterBrace(x int) (r int) {
	return x
}

// @Ensures r > 0 // want `vego: Ensures annotation is not attached to a function; put it in the comment directly above the function`

// OldMeasure uses the keyword that Variant replaced.
//
// @Requires n >= 0
// @Measure n // want `vego: there is no Measure annotation; write Variant`
func OldMeasure(n int) (r int) {
	return n
}

// TwoVariants gives two reasons for its recursion to end.
//
// @Requires n >= 0
// @Variant n
// @Variant n + 1 // want `vego: function TwoVariants already has a Variant`
func TwoVariants(n int) (r int) {
	if n == 0 {
		return 0
	}
	return TwoVariants(n - 1)
}

// LenCall writes the length the way Go does.
//
// @Requires len(A) > 0 // want `vego: in Requires annotation: there is no len in annotations; write \|x\| for the length of x`
func LenCall(A []int) (r int) {
	return A[0]
}

// CloseKeywords has keywords that are almost right, written with the right
// prefix and no space after the @.
//
// @ensures r > 100 // want `vego: unknown annotation "ensures"; an annotation starts with one of .*`
// @Ensure r > 100 // want `vego: unknown annotation "Ensure"; an annotation starts with one of .*`
func CloseKeywords(x int) (r int) {
	return x
}

// OtherTools has words after an @ that are no keywords of this language.
// The test declares Summary as another tool's; Postcondition it does not,
// and a word that nobody declared is taken to be a keyword gone wrong.
//
// @Summary returns its argument
// @Postcondition r > 100 // want `vego: unknown annotation "Postcondition"; an annotation starts with one of .* declare the word with -vego.other-tags`
// @Ensures r = x
func OtherTools(x int) (r int) {
	return x
}

// Wrapped continues its postcondition on a line that is an ordinary
// comment, which would be left out of it.
//
// @Ensures r >= 0
//   And r > 100 // want `vego: a comment directly after an annotation is not read as part of it; continue an annotation with "// @ ...", or put an empty // line before a comment`
func Wrapped(x int) (r int) {
	return 0
}

// Continued continues it with the prefix, and the whole clause is checked.
//
// @Ensures r >= 0
// @   And r > 100
func Continued(x int) (r int) {
	return 0 // want `vego: postcondition may not hold: r > 100`
}

// Glued writes its keywords without a space before the formula.
//
// @Requires(x > 0)
// @Ensures(r > 100)
func Glued(x int) (r int) {
	return 100 / x // want `vego: postcondition may not hold: \(r > 100\)`
}

// GluedToAt leaves out the space after the @ as well, which is a keyword
// all the same.
//
// @Ensures(r > 100)
func GluedToAt(x int) (r int) {
	return 0 // want `vego: postcondition may not hold: \(r > 100\)`
}

// InFront has something between the slashes and the @.
//
// @Requires x >= 0
// post: @ Ensures r > 100 // want `vego: an annotation is written "// @Keyword ...", with nothing but one space between // and @`
func InFront(x int) (r int) {
	return 0
}

// TripleSlash has a third slash there.
//
// @Requires x >= 0
/// @Ensures r > 100 // want `vego: an annotation is written "// @Keyword ...", with nothing but one space between // and @`
func TripleSlash(x int) (r int) {
	return 0
}

// NoBreakSpace has a space there that only looks like one.
//
// @Requires x >= 0
// @ Ensures r > 100 // want `vego: an annotation is written "// @Keyword ...", with one space before the @ and none after it`
func NoBreakSpace(x int) (r int) {
	return 0
}

// Stray has an assertion between two functions.

// @Assert True // want `vego: Assert annotation is not attached to anything; it stands inside a function body, or, for an Invariant, in the doc comment of a struct type`

// InSignature has an annotation among its parameters.
func InSignature(
	// @Requires x > 0 // want `vego: Requires annotation stands inside InSignature; put it in the doc comment of the function`
	x int,
) (r int) {
	return x
}

// DoubledAt writes the @ twice.
//
// @@ Ensures r > 100 // want `vego: an annotation is written "// @Keyword ...", with nothing but one space between // and @`
func DoubledAt(x int) (r int) {
	return 0
}

// DoubledAtAfter does so after another clause.
//
// @Requires x >= 0
// @@ Ensures r > 100 // want `vego: an annotation is written "// @Keyword ...", with nothing but one space between // and @`
func DoubledAtAfter(x int) (r int) {
	return 0
}

// InFrontMisspelt has other text before an @ with a keyword that is almost
// right.
//
// @Requires x >= 0
// post: @ ensures r > 100 // want `vego: an annotation is written "// @Keyword ...", with nothing but one space between // and @`
func InFrontMisspelt(x int) (r int) {
	return 0
}

// InAside writes a second annotation in the comment that ends the first.
//
// @Requires x >= 0 // post: @ Ensures r > 100 // want `vego: an annotation is written "// @Keyword ...", with nothing but one space between // and @`
func InAside(x int) (r int) {
	return 0
}

// ZeroWidth has a character after the @ that takes no room. The keyword is
// read as if it were not there.
//
// @​Ensures r > 100
func ZeroWidth(x int) (r int) {
	return 0 // want `vego: postcondition may not hold: r > 100`
}

// BlockAfter continues its postcondition in a block comment.
//
// @Ensures r >= 0
/* And r > 100 */ // want `vego: a comment directly after an annotation is not read as part of it; continue an annotation with "// @ ...", or put an empty // line before a comment`
func BlockAfter(x int) (r int) {
	return 0
}

// CommentedOut has an annotation behind slashes of its own, which is how a
// line is taken out, and is not read.
//
// // @Ensures r > 100
func CommentedOut(x int) (r int) {
	return 0
}

// SpaceAfterAt writes a space between the @ and the keyword.
//
// @ Requires x > 0 // want `vego: an annotation is written "// @Keyword ...", with one space before the @ and none after it`
func SpaceAfterAt(x int) (r int) {
	return x
}

// GluedContinuation continues a clause without the space that marks a
// continuation.
//
// @Ensures r >= 0
// @And r > 100 // want `vego: unknown annotation "And"; an annotation starts with one of .*`
func GluedContinuation(x int) (r int) {
	return 0
}

// BlockRetired has a keyword of an earlier version in a block comment.
/* @Measure n */ // want `vego: annotations are only read from // comments, not from /\* \*/ comments`
func BlockRetired(n int) (r int) { return n }

// BlockMisspelt has a keyword that is almost right after other text there.
/* note: @ensures r > 100 */ // want `vego: annotations are only read from // comments, not from /\* \*/ comments`
func BlockMisspelt(n int) (r int) { return n }

// SignsAfterAt has signs between the @ and the keyword.
//
// @- Ensures r > 100 // want `vego: an annotation is written "// @Keyword ...", with nothing but one space between // and @`
func SignsAfterAt(x int) (r int) {
	return 0
}

// StarsAfterAt writes the keyword in bold.
//
// @**Ensures** r > 100 // want `vego: an annotation is written "// @Keyword ...", with nothing but one space between // and @`
func StarsAfterAt(x int) (r int) {
	return 0
}

// WrongKeyword uses the word another specification language has for a
// postcondition. It must not pass for another tool's tag.
//
// @Post r > 100 // want `vego: unknown annotation "Post"; an annotation starts with one of .*`
func WrongKeyword(x int) (r int) {
	return 0
}

// WrongKeywordInBody does the same inside a body.
//
// @Ensures r = 0
func WrongKeywordInBody(x int) (r int) {
	// @Check x > 5 // want `vego: unknown annotation "Check"; an annotation starts with one of .*`
	return 0
}

// GluedAfterGap continues a clause after an empty line, with no space
// after the @.
//
// @Ensures r >= 0
//
// @And r > 100 // want `vego: unknown annotation "And"; an annotation starts with one of .*`
func GluedAfterGap(x int) (r int) {
	return 0
}

// ArrowFirst starts with a sign of the formula language.
//
// @-> r > 100 // want `vego: unknown annotation "->"; an annotation starts with one of .*`
func ArrowFirst(x int) (r int) {
	return 0
}

// Declared has tags that the test declares as another tool's, one of them
// with a hyphen. They are ordinary comment.
//
// @Summary returns its argument
// @Param x query int true "the argument"
// @x-order 3
//
// @Ensures r = x
func Declared(x int) (r int) {
	return x
}

// DeclaredAfter has such a tag directly under an annotation, where a
// comment may not stand.
//
// @Ensures r = x
// @Summary returns its argument // want `vego: a comment directly after an annotation is not read as part of it; continue an annotation with "// @ ...", or put an empty // line before a comment`
func DeclaredAfter(x int) (r int) {
	return x
}

// HiddenInString has a character that takes no room inside a string of its
// contract. The string is the one that is written, so a function that
// returns the visible letter alone does not meet it.
//
// @Ensures s = "a​"
func HiddenInString() (s string) {
	return "a" // want `vego: postcondition may not hold: s = "a​"`
}

// HiddenInStringKept returns the string as it is written.
//
// @Ensures s = "a​"
func HiddenInStringKept() (s string) {
	return "a\u200b"
}

// HiddenInFormula has such a character between the words of a formula,
// where it is no part of the language.
//
// @Ensures r​ = 0 // want `vego: syntax error in Ensures annotation: .*`
func HiddenInFormula() (r int) {
	return 0
}

// HiddenInBlock has one inside a keyword in a block comment.
/* @Ensu​res r = 1 */ // want `vego: annotations are only read from // comments, not from /\* \*/ comments`
func HiddenInBlock() (r int) { return 0 }

// Accented misspells a keyword by two letters that take more than one byte
// each.
//
// @Enšurés r = 1 // want `vego: unknown annotation "Enšurés"; an annotation starts with one of .*`
func Accented() (r int) { return 0 }

// AccentedInBlock does so in a block comment.
/* @Enšurés r = 1 */ // want `vego: annotations are only read from // comments, not from /\* \*/ comments`
func AccentedInBlock() (r int) { return 0 }

// ThirdSlashFar has a wrong keyword that is far from every real one,
// behind a third slash.
//
/// @Post r > 100 // want `vego: an annotation is written "// @Keyword ...", with nothing but one space between // and @`
func ThirdSlashFar(x int) (r int) {
	return 50
}

// BlockFar has one in a block comment.
/* @Post r > 100 */ // want `vego: annotations are only read from // comments, not from /\* \*/ comments`
func BlockFar(x int) (r int) { return 50 }

// BlockDeclared has a declared tag of another tool in a block comment,
// which is ordinary comment.
/* @Summary returns fifty */
func BlockDeclared(x int) (r int) { return 50 }

// TagHides has an annotation further along the line of a declared tag.
//
// @Summary returns zero @Ensures r > 100 // want `vego: an annotation is written "// @Keyword ...", with nothing but one space between // and @`
func TagHides(x int) (r int) {
	return 0
}

// TagQuotes has a declared tag whose line shows an annotation behind
// slashes of its own, as an ordinary comment may.
//
// @Summary once written // @Ensures r > 100
//
// @Ensures r = 0
func TagQuotes(x int) (r int) {
	return 0
}

// BlockSlashes has an annotation in a block comment, with slashes on the
// line before it. Slashes show an annotation only on its own line.
/* // want `vego: annotations are only read from // comments, not from /\* \*. comments`
 //
 @Ensures r = 1
*/
func BlockSlashes() (r int) { return 0 }

// LineSeparator has a character in its doc comment that ends a line on the
// screen and not for Go, so that the annotation after it looks like a line
// of its own.
//
// note // @Ensures r > 100 // want `vego: this comment has an @ and a character that ends a line on the screen but not for Go, such as U\+2028; remove the character, so that what is read is what is seen`
func LineSeparator(x int) (r int) {
	return 50
}

// SeparatedContinuation has one before what looks like a continuation.
//
// @Ensures r >= 0 // @ And r > 100 // want `vego: this comment has an @ and a character that ends a line on the screen but not for Go, such as U\+2028; remove the character, so that what is read is what is seen`
func SeparatedContinuation(x int) (r int) {
	return 50
}

// SeparatorInBlock has one in a block comment.
/* note // @Ensures r > 100 */ // want `vego: this comment has an @ and a character that ends a line on the screen but not for Go, such as U\+2028; remove the character, so that what is read is what is seen`
func SeparatorInBlock(x int) (r int) { return 50 }

// HiddenSlashes has a string in its contract with a character that takes
// no room between two slashes, and an @ after them. The slashes are not
// the start of a comment, and the function meets its contract.
//
// @Ensures s = "a/​/@Ensures"
func HiddenSlashes() (s string) {
	return "a/\u200b/@Ensures"
}

// ShownWithString shows an annotation behind slashes of its own whose
// formula has a string with an @ in it.
//
// // @Ensures s = "@Ensures"
//
// @Ensures r = 0
func ShownWithString() (r int) {
	return 0
}

// ShownThenStray shows one and then has another that is not shown.
//
// see // @Requires x > 0 and also @Ensures r > 100 // want `vego: an annotation is written "// @Keyword ...", with nothing but one space between // and @`
func ShownThenStray(x int) (r int) {
	return 0
}
