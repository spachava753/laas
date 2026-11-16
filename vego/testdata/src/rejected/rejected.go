// Package rejected holds annotations and programs outside the supported
// fragment, which must be reported rather than silently accepted.
package rejected

// @ Modifies A
// @ Ensures |A'| = |A|
func write(A, B []int) {
	if len(A) > 0 && len(B) > 0 {
		A[0] = B[0]
	}
}

// @ Requires |A| > 0
// @ Modifies A
func PassesTwice(A []int) {
	write(A, A) // want `vego: the slices passed to write as A and B may overlap`
}

func unverified(A []int) []int { return A }

// @ Requires |A| > 0
func UsesUnverifiedSlice(A []int) (result int) {
	B := unverified(A)
	return B[0] // want `vego: index may be out of range`
}

// @ Requires x > // want `vego:\ syntax\ error\ in\ Requires\ annotation:\ expected\ an\ expression,\ found\ "end\ of\ annotation"`
func SyntaxError(x int) (result int) {
	return x
}

// @ Requires y > 0 // want `vego:\ in\ Requires\ annotation:\ unknown\ name\ y`
func UnknownName(x int) (result int) {
	return x
}

// @ Requires x' > 0 // want `vego:\ in\ Requires\ annotation:\ x'\ describes\ the\ state\ on\ return\ and\ is\ only\ allowed\ in\ Ensures`
func PrimeInRequires(x int) (result int) {
	return x
}

// @ Ensures x' = y // want `vego: in Ensures annotation: x is passed by value, so only its value on entry is visible to callers; drop the prime`
func PrimeOnValue(x int) (y int) {
	return x
}

// @ Requires A > 0 // want `vego:\ in\ Requires\ annotation:\ cannot\ compare\ A\ \(string\ or\ \[\]int\)\ with\ 0\ \(int\)`
func SliceAsInteger(A []int) (result int) {
	return 0
}

// @ Predicate liar(x) ::= ~liar(x) // want `vego:\ recursive\ use\ of\ predicate\ liar\ must\ not\ occur\ under\ negation,\ on\ the\ left\ of\ \->,\ or\ under\ <\->`

// @ Predicate twice(x) ::= x > 0
// @ Predicate twice(x) ::= x < 0 // want `vego:\ predicate\ twice\ is\ already\ defined`

// @ Requires undefined(x) // want `vego:\ in\ Requires\ annotation:\ unknown\ predicate\ undefined`
func UnknownPredicate(x int) (result int) {
	return x
}

// @ Ensures y = x // want `vego:\ in\ Ensures\ annotation:\ operator\ =\ cannot\ be\ applied\ to\ float\ values`
func Floats(x float64) (y float64) {
	return x
}

func MisplacedInvariant(x int) (result int) {
	// @ Invariant x > 0 // want `vego:\ Invariant\ annotation\ must\ be\ directly\ above\ a\ for\ loop`
	return x
}

func InvariantInsideBody(n int) (s int) {
	// @ Variant n - i
	for i := 0; i < n; i++ {
		// @ Requires i >= 0 // want `vego:\ Requires\ annotation\ stands\ inside\ InvariantInsideBody;\ put\ it\ in\ the\ doc\ comment\ of\ the\ function`
		s++
	}
	return s
}

// @ Requires x > 0 // want `vego:\ Requires\ annotation\ is\ not\ attached\ to\ a\ function;\ put\ it\ in\ the\ comment\ directly\ above\ the\ function`

var global int

// @ Requires x > 0
func ReadsGlobal(x int) (result int) {
	return x + global // want `vego:\ cannot\ verify\ ReadsGlobal:\ global\ is\ not\ a\ local\ variable\ of\ a\ supported\ type`
}

// @ Requires x > 0
func Closure(x int) (result int) {
	f := func() int { return x } // want `vego: cannot verify Closure: f has unsupported type func\(\) int`
	return f()
}

// @ Preserves |A| // want `vego:\ Preserves\ annotations\ are\ not\ supported\ yet`

// @ Requires x > 0
func Goes(x int) {
	go Goes(x) // want `vego:\ cannot\ verify\ Goes:\ go\ statements\ are\ not\ supported\ yet`
}

// @ Requires n >= 0
func Labeled(n int) {
outer: // want `vego:\ cannot\ verify\ Labeled:\ labeled\ statements\ are\ not\ supported\ yet`
	for i := 0; i < n; i++ {
		continue outer
	}
}

func InsideInitializer() (result int) {
	x := (
	// @ Assert False // want `vego:\ Assert\ annotation\ must\ stand\ between\ statements,\ on\ a\ line\ of\ its\ own`
	0)
	return x
}

func InsideSwitch(n int) (result int) {
	switch n {
	// @ Assert False // want `vego:\ Assert\ annotation\ must\ stand\ between\ statements,\ on\ a\ line\ of\ its\ own`
	case 0:
		return 0
	default:
		// @ Assert n != 0
		return 1
	}
}

// @ Ensures	False
func TabSeparator() (result int) { return 0 } // want `vego:\ postcondition\ may\ not\ hold:\ False`

// @ Ensure result = 1 // want `vego:\ unknown\ annotation\ "Ensure";\ an\ annotation\ starts\ with\ one\ of\ Requires,\ Ensures,\ Modifies,\ Invariant,\ Variant,\ Assert,\ Predicate`
func MisspeltKeyword() int { return 0 }

// @Summary comments of other tools are not annotations.
func OtherTool() int { return 0 }

// @ Ensures result = // want `vego:\ syntax\ error\ in\ Ensures\ annotation:\ expected\ an\ expression,\ found\ "end\ of\ annotation"`
func malformed() (result int) { return 0 }

// @ Ensures result = 0
func CallsMalformed() (result int) { return malformed() } // want `vego:\ cannot\ verify\ CallsMalformed:\ malformed\ has\ a\ contract\ that\ could\ not\ be\ understood`

// @ Predicate negate(b) ::= ~b
// @ Predicate hiddenLiar(n) ::= negate(hiddenLiar(n)) // want `vego:\ recursive\ use\ of\ predicate\ hiddenLiar\ must\ not\ occur\ under\ negation,\ on\ the\ left\ of\ \->,\ or\ under\ <\->`

// @ Ensures result = 1
func MultipleVariants() (result int) {
	i := 0
	// @ Invariant 0 <= i <= 1
	// @ Variant 0
	// @ Variant 1 - i // want `vego:\ loop\ already\ has\ a\ Variant;\ give\ it\ exactly\ one`
	for i < 1 { // want `vego:\ loop\ variant\ may\ not\ decrease:\ 0`
		i++
	}
	return i
}

// @ Ensures result = ١ // want `vego:\ syntax\ error\ in\ Ensures\ annotation:\ unexpected\ character\ '١'`
func ArabicDigit() (result int) { return 1 }

type shape interface{ Area() int }

// @ Requires s != nil
func Interfaces(s shape) (result int) { // want `vego: cannot verify Interfaces: parameter s has unsupported type rejected.shape`
	return s.Area()
}

type cell struct{ value int }

// @ Requires c != nil
// @ Modifies c.missing // want `vego: in Modifies annotation: c\.missing: rejected.cell has no field missing`
func MissingField(c *cell) {
	c.value = 1
}

// @ Requires c != nil
// @ Modifies c[0] // want `vego: in Modifies annotation: c: a \*rejected.cell cannot be indexed`
func BadTarget(c *cell) {
	c.value = 1
}

// @ Requires c.value.size > 0 // want `vego: in Requires annotation: c\.value\.size: a int has no fields`
func FieldOfNumber(c *cell) (result int) {
	return 0
}

// @ Requires c > 0 // want `vego: in Requires annotation: cannot compare c \(pointer\) with 0 \(int\)`
func PointerAsNumber(c *cell) (result int) {
	return 0
}

// @ Requires p != nil
func PointerToNumber(p *int) (result int) { // want `vego: cannot verify PointerToNumber: parameter p has unsupported type \*int`
	return *p
}

// @ Requires c != nil
func Embedded(c *cell) (result int) {
	m := make(chan int, 1) // want `vego: cannot verify Embedded: m has unsupported type chan int`
	return len(m) + c.value
}

// @ Requires c != nil
// @ Modifies c.value + 1 // want `vego: syntax error in Modifies annotation: unexpected "\+"`
func BadSyntax(c *cell) {
	c.value = 1
}

// @ Requires c != nil
// @ Modifies old(c) // want `vego: syntax error in Modifies annotation: a Modifies clause lists what is reached from the parameters, as in "A, s\.items, cs\[0\]"`
func BadKind(c *cell) {
	c.value = 1
}

// Impossible has a precondition nothing satisfies, from which anything
// would follow.
//
// @ Requires |A| < 0
// @ Ensures result = 42 And result = 43
func Impossible(A []int) (result int) { // want `vego: nothing can satisfy the Requires clauses of Impossible together with what the types of its parameters guarantee, so verifying it would prove nothing`
	return A[7]
}

// ResultParameter has a result without a name, which a contract cannot
// speak of.
//
// @ Requires result = 7
// @ Ensures result = 7
func ResultParameter(result int) int { // want `vego: ResultParameter has annotations, so each of its results needs a name, as in func ResultParameter\(...\) \(n int, err error\)`
	return 5
}

// FalseParameter has a parameter with the name of a word of the language.
//
// @ Ensures r = False
func FalseParameter(False bool) (r bool) { // want `vego: cannot verify FalseParameter: the variable False has a name that means something else in annotations; rename it`
	return false
}

// NamedResult calls its result result, which is a name like any other.
//
// @ Ensures result = 3
func NamedResult() (result int) {
	return 3
}

// SpacedOut has a contract and an assertion that both fail.
//
// @ Requires x >= 0
// @ Ensures result <= 0
func SpacedOut(x int) (result int) {
	// @ Assert x >= 1 // want `vego: assertion may not hold: x >= 1`
	return x // want `vego: postcondition may not hold: result <= 0`
}

// Misspelt has keywords that are almost right.
//
// @ Requires x >= 0
func Misspelt(x int) (result int) {
	//@assert False // want `vego: an annotation is written "// @ ...", with one space between // and @`
	// @ assert False // want `vego: unknown annotation "assert"; an annotation starts with one of .*`
	return x
}

//@Ensure result > 100 // want `vego: an annotation is written "// @ ...", with one space between // and @`

/*@ Ensures result > 100 */ // want `vego: annotations are only read from // comments, not from /\* \*/ comments`

// ResultField takes a struct with a field named like the result, which is
// no clash: a field is always written with what it is a field of.
//
// @ Ensures result = 0
func ResultField(x struct{ result int }) (result int) {
	return 0
}

// @ Requires True
/* // want `vego: annotations are only read from // comments, not from /\* \*. comments`
InBlock has an annotation inside a block comment, after other text.
@Ensures result = 0
*/
func InBlock() (result int) { return 1 }

// LocalTrue has a local variable named like a word of the language, which
// an annotation inside the body uses.
//
// @ Ensures result <-> a > 0
// @ Ensures result = a
func LocalTrue(a int8) (result bool) {
	True := a > 0 // want `vego: cannot verify LocalTrue: the variable True has a name that means something else in annotations; rename it`
	// @ Assert True
	return True
}

// @ Requires True
/* InBlockLater has a note @ Ensures result = 0 that comes after other text on its line. */ // want `vego: annotations are only read from // comments, not from /\* \*. comments`
func InBlockLater() (result int) { return 1 }

// OldPrefix writes an annotation without the space after the slashes.
//
//@ Requires x > 0 // want `vego: an annotation is written "// @ ...", with one space between // and @`
func OldPrefix(x int) (r int) {
	return x
}

// WidePrefix writes one with two spaces.
//
//  @ Requires x > 0 // want `vego: an annotation is written "// @ ...", with one space between // and @`
func WidePrefix(x int) (r int) {
	return x
}

// AfterBrace has its postcondition behind it, where annotations are no
// longer read from.
//
// @ Requires x > 0
func AfterBrace(x int) (r int) {
	return x
}

// @ Ensures r > 0 // want `vego: Ensures annotation is not attached to a function; put it in the comment directly above the function`

// OldMeasure uses the keyword that Variant replaced.
//
// @ Requires n >= 0
// @ Measure n // want `vego: there is no Measure annotation; write Variant`
func OldMeasure(n int) (r int) {
	return n
}

// TwoVariants gives two reasons for its recursion to end.
//
// @ Requires n >= 0
// @ Variant n
// @ Variant n + 1 // want `vego: function TwoVariants already has a Variant`
func TwoVariants(n int) (r int) {
	if n == 0 {
		return 0
	}
	return TwoVariants(n - 1)
}

// LenCall writes the length the way Go does.
//
// @ Requires len(A) > 0 // want `vego: in Requires annotation: there is no len in annotations; write \|x\| for the length of x`
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

// OtherTools has words after an @ that are no keywords of this language
// and stand for another tool's.
//
// @Summary returns its argument
// @Postcondition r > 100
// @ Ensures r = x
func OtherTools(x int) (r int) {
	return x
}

// Wrapped continues its postcondition on a line that is an ordinary
// comment, which would be left out of it.
//
// @ Ensures r >= 0
//   And r > 100 // want `vego: a comment line directly after an annotation is not read as part of it; continue an annotation with "// @ ...", or leave a line empty before a comment`
func Wrapped(x int) (r int) {
	return 0
}

// Continued continues it with the prefix, and the whole clause is checked.
//
// @ Ensures r >= 0
// @   And r > 100
func Continued(x int) (r int) {
	return 0 // want `vego: postcondition may not hold: r > 100`
}

// Glued writes its keywords without a space before the formula.
//
// @ Requires(x > 0)
// @ Ensures(r > 100)
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
// @ Requires x >= 0
// post: @ Ensures r > 100 // want `vego: an annotation is written "// @ ...", with nothing but one space between // and @`
func InFront(x int) (r int) {
	return 0
}

// TripleSlash has a third slash there.
//
// @ Requires x >= 0
/// @ Ensures r > 100 // want `vego: an annotation is written "// @ ...", with nothing but one space between // and @`
func TripleSlash(x int) (r int) {
	return 0
}

// NoBreakSpace has a space there that only looks like one.
//
// @ Requires x >= 0
// @ Ensures r > 100 // want `vego: an annotation is written "// @ ...", with one space between // and @`
func NoBreakSpace(x int) (r int) {
	return 0
}

// Stray has an assertion between two functions.

// @ Assert True // want `vego: Assert annotation is not attached to anything; it stands inside a function body, or, for an Invariant, in the doc comment of a struct type`

// InSignature has an annotation among its parameters.
func InSignature(
	// @ Requires x > 0 // want `vego: Requires annotation stands inside InSignature; put it in the doc comment of the function`
	x int,
) (r int) {
	return x
}
