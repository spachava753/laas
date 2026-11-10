// Package rejected holds annotations and programs outside the supported
// fragment, which must be reported rather than silently accepted.
package rejected

type point struct{ x, y int }

// @ Requires p.x > 0 // want `vego:\ syntax\ error\ in\ Requires\ annotation:\ unexpected\ character\ '\.'`
func StructParameter(p point) int {
	return p.x
}

// @ Requires |A| > 0
func Aliases(A []int) int {
	B := A // want `vego:\ cannot\ verify\ Aliases:\ assigning\ slice\ A\ to\ another\ variable\ would\ make\ two\ variables\ share\ one\ backing\ array`
	B[0] = 1
	return A[0]
}

// @ Requires |A| > 0
func ReturnsParameter(A []int) []int {
	A[0] = 1
	return A // want `vego:\ cannot\ verify\ ReturnsParameter:\ returning\ slice\ parameter\ A\ would\ give\ the\ caller\ two\ names\ for\ one\ backing\ array`
}

// @ Requires |A| > 1
func SubSlices(A []int) int {
	B := A[1:] // want `vego:\ cannot\ verify\ SubSlices:\ this\ slice\ expression\ is\ not\ supported\ \(sub\-slicing\ and\ aliasing\ are\ not\ modelled\ yet\)`
	return B[0]
}

func write(A, B []int) {
	if len(A) > 0 && len(B) > 0 {
		A[0] = B[0]
	}
}

//@ Ensures |A'| = |A|

// @ Requires |A| > 0
func PassesTwice(A []int) {
	write(A, A) // want `vego:\ cannot\ verify\ PassesTwice:\ slice\ A\ is\ passed\ more\ than\ once\ to\ a\ function\ that\ may\ modify\ it`
}

func unverified(A []int) []int { return A }

// @ Requires |A| > 0
func UsesUnverifiedSlice(A []int) int {
	B := unverified(A) // want `vego:\ cannot\ verify\ UsesUnverifiedSlice:\ unverified\ returns\ a\ slice;\ a\ trusted\ contract\ cannot\ yet\ say\ that\ the\ slice\ shares\ no\ storage`
	return B[0]
}

// @ Requires x > // want `vego:\ syntax\ error\ in\ Requires\ annotation:\ expected\ an\ expression,\ found\ "end\ of\ annotation"`
func SyntaxError(x int) int {
	return x
}

// @ Requires y > 0 // want `vego:\ in\ Requires\ annotation:\ unknown\ name\ y`
func UnknownName(x int) int {
	return x
}

// @ Requires x' > 0 // want `vego:\ in\ Requires\ annotation:\ x'\ describes\ the\ state\ on\ return\ and\ is\ only\ allowed\ in\ Ensures`
func PrimeInRequires(x int) int {
	return x
}

func PrimeOnValue(x int) (y int) {
	return x
}

//@ Ensures x' = y // want `vego:\ in\ Ensures\ annotation:\ x\ is\ passed\ by\ value,\ so\ only\ its\ entry\ value\ x\ is\ visible\ to\ callers`

// @ Requires A > 0 // want `vego:\ in\ Requires\ annotation:\ cannot\ compare\ A\ \(\[\]int\)\ with\ 0\ \(int\)`
func SliceAsInteger(A []int) int {
	return 0
}

//@ Predicate liar(x) ::= ~liar(x) // want `vego:\ recursive\ use\ of\ predicate\ liar\ must\ not\ occur\ under\ negation,\ on\ the\ left\ of\ \->,\ or\ under\ <\->`

//@ Predicate twice(x) ::= x > 0
//@ Predicate twice(x) ::= x < 0 // want `vego:\ predicate\ twice\ is\ already\ defined`

// @ Requires undefined(x) // want `vego:\ in\ Requires\ annotation:\ unknown\ predicate\ undefined`
func UnknownPredicate(x int) int {
	return x
}

func Floats(x float64) (y float64) {
	return x
}

//@ Ensures y = x // want `vego:\ in\ Ensures\ annotation:\ operator\ =\ cannot\ be\ applied\ to\ float\ values`

func MisplacedInvariant(x int) int {
	//@ Invariant x > 0 // want `vego:\ Invariant\ annotation\ must\ be\ directly\ above\ a\ for\ loop`
	return x
}

func InvariantInsideBody(n int) (s int) {
	//@ Variant n - i
	for i := 0; i < n; i++ {
		//@ Requires i >= 0 // want `vego:\ Requires\ annotations\ belong\ outside\ the\ function\ body`
		s++
	}
	return s
}

//@ Requires x > 0 // want `vego:\ Requires\ annotation\ is\ not\ attached\ to\ a\ function;\ put\ it\ in\ the\ comment\ directly\ above\ the\ function`

var global int

// @ Requires x > 0
func ReadsGlobal(x int) int {
	return x + global // want `vego:\ cannot\ verify\ ReadsGlobal:\ global\ is\ not\ a\ local\ variable\ of\ a\ supported\ type`
}

// @ Requires x > 0
func Closure(x int) int {
	f := func() int { return x } // want `vego:\ cannot\ verify\ Closure:\ expressions\ of\ type\ func\(\)\ int\ are\ not\ supported`
	return f()
}

//@ Preserves |A| // want `vego:\ Preserves\ annotations\ are\ not\ supported\ yet`

type counter struct{ n int }

// @ Requires c.n >= 0 // want `vego:\ syntax\ error\ in\ Requires\ annotation:\ unexpected\ character\ '\.'`
func (c *counter) Method() int {
	return c.n
}

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

func InsideInitializer() int {
	x := (
	// @ Assert False // want `vego:\ Assert\ annotation\ must\ stand\ between\ statements,\ on\ a\ line\ of\ its\ own`
	0)
	return x
}

func InsideSwitch(n int) int {
	switch n {
	// @ Assert False // want `vego:\ Assert\ annotation\ must\ stand\ between\ statements,\ on\ a\ line\ of\ its\ own`
	case 0:
		return 0
	default:
		//@ Assert n != 0
		return 1
	}
}

// @ Ensures	False
func TabSeparator() int { return 0 } // want `vego:\ postcondition\ may\ not\ hold:\ False`

// @ Ensure result = 1 // want `vego:\ unknown\ annotation\ "Ensure";\ an\ annotation\ starts\ with\ one\ of\ Requires,\ Ensures,\ Invariant,\ Variant,\ Measure,\ Assert,\ Predicate`
func MisspeltKeyword() int { return 0 }

// @Summary comments of other tools are not annotations.
func OtherTool() int { return 0 }

// @ Ensures result = // want `vego:\ syntax\ error\ in\ Ensures\ annotation:\ expected\ an\ expression,\ found\ "end\ of\ annotation"`
func malformed() int { return 0 }

// @ Ensures result = 0
func CallsMalformed() int { return malformed() } // want `vego:\ cannot\ verify\ CallsMalformed:\ malformed\ has\ a\ contract\ that\ could\ not\ be\ understood`

//@ Predicate negate(b) ::= ~b
//@ Predicate hiddenLiar(n) ::= negate(hiddenLiar(n)) // want `vego:\ recursive\ use\ of\ predicate\ hiddenLiar\ must\ not\ occur\ under\ negation,\ on\ the\ left\ of\ \->,\ or\ under\ <\->`

func MultipleVariants() int {
	i := 0
	//@ Invariant 0 <= i <= 1
	//@ Variant 0
	//@ Variant 1 - i // want `vego:\ loop\ already\ has\ a\ Variant;\ give\ it\ exactly\ one`
	for i < 1 { // want `vego:\ loop\ variant\ may\ not\ decrease:\ 0`
		i++
	}
	return i
}

//@ Ensures result = 1

// @ Ensures result = ١ // want `vego:\ syntax\ error\ in\ Ensures\ annotation:\ unexpected\ character\ '١'`
func ArabicDigit() int { return 1 }
