// Package rejected holds annotations and programs outside the supported
// fragment, which must be reported rather than silently accepted.
package rejected

// @ Modifies A
func write(A, B []int) {
	if len(A) > 0 && len(B) > 0 {
		A[0] = B[0]
	}
}

//@ Ensures |A'| = |A|

// @ Requires |A| > 0
// @ Modifies A
func PassesTwice(A []int) {
	write(A, A) // want `vego: the slices passed to write as A and B may overlap`
}

func unverified(A []int) []int { return A }

// @ Requires |A| > 0
func UsesUnverifiedSlice(A []int) int {
	B := unverified(A)
	return B[0] // want `vego: index may be out of range`
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

//@ Ensures x' = y // want `vego: in Ensures annotation: x is passed by value, so only its value on entry is visible to callers; drop the prime`

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
	f := func() int { return x } // want `vego: cannot verify Closure: f has unsupported type func\(\) int`
	return f()
}

//@ Preserves |A| // want `vego:\ Preserves\ annotations\ are\ not\ supported\ yet`

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

// @ Ensure result = 1 // want `vego:\ unknown\ annotation\ "Ensure";\ an\ annotation\ starts\ with\ one\ of\ Requires,\ Ensures,\ Modifies,\ Invariant,\ Variant,\ Measure,\ Assert,\ Predicate`
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

type shape interface{ Area() int }

// @ Requires s != nil
func Interfaces(s shape) int { // want `vego: cannot verify Interfaces: parameter s has unsupported type rejected.shape`
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
func FieldOfNumber(c *cell) int {
	return 0
}

// @ Requires c > 0 // want `vego: in Requires annotation: cannot compare c \(pointer\) with 0 \(int\)`
func PointerAsNumber(c *cell) int {
	return 0
}

// @ Requires p != nil
func PointerToNumber(p *int) int { // want `vego: cannot verify PointerToNumber: parameter p has unsupported type \*int`
	return *p
}

// @ Requires c != nil
func Embedded(c *cell) int {
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
