package formatting

// Logf is the project's own logging function. It forwards its values to
// log.Printf, which cannot be verified here, so it has an entry under
// formats in the trust file.
func Logf(format string, args ...any) {
}

// @Ensures True
func UsesLogf(n int, p Point) {
	Logf("%d at %v", n, p)
}

// @Ensures True
func UsesLogfWrongly(v any) {
	Logf("%v", v) // want `vego:\ cannot\ verify\ UsesLogfWrongly:\ Logf\ formats\ v`
}

// Sink is a function type whose contract writes.
//
// @Modifies b
type Sink func(b []int)

// The entries of handing, twoValues, and notAny break the rules of formats,
// each in its own way. Those of fill and sinking write, and run code that
// writes, after they format, which formats claims.

func fill(b []int, a ...any)     {}
func handing(f func(), a ...any) {}
func sinking(s Sink, a ...any)   {}
func twoValues(a any, b ...any)  {}
func notAny(n int, a ...int)     {}

// @Requires |b| > 0
// @Modifies b
// @Ensures True
func UsesFill(b []int) {
	fill(b, 1)
}

// @Ensures True
func UsesHanding() {
	handing(func() {}, 1) // want `vego:\ the\ trusted\ contract\ of\ formatting\.handing\ .*cannot\ be\ used:\ it\ lists\ formats\ and\ has\ calls`
}

// @Ensures True
func UsesSinking(s Sink) {
	sinking(s, 1)
}

// @Ensures True
func UsesTwoValues() {
	twoValues(1, 2) // want `vego:\ the\ trusted\ contract\ of\ formatting\.twoValues\ .*cannot\ be\ used:\ its\ formats\ lists\ a\ and\ b`
}

// @Ensures True
func UsesNotAny() {
	notAny(1, 2) // want `vego:\ the\ trusted\ contract\ of\ formatting\.notAny\ .*cannot\ be\ used:\ its\ formats\ lists\ a,\ of\ type\ \[\]int` `its formats lists no parameter of type any`
}

// Shout is a function type of values that take a value to format.
//
// @Ensures True
type Shout func(v any)

// logAny formats what it is given.
func logAny(v any) {}

// @Ensures True
func MakeShout() (s Shout) {
	return logAny // want `vego:\ cannot\ verify\ MakeShout:\ logAny\ is\ used\ as\ a\ value,\ which\ passes\ what\ it\ is\ called\ with\ to\ logAny\ as\ v;\ logAny\ formats\ v,\ and\ what\ a\ value\ is\ called\ with\ cannot\ be\ checked\ as\ it\ is\ at\ a\ call\ written\ out\.\ Call\ logAny\ directly`
}
