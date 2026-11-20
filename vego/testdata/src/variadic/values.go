package variadic

// Variadic function types and methods of interfaces with contracts, and
// values made of variadic functions, literals, and methods.

// Counter counts what it is given.
//
// @Ensures r = |xs|
type Counter func(xs ...int) (r int)

// @Ensures r = |xs|
func countAll(xs ...int) (r int) {
	return len(xs)
}

// @Ensures c != nil
func MakeCounter() (c Counter) {
	return countAll
}

// @Ensures c != nil
func MakeCounterLiteral() (c Counter) {
	return func(xs ...int) (r int) { return len(xs) }
}

// @Ensures c != nil
func MakeCounterWrong() (c Counter) {
	return func(xs ...int) (r int) { return 0 } // want `vego:\ postcondition\ may\ not\ hold:\ r\ =\ \|xs\|,\ in\ the\ function\ literal\ used\ as\ a\ value\ of\ type\ Counter`
}

// @Requires c != nil And |xs| <= 10
// @Ensures a = 3 And b = 0 And d = |xs|
func UseCounter(c Counter, xs []int) (a, b, d int) {
	a = c(1, 2, 3)
	b = c()
	d = c(xs...)
	return a, b, d
}

// @Requires c != nil
// @Ensures a = 2
func UseCounterWrong(c Counter) (a int) {
	return c(1, 2, 3) // want `vego:\ postcondition\ may\ not\ hold:\ a\ =\ 2`
}

// Tally is an interface with a variadic method.
type Tally interface {
	// @Ensures n = |xs|
	Count(xs ...int) (n int)
}

type tally struct{}

// @Ensures n = |xs|
func (tally) Count(xs ...int) (n int) {
	return len(xs)
}

type badTally struct{}

// @Ensures n = 0
func (badTally) Count(xs ...int) (n int) {
	return 0
}

// @Ensures t != nil
func MakeTally() (t Tally) {
	return tally{}
}

// @Ensures t != nil
func MakeTallyWrong() (t Tally) {
	return badTally{} // want `vego:\ postcondition\ may\ not\ hold:\ n\ =\ \|xs\|,\ in\ badTally\.Count\ used\ as\ a\ method\ of\ Tally`
}

// @Requires t != nil
// @Ensures n = 2
func UseTally(t Tally) (n int) {
	return t.Count(4, 5)
}

// Logger is a variadic function type that takes values of any type.
//
// @Ensures True
type Logger func(format string, args ...any)

// What a value of Logger is given may carry code nobody has seen.
//
// @Requires l != nil
// @Ensures True
func UseLogger(l Logger, n int) {
	l("%d", n) // want `vego:\ cannot\ verify\ UseLogger:\ n\ is\ passed\ to\ the\ function\ value\ l\ and\ is\ a\ value\ of\ type\ any`
}
