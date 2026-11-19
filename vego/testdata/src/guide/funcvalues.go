package guide

import "errors"

// The programs of the section on function values.

// Mapper maps a number in range to a number in range.
//
// @Requires 0 <= x <= 1000
// @Ensures 0 <= y <= 2000
type Mapper func(x int) (y int)

// Apply maps every element of a slice.
//
// @Requires f != nil
// @Requires Forall i in [0, |xs|) : 0 <= xs[i] <= 1000
// @Modifies xs
// @Ensures Forall i in [0, |xs|) : 0 <= xs'[i] <= 2000
func Apply(xs []int, f Mapper) {
	// @Invariant Forall k in [0, i) : 0 <= xs[k] <= 2000
	// @Invariant Forall k in [i, |xs|) : xs[k] = old(xs)[k]
	for i := range xs {
		xs[i] = f(xs[i])
	}
}

// ApplyOnce calls a value that may be nil.
//
// @Requires 0 <= x <= 1000
// @Ensures True
func ApplyOnce(f Mapper, x int) (y int) {
	return f(x) // want `vego: the function value f may be nil`
}

// TwiceOf calls a value of a type without a contract.
//
// @Ensures True
func TwiceOf(f func(int) int) (y int) {
	return f(1) // want `vego: cannot verify TwiceOf: f has type func\(int\) int, which has no contract; declare a named function type with a contract and use it here`
}

// Config is what options change.
type Config struct {
	Timeout int
	Retries int
}

// Option changes a configuration.
//
// @Requires c != nil
// @Modifies c
type Option func(c *Config)

// Configure applies options to a configuration of its own.
//
// @Requires Forall i in [0, |opts|) : opts[i] != nil
// @Ensures True
func Configure(opts []Option) (cfg Config) {
	for _, opt := range opts {
		opt(&cfg)
	}
	return cfg
}

// WithTimeout returns an option that sets the timeout.
//
// @Ensures o != nil
func WithTimeout(d int) (o Option) {
	return func(c *Config) {
		c.Timeout = d
	}
}

// double doubles a number in range.
//
// @Requires 0 <= x <= 1000
// @Ensures y = 2 * x
func double(x int) (y int) {
	return 2 * x
}

// DoubleAll passes double as a mapper.
//
// @Requires Forall i in [0, |xs|) : 0 <= xs[i] <= 1000
// @Modifies xs
// @Ensures True
func DoubleAll(xs []int) {
	Apply(xs, double)
}

// small needs a smaller number than Mapper allows.
//
// @Requires 0 <= x <= 10
// @Ensures y = x
func small(x int) (y int) {
	return x
}

// Small uses small as a mapper.
//
// @Ensures f != nil
func Small() (f Mapper) {
	return small // want `vego: precondition of small may not hold: 0 <= x <= 10, in small used as a value of type Mapper at funcvalues.go:103:9`
}

// Offset adds an amount the literal captures.
//
// @Requires 0 <= k <= 1000
// @Ensures f != nil
func Offset(k int) (f Mapper) {
	return func(x int) int {
		return x + k
	}
}

// Later captures a variable that changes after the literal is made.
//
// @Ensures f != nil
func Later() (f Mapper) {
	k := 1
	f = func(x int) int {
		return x + k // want `vego: addition may overflow int, in the function literal used as a value of type Mapper at funcvalues.go:121:6` `vego: postcondition may not hold: 0 <= y <= 2000, in the function literal used as a value of type Mapper at funcvalues.go:121:6`
	}
	k = 5000
	return f
}

// Tally counts calls in a variable it captures.
//
// @Ensures f != nil
func Tally() (f Mapper) {
	calls := 0
	return func(x int) int {
		calls++ // want `vego: cannot verify Tally: a function literal used as a value cannot assign calls, a variable of the function around it: it may run when that function has moved on, and no call of it could tell that function what it did`
		return x
	}
}

// Logged wraps a mapper in a literal that calls it.
//
// @Requires f != nil
// @Ensures g != nil
func Logged(f Mapper) (g Mapper) {
	return func(x int) int {
		return f(x) // want `vego: cannot verify Logged: the function literal used as a value calls through the function value f, and code that a function value runs cannot do that yet: no contract of a function type has a variant, so nothing would prove that such calls end`
	}
}

// Half promises what an odd number cannot have.
//
// @Requires 0 <= x <= 1000
// @Ensures 2 * y = x
type Half func(x int) (y int) // want `vego: the Ensures clauses of Half are not proved to be satisfiable for every call that its Requires allow, by results and a change of what Modifies lists; a value of the type is taken to meet them, so a call of one could prove something false. State in the Requires when some result exists, or weaken the Ensures`

// Report is told about an error.
//
// @Requires e != nil
type Report func(e error)

// Tell hands a report an error that came from a parameter.
//
// @Requires r != nil And e != nil
// @Ensures True
func Tell(r Report, e error) {
	r(e) // want `vego: cannot verify Tell: e is passed to the function value r and is an error whose origin is not known; the value may come from code that is not verified, which could run code through it that nobody has seen`
}

// TellMade hands a report an error made here.
//
// @Requires r != nil
// @Ensures True
func TellMade(r Report) {
	r(errors.New("failed"))
}
