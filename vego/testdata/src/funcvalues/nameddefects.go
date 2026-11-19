package funcvalues

import "funcvalueslib"

// strict needs a smaller number than Mapper promises to pass.
//
// @Requires 0 <= x <= 10
// @Ensures y = x
func strict(x int) (y int) {
	return x
}

// Strict uses strict as a mapper.
//
// @Ensures f != nil
func Strict() (f Mapper) {
	return strict // want `vego: precondition of strict may not hold: 0 <= x <= 10, in strict used as a value of type Mapper at nameddefects.go:\d+:\d+`
}

// tripled can leave the range of Mapper.
//
// @Requires 0 <= x <= 1000
// @Ensures y = 3 * x
func tripled(x int) (y int) {
	return 3 * x
}

// Tripled uses tripled as a mapper.
//
// @Ensures f != nil
func Tripled() (f Mapper) {
	return tripled // want `vego: postcondition may not hold: 0 <= y <= 2000, in tripled used as a value of type Mapper`
}

// Retimes changes the timeout of a configuration.
//
// @Requires c != nil
// @Modifies c.Timeout
type Retimes func(c *Config)

// reset changes all of a configuration.
//
// @Requires c != nil
// @Modifies c
func reset(c *Config) {
	*c = Config{}
}

// Reset uses reset where only the timeout may change.
//
// @Ensures r != nil
func Reset() (r Retimes) {
	return reset // want `vego: reset may modify c, which may not be modified: nothing the // @Modifies clauses list is known to cover it|reset may modify c`
}

// first divides by its first parameter.
//
// @Requires y != 0
// @Ensures True
func first(y, x int) (z int) {
	return 100 / y
}

// WrongPosition uses a function that needs its first parameter not to be
// zero, which Pair does not promise.
//
// @Ensures p != nil
func WrongPosition() (p Pair) {
	return first // want `vego: precondition of first may not hold: y != 0`
}

// Dividers divide by what they hold.
type Divider struct{ k int }

// Div divides by the divisor it points to.
//
// @Requires d != nil And d.k > 0
// @Ensures True
func (d *Divider) Div(x int) (y int) {
	return x / d.k
}

// Plainly maps a number.
//
// @Ensures True
type Plainly func(x int) (y int)

// MakeDiv knows that d.k is 1 where the value is made, but the value runs
// later, when d.k may be 0.
//
// @Requires d != nil
// @Modifies d.k
// @Ensures f != nil
func MakeDiv(d *Divider) (f Plainly) {
	d.k = 1
	f = d.Div // want `vego: precondition of Div may not hold: d.k > 0, in d.Div used as a value of type Plainly at nameddefects.go:\d+:\d+`
	d.k = 0
	return f
}

// Bump counts one up in what it points to.
//
// @Requires c != nil And c.Retries < 1000
// @Modifies c.Retries
func (c *Config) Bump(x int) (y int) {
	c.Retries++
	return 0
}

// BumpOf makes a method value of a configuration of its own, whose method
// writes the configuration; Plainly does not let a value write anything.
//
// @Ensures f != nil
func BumpOf() (f Plainly) {
	var c Config
	return c.Bump // want `vego: precondition of Bump may not hold: c.Retries < 1000` `vego: Bump may modify what it calls c.Retries, which Plainly may not modify`
}

// NilScale makes a method value with a value receiver of a nil pointer,
// which copies the struct where the value is made.
//
// @Ensures True
func NilScale(p *Scale) (f Mapper) {
	return p.By // want `vego: pointer may be nil` `precondition of By may not hold`
}

// Applier applies a mapper.
//
// @Requires f != nil
// @Ensures True
type Applier func(xs []int, f Mapper)

// applyAll calls through the value it is given.
//
// @Requires f != nil
// @Ensures True
func applyAll(xs []int, f Mapper) {
}

// UsesApply uses a function that calls through a value as a value.
//
// @Ensures a != nil
func UsesApply() (a Applier) {
	return Apply // want `vego: cannot verify UsesApply: Apply may call through a function value, and code that a function value runs cannot do that yet: no contract of a function type has a variant, so nothing would prove that such calls end`
}

// Stepper steps.
//
// @Requires 0 <= x <= 100
// @Ensures True
type Stepper func(s funcvalueslib.Step, x int) (y int)

// UsesRun uses a function of another package that calls through a value.
//
// @Ensures s != nil
func UsesRun() (s Stepper) {
	return funcvalueslib.Run // want `vego: cannot verify UsesRun: Run may call through a function value`
}

// Converts makes a mapper from a value of another type.
//
// @Ensures True
func Converts(p Plain) (f Mapper) {
	return Mapper(p) // want `vego: cannot verify Converts: converting p to funcvalues.Mapper is not supported: a value of a function type is made only from a function literal, a function, or a method value written there, from nil, or from a value of the same type`
}

// Unnamed uses a function as a value of a type without a contract.
//
// @Ensures True
func ToUnnamed() (f func(x int) (y int)) {
	return double // want `vego: cannot verify ToUnnamed: double is used as a value of type func\(x int\) \(y int\), which has no contract; declare a named function type with a contract and use it here`
}

// Expression uses a method expression as a value.
//
// @Ensures True
func Expression() (f func(d *Divider, x int) (y int)) {
	return (*Divider).Div // want `vego: cannot verify Expression: a method expression, as in T.M, cannot be used as a value yet`
}

// hook is set by code that is not verified.
var hook func()

// fire is trusted, and calls the hook, which its body shows although its
// contract lists nothing under runs.
func fire() {
	if hook != nil {
		hook()
	}
}

// fires calls fire.
//
// @Ensures True
func fires(x int) (y int) {
	fire() // want `vego: fire is trusted and calls back into fires, so that this call ends cannot be proved; verify fire instead of trusting it`
	return 0
}

// UsesFires uses a function as a value that calls a trusted function whose
// body calls through a function value.
//
// @Ensures f != nil
func UsesFires() (f Plainly) {
	return fires // want `vego: cannot verify UsesFires: fires may call through a function value`
}

// logErr is trusted and is given an error, which its contract does not
// list under runs.
func logErr(e error) {}

// Logger logs an error.
//
// @Ensures True
type Logger func(e error)

// UsesLogErr uses logErr as a value, which hands it whatever error the
// value is called with.
//
// @Ensures l != nil
func UsesLogErr() (l Logger) {
	return logErr // want `vego: cannot verify UsesLogErr: logErr is used as a value, which passes what it is called with to logErr as e; logErr is trusted, and that can hold code nobody has seen`
}

// Div divides by its argument, whose name is the one of the parameter of
// Leak, which knows it is positive.
//
// @Ensures True
type DivBy func(x int) (y int)

// divide needs its argument not to be zero.
//
// @Requires x != 0
// @Ensures True
func divide(x int) (y int) {
	return 100 / x
}

// Leak uses divide as a value. What Leak knows of its own x says nothing of
// the x the value is called with.
//
// @Requires x > 0
// @Ensures True
func Leak(x int) (d DivBy) {
	return divide // want `vego: precondition of divide may not hold: x != 0, in divide used as a value of type DivBy`
}
