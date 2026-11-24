package typederrors

// Types whose conversion to error is refused, one for each condition of
// checkedMethods (F13 and F14 of the review of S1). Code that is not
// verified may run any method of what an error holds at any time, as
// consume below does under its trusted entry.

// Counter counts; Bump writes it.
type Counter struct{ n int }

// Bump has no contract.
func (c *Counter) Bump() { c.n++ }

// consume runs what an error holds: its trusted entry (trusted.yaml) lists
// e under runs and modifies nothing.
func consume(e error) {
	if h, ok := e.(HeldAny); ok {
		if b, ok := h.X.(interface{ Bump() }); ok {
			b.Bump()
		}
	}
	if h, ok := e.(heldHidden); ok {
		if b, ok := h.x.(interface{ Bump() }); ok {
			b.Bump()
		}
	}
	_ = e.Error()
}

// HeldAny holds anything in an exported field.
type HeldAny struct{ X any }

// @Ensures True
func (h HeldAny) Error() (s string) { return "held" }

// ThroughAny would return 1 where its contract says 0, if the conversion
// were let through: consume bumps the counter (TestRefusedWouldFail).
//
// @Ensures r = 0
func ThroughAny() (r int) {
	c := &Counter{}
	consume(HeldAny{X: c}) // want `converting a HeldAny to an error is not supported: it holds in field X a value of type any, which can carry code that nothing checks`
	return c.n
}

// heldHidden holds anything in a field that is not exported.
type heldHidden struct{ x any }

// @Ensures True
func (h heldHidden) Error() (s string) { return "hidden" }

// @Ensures r = 0
func ThroughHidden() (r int) {
	c := &Counter{}
	consume(heldHidden{x: c}) // want `converting a heldHidden to an error is not supported: it holds in field x a value of type any`
	return c.n
}

// ReqErr has an Error method with a Requires clause.
type ReqErr struct{ Line int }

// @Requires e != nil
// @Ensures True
func (e *ReqErr) Error() (s string) {
	if e.Line < 0 {
		return "negative"
	}
	return "req"
}

// NilRuns would panic in consume, which calls Error on a nil *ReqErr,
// where its contract says it returns 0 (TestRefusedWouldFail).
//
// @Ensures r = 0
func NilRuns() (r int) {
	var p *ReqErr
	consume(p) // want `converting a \*ReqErr to an error is not supported: \(\*ReqErr\).Error has a Requires clause, which a call made at any time may not meet`
	return 0
}

// Hook is a function type with a contract.
//
// @Ensures True
type Hook func() (s string)

// @Ensures True
func plainHook() (s string) { return "hook" }

// hook is a variable that holds a Hook.
var hook Hook = plainHook

// CallsHook has an Error method that calls through a function value.
type CallsHook int

// @Ensures True
func (c CallsHook) Error() (s string) {
	if hook == nil {
		return "none"
	}
	return hook() // want `this call may not end: CallsHook.Error calls hook\(\)`
}

// @Ensures err != nil
func HookError() (err error) {
	return CallsHook(1) // want `converting a CallsHook to an error is not supported: CallsHook.Error may call through a function value or an interface value`
}

// @Invariant 0 <= hits
var hits int

// CountsHits has an Error method that reads a variable of a group with an
// invariant.
type CountsHits int

// @Ensures True
func (c CountsHits) Error() (s string) {
	if hits > 0 {
		return "hit"
	}
	return "none"
}

// @Ensures err != nil
func HitsError() (err error) {
	return CountsHits(1) // want `converting a CountsHits to an error is not supported: CountsHits.Error names a variable of a group with an invariant`
}

// Inner has an Error method that Outer promotes.
type Inner struct{ n int }

// @Ensures True
func (i Inner) Error() (s string) { return "inner" }

// Outer embeds Inner.
type Outer struct{ Inner }

// @Ensures err != nil
func PromotedError() (err error) {
	return Outer{} // want `converting a Outer to an error is not supported: its method Error is promoted from an embedded field; code that is not verified may run any method of an error at any time, so declare Error on Outer itself`
}

// ValueErr has an Error method with a value receiver.
type ValueErr struct{ n int }

// @Ensures True
func (v ValueErr) Error() (s string) { return "value" }

// NilValueReceiver converts a nil pointer whose type's Error has a value
// receiver, under a contract that is otherwise met.
//
// @Ensures err = nil <-> n <= 0
func NilValueReceiver(n int) (err error) {
	var p *ValueErr
	if n > 0 {
		return p // want `ValueErr.Error has a value receiver, and the pointer converted to error may be nil, so the method would panic when it runs; convert a pointer that is not nil, or the value it points to`
	}
	return nil
}

// Count has a method, which reflection reaches through CountErr.C.
type Count struct{ n int }

// @Requires c != nil
// @Ensures v = c.n
func (c *Count) Value() (v int) { return c.n }

// CountErr holds a *Count in an exported field.
type CountErr struct{ C *Count }

// @Ensures True
func (c CountErr) Error() (s string) { return "count" }

// @Ensures err != nil
func ReachedError() (err error) {
	return CountErr{C: &Count{}} // want `converting a CountErr to an error is not supported: it holds through an exported field a value of type Count, which has methods; code that is not verified may run any method of an error at any time, so nothing a type converted to error holds through an exported field may have methods`
}

// Positive has an invariant.
//
// @Invariant n > 0
type Positive struct{ n int }

// @Ensures True
func (p *Positive) Error() (s string) { return "positive" }

// @Ensures err != nil
func InvariantError() (err error) {
	return &Positive{n: 1} // want `converting a \*Positive to an error is not supported: \*Positive has an invariant, which a method run at any time could not assume`
}

// Logged counts the calls of its Error method.
type Logged struct{ calls int }

// @Requires e != nil
// @Modifies e
// @Ensures True
func (e *Logged) Error() (s string) {
	if e.calls < 1000 {
		e.calls++
	}
	return "logged"
}

// @Ensures err != nil
func ModifiesError() (err error) {
	return &Logged{} // want `converting a \*Logged to an error is not supported: \(\*Logged\).Error modifies memory; code that is not verified may run any method of an error at any time, so each method of a type converted to error must modify nothing`
}
