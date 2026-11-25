// Package runsclaims holds programs about what an entry claims under runs
// and asserts (the runs step of F33). An entry that lists a parameter under
// runs claims that the function calls, through an interface value or a
// function value, nothing that the parameter holds but the methods of the
// interfaces and the function types that the parameter's type reaches,
// and what it lists under asserts; no asserts for the parameter claims
// that it finds nothing more by a type assertion. Verified code answers for
// the methods it can call through those types, each checked where the
// value is made; the author of the entry answers for the rest, which is
// read from the function's source. The functions in lower case are trusted
// (trusted.yaml); run_test.go runs them.
package runsclaims

// Pinger has a method with a contract that writes nothing.
type Pinger interface {
	// @Ensures True
	Ping()
}

// Counter pings, and has a method without a contract that writes it.
type Counter struct{ n int }

// @Ensures True
func (c *Counter) Ping() {}

// Bump has no contract, and nothing checks it where a Counter is converted
// to Pinger.
func (c *Counter) Bump() { c.n++ }

// use asserts p to an interface with Bump and calls it. Its entry lists p
// under runs and has no asserts, so it claims that use calls nothing of p
// but Ping: the entry is false, which only the source of use shows, as
// only the source shows what a function keeps. It is kept false here to
// show what such an entry lets through.
func use(p Pinger) {
	if b, ok := p.(interface{ Bump() }); ok {
		b.Bump()
	}
}

// Hands verifies under the false entry of use, and returns 1
// (TestFalseEntry). Before the runs step the entry was true by its
// wording, which spoke of the interfaces that the parameter's type reaches
// and those it may be asserted to, and this proof was false (the
// reviewer's /tmp/f33s1p/ping, F13 of the review of S1).
//
// @Ensures r = 0
func Hands() (r int) {
	c := &Counter{}
	use(c)
	return c.n
}

// useBump is use with its entry corrected: it lists interface{ Bump() }
// under asserts for p, which is a defect, as Bump is not a method of
// Pinger.
func useBump(p Pinger) {
	if b, ok := p.(interface{ Bump() }); ok {
		b.Bump()
	}
}

// @Ensures r = 0
func HandsBump() (r int) {
	c := &Counter{}
	useBump(c) // want `the trusted contract of runsclaims.useBump \(trusted.yaml:\d+\) cannot be used: its asserts lists interface\{ Bump\(\) \} for p, an interface with the method Bump, and what it holds may hold a value of runsclaims.Pinger, which lacks it`
	return c.n
}

// Shutter has a method with a contract that writes nothing.
type Shutter interface {
	// @Ensures True
	Shut()
}

// Door is converted to Pinger only; its Shut writes it.
type Door struct{ n int }

// @Ensures True
func (d *Door) Ping() {}

// Shut has no contract and writes d.
func (d *Door) Shut() { d.n++ }

// useShut asserts p to Shutter, which its entry declares. Shut has a
// contract, but nothing checked a Door against it where the Door was
// converted to Pinger, so the entry is a defect all the same (the
// reviewer's /tmp/f33s1p/ping2).
func useShut(p Pinger) {
	if s, ok := p.(Shutter); ok {
		s.Shut()
	}
}

// @Ensures r = 0
func HandsShut() (r int) {
	d := &Door{}
	useShut(d) // want `the trusted contract of runsclaims.useShut \(trusted.yaml:\d+\) cannot be used: its asserts lists runsclaims.Shutter for p, an interface with the method Shut, and what it holds may hold a value of runsclaims.Pinger, which lacks it`
	return d.n
}

// usePing asserts p to an interface whose only method is Ping, which
// Pinger has: what it finds is checked, and the entry may list it.
func usePing(p Pinger) {
	if q, ok := p.(interface{ Ping() }); ok {
		q.Ping()
	}
}

// @Ensures r = 0
func HandsPing() (r int) {
	c := &Counter{}
	usePing(c)
	return c.n
}

// failing writes what it holds when its Error runs; it has no contract.
type failing []int

func (f failing) Error() string {
	f[0] = 1
	return "f"
}

// consumeAny asserts x to error and calls Error. Its entry declares it, as
// asserts: {x: [error]}, which is a defect: an any reaches no method, and
// a value converted to any is checked against none (the orchestrator's
// /tmp/f33probe/anyrun).
func consumeAny(x any) {
	if e, ok := x.(error); ok {
		_ = e.Error()
	}
}

// @Requires |a| = 1 And a[0] = 0
// @Ensures result = 0
func BoxedAny(a failing) (result int) {
	consumeAny(a) // want `the trusted contract of runsclaims.consumeAny \(trusted.yaml:\d+\) cannot be used: its asserts lists error for x, an interface with the method Error, and what it holds may hold a value of any, which lacks it`
	return a[0]
}

// PingErr is an error that holds a Pinger.
type PingErr struct{ p Pinger }

// @Ensures True
func (e PingErr) Error() (s string) { return "ping" }

// consumeErr asserts an error to PingErr, and what it holds to an
// interface with Bump. Over an error, asserts may list any type, since
// every method of the error is checked where it is made; so it is what
// the error holds that must have nothing unchecked, and a conversion to
// error of a type that holds a Pinger is refused.
func consumeErr(e error) {
	if pe, ok := e.(PingErr); ok {
		if b, ok := pe.p.(interface{ Bump() }); ok {
			b.Bump()
		}
	}
}

// @Ensures r = 0
func HandsInError() (r int) {
	c := &Counter{}
	consumeErr(PingErr{p: c}) // want `converting a PingErr to an error is not supported: it holds in field p a value of type Pinger, which was checked only against the methods of Pinger where it was made, and code given the error may find other methods on it by a type assertion`
	return c.n
}

// TimeoutErr is an error with a Timeout method.
type TimeoutErr int

// @Ensures True
func (e TimeoutErr) Error() (s string) { return "timeout" }

// @Ensures t = (e > 0)
func (e TimeoutErr) Timeout() (t bool) { return e > 0 }

// isTimeout asserts err to an interface with Timeout, as os.IsTimeout
// does. Over an error that is no defect: Timeout is checked where a
// TimeoutErr is converted to error.
func isTimeout(err error) bool {
	t, ok := err.(interface{ Timeout() bool })
	return ok && t.Timeout()
}

// @Ensures True
func AskTimeout() (r bool) {
	return isTimeout(TimeoutErr(1))
}

// Holder holds a Pinger in a field.
type Holder struct{ P Pinger }

// useHolder asserts what h holds to an interface with Ping, which the type
// of h reaches through its field.
func useHolder(h *Holder) {
	if q, ok := h.P.(interface{ Ping() }); ok {
		q.Ping()
	}
}

// @Ensures r = 0
func HandsHolder() (r int) {
	c := &Counter{}
	useHolder(&Holder{P: c})
	return c.n
}

// Hook is a function type with a method Ping.
type Hook func()

// @Ensures True
func (h Hook) Ping() {}

// useHook asserts p to Hook and calls the function, which nothing checked
// where a Hook was converted to Pinger.
func useHook(p Pinger) {
	if h, ok := p.(Hook); ok {
		h()
	}
}

// @Ensures r = 0
func HandsHook() (r int) {
	c := &Counter{}
	useHook(Hook(func() { c.n++ })) // want `the trusted contract of runsclaims.useHook \(trusted.yaml:\d+\) cannot be used: its asserts lists runsclaims.Hook for p, a function type that nothing it holds has`
	return c.n
}

// Two holds a Pinger and a Shutter.
type Two struct {
	P Pinger
	S Shutter
}

// Latch shuts, and has a Ping without a contract that writes it.
type Latch struct{ n int }

// @Ensures True
func (l *Latch) Shut() {}

// Ping has no contract and writes l.
func (l *Latch) Ping() { l.n++ }

// useTwo asserts what h holds to an interface with Ping. Pinger has Ping,
// but what S holds may lack it: nothing checked a Latch's Ping where it
// was converted to Shutter, so the entry is a defect.
func useTwo(h *Two) {
	if q, ok := h.S.(interface{ Ping() }); ok {
		q.Ping()
	}
}

// @Ensures r = 0
func HandsTwo() (r int) {
	l := &Latch{}
	useTwo(&Two{P: &Counter{}, S: l}) // want `the trusted contract of runsclaims.useTwo \(trusted.yaml:\d+\) cannot be used: its asserts lists interface\{ Ping\(\) \} for h, an interface with the method Ping, and what it holds may hold a value of runsclaims.Shutter, which lacks it`
	return l.n
}

// Source has a Ping and returns a Shutter.
type Source interface {
	// @Ensures True
	Ping()
	// @Ensures True
	Next() (s Shutter)
}

// Spring is a Source whose Next returns a Latch.
type Spring struct{ l *Latch }

// @Ensures True
func (s Spring) Ping() {}

// @Ensures True
func (s Spring) Next() (r Shutter) {
	if s.l == nil {
		return nil
	}
	return s.l
}

// useNext asserts what Next returns to an interface with Ping, which Source
// has and Shutter does not.
func useNext(p Source) {
	if q, ok := p.Next().(interface{ Ping() }); ok {
		q.Ping()
	}
}

// @Ensures r = 0
func HandsNext() (r int) {
	l := &Latch{}
	useNext(Spring{l: l}) // want `the trusted contract of runsclaims.useNext \(trusted.yaml:\d+\) cannot be used: its asserts lists interface\{ Ping\(\) \} for p, an interface with the method Ping, and what it holds may hold a value of runsclaims.Shutter, which lacks it`
	return l.n
}

// Latcher has a method that returns a Shutter.
type Latcher interface {
	// @Ensures True
	Latch() (r Shutter)
}

// LatchErr is an error whose method returns a Shutter.
type LatchErr struct{ l *Latch }

// @Ensures True
func (e LatchErr) Error() (s string) { return "latch" }

// @Ensures True
func (e LatchErr) Latch() (r Shutter) {
	if e.l == nil {
		return nil
	}
	return e.l
}

// consumeLatch asserts an error to Latcher, and what that
// returns to one with Ping. Over an error asserts may list both, so it is
// the conversion of a type whose method returns a Shutter that is refused.
func consumeLatch(e error) {
	if le, ok := e.(Latcher); ok {
		if q, ok := le.Latch().(interface{ Ping() }); ok {
			q.Ping()
		}
	}
}

// @Ensures r = 0
func HandsLatch() (r int) {
	l := &Latch{}
	consumeLatch(LatchErr{l: l}) // want `converting a LatchErr to an error is not supported: LatchErr.Latch returns a value of type Shutter, which can carry code that nothing checked against all that code given the error may call on it`
	return l.n
}
