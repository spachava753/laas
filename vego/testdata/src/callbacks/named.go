package callbacks

// positive is verified, and asks only that i is not negative.
//
// @Requires 0 <= i
// @Ensures True
func positive(i int) (b bool) {
	return i > 0
}

// small asks for more than search promises.
//
// @Requires i < 3
// @Ensures True
func small(i int) (b bool) {
	return i < 2
}

func unannotated(i int) bool { return i > 0 }

// HandsFunction hands search a verified function.
//
// @Ensures True
func HandsFunction(n int) (k int) {
	return search(n, positive)
}

// HandsTooMuch hands one whose requires search does not promise.
//
// @Ensures True
func HandsTooMuch(n int) (k int) {
	return search(n, small) // want `vego: precondition of small may not hold: i < 3, in small run by search at named.go:\d+:\d+`
}

// HandsUnannotated hands one without a contract.
//
// @Ensures True
func HandsUnannotated(n int) (k int) {
	return search(n, unannotated) // want `cannot verify HandsUnannotated: it hands unannotated to search, and unannotated has no contract`
}

// bump counts in its receiver.
//
// @Requires c != nil
// @Modifies c
// @Ensures True
func (c *counter) bump(i int) {
	c.n = i
}

// HandsMethod hands each a method value whose receiver it may modify.
//
// @Requires c != nil
// @Modifies c
// @Ensures True
func HandsMethod(c *counter) {
	each(3, c.bump)
}

// HandsMethodOutside may not modify the receiver.
//
// @Requires c != nil
// @Ensures True
func HandsMethodOutside(c *counter) {
	each(3, c.bump) // want `vego: bump may modify c, which HandsMethodOutside may not modify; list it in a // @Modifies clause, as c\.n, in c.bump run by each at named.go:\d+:\d+`
}

// HandsNilReceiver hands a method value on a pointer that may be nil.
//
// @Modifies c
// @Ensures True
func HandsNilReceiver(c *counter) {
	each(3, c.bump) // want `vego: precondition of bump may not hold: c != nil, in c.bump run by each`
}

// tick counts once.
//
// @Requires c != nil
// @Modifies c
// @Ensures True
func (c *counter) tick() {
	c.m = 1
}

// TicksUpdated hands update a method that writes what update writes.
//
// @Requires c != nil
// @Modifies c
// @Ensures True
func TicksUpdated(c *counter) {
	update(c, c.tick) // want `vego: tick may modify c, which update may write itself while it runs the function it is handed; a function it is handed may not write what it may write, in c.tick run by update`
}

// ForgetsInLoop hands a method value in a loop; the loop forgets what it
// writes.
//
// @Requires c != nil
// @Modifies c
// @Ensures True
func ForgetsInLoop(c *counter) {
	c.n = 0
	for range 3 {
		// @Assert c.n = 0 // want `vego: assertion may not hold: c.n = 0`
		each(1, c.bump)
	}
}

// HandsValue hands each a value of a type with a contract.
//
// @Requires p != nil
// @Ensures True
func HandsValue(p Visitor) {
	each(3, p)
}

// HandsNil hands one that may be nil.
//
// @Ensures True
func HandsNil(p Visitor) {
	each(3, p) // want `vego: the function value p may be nil`
}

// HandsUncontracted hands a value whose type has no contract.
//
// @Ensures True
func HandsUncontracted(p func(i int)) {
	each(3, p) // want `cannot verify HandsUncontracted: p is passed to each as f, which each calls, and its type func\(i int\) has no contract`
}

// Strict asks for a number above 10.
//
// @Requires i > 10
type Strict func(i int)

// HandsStrict hands one whose contract each does not meet.
//
// @Requires p != nil
// @Ensures True
func HandsStrict(p Strict) {
	each(3, p) // want `vego: precondition of p may not hold: i > 10, in the function value p run by each`
}

// handsItself hands search itself, with nothing to show that this ends.
//
// @Ensures True
func handsItself(i int) (b bool) {
	return search(2, handsItself) >= 0 // want `recursive call needs a // @Variant annotation in the doc comment of handsItself to prove termination; the cycle: handsItself calls handsItself at named.go:\d+:\d+, in handsItself run by search`
}

// handsBack hands search a function that calls it back.
//
// @Ensures True
func handsBack() (b bool) {
	return search(2, callsBack) >= 0 // want `recursive call needs a // @Variant annotation in the doc comment of handsBack to prove termination; the cycle: handsBack calls callsBack at named.go:\d+:\d+, callsBack calls handsBack at named.go:\d+:\d+, in callsBack run by search`
}

// callsBack calls handsBack.
//
// @Ensures True
func callsBack(i int) (b bool) {
	return handsBack() // want `recursive call needs a // @Variant annotation in the doc comment of callsBack to prove termination`
}

// descends hands search itself, and search passes it smaller numbers.
//
// @Requires n >= 0
// @Variant n
// @Ensures True
func descends(n int) (b bool) {
	return search(n, descends) >= 0
}

// Loop makes a value that hands each another value, which in the end is
// itself, so it never returns.
//
// @Ensures True
func Loop() (b bool) {
	var p Visitor
	var v Visitor = func(i int) {
		each(1, p) // want `cannot verify Loop: the function literal used as a value hands the function value p to each, which calls it`
	}
	p = v
	v(0)
	return true
}

type box struct {
	f Visitor
}

// relay calls the value the box holds.
//
// @Requires b != nil And b.f != nil
// @Requires 0 <= i
// @Ensures True
func (b *box) relay(i int) {
	b.f(i) // want `this call may not end: \(\*box\).relay calls b.f\(i\) at named.go:\d+:\d+, which may run \(\*box\).relay`
}

// Relayed makes a value that hands each a method that calls a value.
//
// @Requires b != nil And b.f != nil
// @Ensures v != nil
func Relayed(b *box) (v Visitor) {
	return func(i int) {
		each(1, b.relay) // want `cannot verify Relayed: the function literal used as a value hands relay to each, which calls it, and relay may call through a function value`
	}
}

// visitAny does nothing.
//
// @Requires 0 <= i
// @Ensures True
func visitAny(i int) {}

// relayAll calls a value of its own.
//
// @Requires 0 <= i
// @Ensures True
func relayAll(i int) {
	vs := []Visitor{visitAny}
	vs[0](i) // want `this call may not end: relayAll calls vs\[0\]\(i\) at named.go:\d+:\d+, which may run relayAll`
}

// spread hands each a function that calls a value.
//
// @Requires 0 <= i
// @Ensures True
func spread(i int) {
	// What relayAll calls through a value may be spread itself, which is
	// made into a value below.
	each(i, relayAll) // want `this call may not end: spread calls relayAll at named.go:\d+:\d+, relayAll calls vs\[0\]\(i\) at named.go:\d+:\d+, which may run spread`
}

// Spreads makes spread into a value.
//
// @Ensures v != nil
func Spreads() (v Visitor) {
	return spread // want `cannot verify Spreads: spread may call through a function value`
}

// TickBeside hands both a method value that writes c.m and a literal that
// relies on c.m as it was at the call; each may run after the other.
//
// @Requires c != nil
// @Modifies c
// @Ensures True
func TickBeside(c *counter) {
	c.m = 0
	both(c.tick, func() {
		// @Assert c.m = 0 // want `vego: assertion may not hold: c.m = 0.*, in the function literal run by both`
	})
}

// Config is changed by an Option.
type Config struct {
	Timeout int
}

// Option changes a configuration.
//
// @Requires c != nil
// @Modifies c
type Option func(c *Config)

// HandsCaller hands each a literal that calls a value, which may write
// cfg; the runs and the state after the call forget it.
//
// @Requires p != nil
// @Ensures cfg.Timeout = 0
func HandsCaller(p Option) (cfg Config) {
	each(3, func(i int) { p(&cfg) })
	return cfg // want `vego: postcondition may not hold: cfg.Timeout = 0`
}

// SetsFirst relies, in a run, on cfg as it was at the call, although an
// earlier run may have called the value.
//
// @Requires p != nil
// @Ensures True
func SetsFirst(p Option) (cfg Config) {
	each(3, func(i int) {
		// @Assert cfg.Timeout = 0 // want `vego: assertion may not hold: cfg.Timeout = 0`
		p(&cfg)
	})
	return cfg
}

// Bumped is counted in.
type Bumped struct {
	N int
}

func inc(c *Bumped, f func()) {
	f()
	c.N++
}

// IncrementsBoxed hands inc a literal that writes the variable inc counts
// in, which lives in memory because its address is taken.
//
// @Ensures r = 1
func IncrementsBoxed() (r int) {
	var c Bumped
	inc(&c, func() {
		c.N = 100 // want `vego: c.N is assigned, which inc may write itself while it runs the function it is handed`
	})
	return c.N
}
