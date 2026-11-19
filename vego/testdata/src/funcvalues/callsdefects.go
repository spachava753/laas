package funcvalues

// MaybeNil calls a value that may be nil.
//
// @Requires 0 <= x <= 1000
// @Ensures True
func MaybeNil(f Mapper, x int) (y int) {
	return f(x) // want `vego: the function value f may be nil`
}

// OutOfRange calls a mapper with what its contract does not allow.
//
// @Requires f != nil
// @Ensures True
func OutOfRange(f Mapper) (y int) {
	return f(2000) // want `vego: precondition of f may not hold: 0 <= x <= 1000`
}

// NoPromise claims more than the contract of the type gives.
//
// @Requires f != nil
// @Ensures y <= 1000
func NoPromise(f Mapper) (y int) {
	return f(1) // want `vego: postcondition may not hold: y <= 1000`
}

// Unlisted lets an option change a configuration it does not list.
//
// @Requires c != nil And opt != nil
// @Ensures True
func Unlisted(c *Config, opt Option) {
	opt(c) // want `vego: opt may modify c, which Unlisted may not modify`
}

// Forgets knows nothing of the configuration after an option ran.
//
// @Requires c != nil And opt != nil And c.Retries = 3
// @Modifies c
// @Ensures c.Retries' = 3
func Forgets(c *Config, opt Option) {
	opt(c)
} // want `vego: postcondition may not hold: c.Retries' = 3`

// DeferredNil defers a call of a value that may be nil.
//
// @Requires s != nil And s.hits < 1000
// @Modifies s.hits
// @Ensures True
func DeferredNil(s *Host, done Done) {
	defer done(s) // want `vego: the function value done may be nil`
}

// NoContract calls a value of a named type without a contract.
//
// @Ensures True
func NoContract(f Plain) (y int) {
	return f(1) // want `vego: cannot verify NoContract: f has type funcvalues.Plain, which has no contract; declare a named function type with a contract and use it here`
}

// Plain is a function type without a contract.
type Plain func(x int) (y int)

// NotifyUnknown hands a report an error that came from outside.
//
// @Requires r != nil And e != nil
// @Ensures True
func NotifyUnknown(r Report, e error) {
	r(e) // want `vego: cannot verify NotifyUnknown: e is passed to the function value r and is an error whose origin is not known.*; the value may come from code that is not verified, which could run code through it that nobody has seen`
}

// Sink takes a function value without a contract.
//
// @Ensures True
type Sink func(f Plain)

// HandsPlain hands a value of a type without a contract to a value.
//
// @Requires s != nil
// @Ensures True
func HandsPlain(s Sink, f Plain) {
	s(f) // want `vego: cannot verify HandsPlain: f is passed to the function value s and is a value of type funcvalues.Plain, which can hold a function value whose type has no contract`
}

// Clearer can clear the handler of a server.
//
// @Requires s != nil
// @Modifies s.handler
// @Ensures s.handler' = nil
type Clearer func(s *Host) (n int)

// ClearedBeside reads the handler of a server beside a call that may clear
// it. Go does not fix whether s.handler is read before or after clear runs.
//
// @Requires s != nil And s.handler != nil And clear != nil
// @Modifies s.handler
// @Ensures True
func ClearedBeside(s *Host, clear Clearer) (y int) {
	return s.handler(clear(s)) // want `vego: s.handler may be read before or after the call to clear, which may change it` `vego: precondition of s.handler may not hold`
}


// Box keeps a count that is never negative.
//
// @Invariant n >= 0
type Box struct{ n int }

// MakeBox makes a box.
//
// @Ensures True
type MakeBox func() (b Box)

// FromValue relies on the invariant of what a value hands back, which may
// come from code that is not verified.
//
// @Requires mk != nil
// @Ensures r >= 0
func FromValue(mk MakeBox) (r int) {
	b := mk()
	return b.n // want `vego: postcondition may not hold: r >= 0`
}

// A value of a type without a contract does not become one of a type with a
// contract: nothing claims that it meets the contract.

// through calls a mapper.
//
// @Requires m != nil
// @Ensures 0 <= r <= 2000
func through(m Mapper) (r int) {
	return m(1)
}

// Convert converts a value of another named type.
//
// @Requires p != nil
// @Ensures 0 <= r <= 2000
func Convert(p Plain) (r int) {
	m := Mapper(p) // want `vego: cannot verify Convert: converting p to funcvalues.Mapper is not supported: a value of a function type is made only from`
	return m(1)
}

// Assign assigns a value of an unnamed type.
//
// @Requires u != nil
// @Ensures 0 <= r <= 2000
func Assign(u func(int) int) (r int) {
	var m Mapper = u // want `vego: cannot verify Assign: converting u to funcvalues.Mapper is not supported`
	return m(1)
}

// Pass passes a value of an unnamed type.
//
// @Requires u != nil
// @Ensures 0 <= r <= 2000
func Pass(u func(int) int) (r int) {
	return through(u) // want `vego: cannot verify Pass: converting u to funcvalues.Mapper is not supported`
}

// ConfigureClaims says that the options change nothing, which a loop that
// calls them cannot know: the loop forgets what Option may write.
//
// @Requires Forall i in [0, |opts|) : opts[i] != nil
// @Ensures cfg.Timeout = 0
func ConfigureClaims(opts []Option) (cfg Config) {
	for _, opt := range opts {
		opt(&cfg)
	}
	return cfg // want `vego: postcondition may not hold: cfg.Timeout = 0`
}

// ConfigureCounted is the same with a counted loop.
//
// @Requires Forall i in [0, |opts|) : opts[i] != nil
// @Ensures cfg.Timeout = 0
func ConfigureCounted(opts []Option) (cfg Config) {
	// @Invariant 0 <= i <= |opts|
	// @Variant |opts| - i
	for i := 0; i < len(opts); i++ {
		opts[i](&cfg)
	}
	return cfg // want `vego: postcondition may not hold: cfg.Timeout = 0`
}
