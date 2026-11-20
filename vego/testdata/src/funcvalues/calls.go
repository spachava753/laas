package funcvalues

import "errors"

// A named function type with a contract in its doc comment gives every
// value of the type that contract. A call through such a value is checked
// like a call of a function with that contract.

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
		xs[i] = f(xs[i]) // want `this\ call\ may\ not\ end:\ Apply\ calls\ f\(xs\[i\]\)\ at\ calls\.go:\d+:\d+,\ which\ may\ run\ the\ function\ literal\ at\ literaldefects\.go:\d+:\d+,\ the\ function\ literal\ at\ literaldefects\.go:\d+:\d+\ calls\ Apply\ at\ literaldefects\.go:\d+:\d+`
	}
}

// Twice applies a mapper to its own result, which needs the result in range
// again.
//
// @Requires f != nil And 0 <= x <= 1000
// @Ensures 0 <= y <= 2000
func Twice(f Mapper, x int) (y int) {
	y = f(x)
	if y > 1000 {
		return y
	}
	return f(y)
}

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

// ConfigureIn applies options to a configuration the caller holds.
//
// @Requires c != nil And Forall i in [0, |opts|) : opts[i] != nil
// @Modifies c
func ConfigureIn(c *Config, opts []Option) {
	for i := range opts {
		opts[i](c)
	}
}

// Host keeps a handler in a field.
type Host struct {
	hits    int
	handler Mapper
}

// Serve calls the handler of a server through the field.
//
// @Requires s != nil And s.handler != nil
// @Ensures 0 <= y <= 2000
func Serve(s *Host) (y int) {
	return s.handler(5)
}

// Route calls the handler a map holds for a name.
//
// @Requires has(routes, name) And routes[name] != nil
// @Ensures 0 <= y <= 2000
func Route(routes map[string]Mapper, name string, x int) (y int) {
	if x < 0 || x > 1000 {
		return 0
	}
	return routes[name](x)
}

// Done is called when something is finished.
//
// @Requires s != nil And s.hits < 1000
// @Modifies s.hits
// @Ensures s.hits' = s.hits + 1
type Done func(s *Host)

// Deferred calls a value when it returns, with the arguments it had at the
// defer statement.
//
// @Requires s != nil And done != nil And s.hits < 1000
// @Modifies s.hits
// @Ensures s.hits' = s.hits + 1
func Deferred(s *Host, done Done) {
	defer done(s)
}

// Picker returns a mapper.
//
// @Ensures f != nil
type Picker func() (f Mapper)

// CallResult calls the mapper a call returned.
//
// @Requires pick != nil
// @Ensures 0 <= y <= 2000
func CallResult(pick Picker) (y int) {
	return pick()(7)
}

// Report is told about an error.
//
// @Requires e != nil
type Report func(e error)

// NotifyMade hands a report an error made here, whose methods are those of
// the standard library.
//
// @Requires r != nil
// @Ensures True
func NotifyMade(r Report) {
	r(errors.New("failed"))
}

// Fetch gets a number, or fails.
//
// @Ensures err = nil -> 0 <= n <= 9
type Fetch func(key int) (n int, err error)

// FetchDigit cannot promise success: whether it fails is decided by the
// value it is given, as for a trusted function whose contract does not say
// when it succeeds.
//
// @Requires f != nil
// @Ensures err = nil -> 0 <= d <= 9
func FetchDigit(f Fetch) (d int, err error) {
	n, err := f(1)
	if err != nil {
		return 0, err
	}
	return n, nil
}
