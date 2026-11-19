package funcvalues

// A function literal given a function type with a contract is a value. It is
// verified where it is made, against the contract of the type, as a function
// of its own: memory when it runs is unknown, a captured variable that
// nothing assigns again keeps the value it has here, and any other captured
// variable is unknown.

// Offset adds a captured amount, which is known to be small where the
// literal is made and never changes.
//
// @Requires 0 <= k <= 1000
// @Ensures f != nil
func Offset(k int) (f Mapper) {
	return func(x int) int {
		return x + k
	}
}

// WithTimeout returns an option that sets the timeout.
//
// @Ensures o != nil
func WithTimeout(d int) (o Option) {
	return func(c *Config) {
		c.Timeout = d
	}
}

// Defaults configures with two options made here.
//
// @Ensures True
func Defaults() (cfg Config) {
	return Configure([]Option{WithTimeout(5), func(c *Config) { c.Retries = 3 }})
}

// ApplyHalf halves every element through a literal passed as a mapper.
//
// @Requires Forall i in [0, |xs|) : 0 <= xs[i] <= 1000
// @Modifies xs
// @Ensures Forall i in [0, |xs|) : 0 <= xs'[i] <= 2000
func ApplyHalf(xs []int) {
	Apply(xs, func(x int) int { return x / 2 })
}

// Stored keeps a literal in a field and in a map.
//
// @Requires s != nil And routes != nil
// @Modifies s.handler, routes
// @Ensures s.handler' != nil
func Stored(s *Host, routes map[string]Mapper) {
	s.handler = func(x int) int { return x }
	routes["id"] = func(x int) int { return 0 }
}

// Named gives the literal a type in its declaration and passes it on.
//
// @Requires Forall i in [0, |xs|) : 0 <= xs[i] <= 1000
// @Modifies xs
// @Ensures True
func Named(xs []int) {
	var f Mapper = func(x int) int { return x }
	Apply(xs, f)
}

// Loop makes a literal in each iteration of a range loop; from Go 1.22 on
// each iteration has its own i, which the literal keeps.
//
// @Requires |out| = |xs| And Forall j in [0, |xs|) : 0 <= xs[j] <= 1000
// @Modifies out
// @Ensures True
func Loop(xs []int, out []Mapper) {
	for i, x := range xs {
		out[i] = func(y int) int {
			return x
		}
	}
}

// OwnOld names the literal's own parameter with old.
//
// @Ensures f != nil
func OwnOld() (f Mapper) {
	return func(x int) int {
		x = x / 2
		// @Assert 2 * x <= old(x)
		return x
	}
}

// Deferred makes a literal that defers a literal of its own.
//
// @Ensures d != nil
func DeferredLit() (d Done) {
	return func(s *Host) {
		defer func() { s.hits++ }()
	}
}

// Inner makes a literal inside a literal, which keeps what both captured.
//
// @Requires 0 <= k <= 500
// @Ensures p != nil
func Inner(k int) (p Picker) {
	return func() Mapper {
		return func(x int) int { return x + k }
	}
}
