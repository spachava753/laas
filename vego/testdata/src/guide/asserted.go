package guide

// The example of "What a function finds on what it is handed": a trusted
// function that asserts what it is handed to an interface that the
// parameter's type does not have.

// Pinger has a method with a contract.
type Pinger interface {
	// @Ensures True
	Ping()
}

// Meter counts.
type Meter struct{ n int }

// @Ensures True
func (t *Meter) Ping() {}

// Bump has no contract.
func (t *Meter) Bump() { t.n++ }

// use is trusted. Its entry lists interface{ Bump() } under asserts, which
// is true and a defect.
func use(p Pinger) {
	if b, ok := p.(interface{ Bump() }); ok {
		b.Bump()
	}
}

// @Ensures r = 0
func Hands() (r int) {
	t := &Meter{}
	use(t) // want `the trusted contract of guide.use \(trusted.yaml:\d+\) cannot be used: its asserts lists interface\{ Bump\(\) \} for p, an interface with the method Bump, and what it holds may hold a value of guide.Pinger, which lacks it: nothing checks a value converted to an interface against another interface it is later asserted to, so a function that calls what it finds that way runs code nobody checked, and no entry can claim it; only over an error, each method of which is checked where the error is made, may asserts list more`
	return t.n
}
