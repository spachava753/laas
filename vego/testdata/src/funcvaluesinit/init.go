// Package funcvaluesinit calls, while its variables are initialised, a
// function that calls through a function value. Code that the value runs
// could then run before ErrX has its value, so the package relies on none of
// its error variables.
package funcvaluesinit

import "errors"

// Config is configured by options.
type Config struct{ n int }

// Option changes a configuration.
//
// @Requires c != nil
// @Modifies c
type Option func(c *Config)

// Configure applies options.
//
// @Requires c != nil And Forall i in [0, |opts|) : opts[i] != nil
// @Modifies c
// @Ensures out = c
func Configure(c *Config, opts []Option) (out *Config) {
	for _, opt := range opts {
		opt(c)
	}
	return c
}

var cfg = Configure(&Config{}, nil)

var ErrX = errors.New("x")

// Known is 1 because ErrX is not nil, which is known only in a package
// where no code of the package can run before ErrX has its value.
//
// @Ensures n = 1
func Known() (n int) {
	if ErrX != nil { // want `vego: cannot verify Known: ErrX is not known to have its value yet when this runs: a function value or an interface method is called at init.go:\d+ while the variables of the package are initialised`
		return 1
	}
	return 0
}
