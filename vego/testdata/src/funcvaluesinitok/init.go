// Package funcvaluesinitok is funcvaluesinit without the initialiser that
// calls Configure, so ErrX is known not to be nil.
package funcvaluesinitok

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


var ErrX = errors.New("x")

// Known is 1 because ErrX is not nil, which is known only in a package
// where no code of the package can run before ErrX has its value.
//
// @Ensures n = 1
func Known() (n int) {
	if ErrX != nil {
		return 1
	}
	return 0
}
