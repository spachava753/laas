package xb

import (
	"errors"
	"fmt"

	"census/xa"
)

// Load wraps an error of xa, whose origin xa's census publishes.
func Load(s string) error {
	if err := xa.Check(s); err != nil {
		return fmt.Errorf("load: %w", err)
	}
	return nil
}

// IsEmpty asks errors.Is of an error of xa.
func IsEmpty(s string) bool { return errors.Is(xa.Check(s), xa.ErrEmpty) }

// Op has a contract.
//
// @Ensures True
type Op func(x int) (y int)

// Make makes a value of Op from a function of xa that calls nothing.
func Make() Op { return xa.Plain }

type server struct{ store *xa.Store }

// handle calls a method of the owner it holds, which is xa's.
func (sv *server) handle(k string) int { return sv.store.Get(k) }
