// Package xa is called from xb, another package of the module, which reads
// what a census publishes of its functions (F35 of the review).
package xa

import "errors"

var ErrEmpty = errors.New("empty")

// Check returns ErrEmpty or nil: an error of known origin.
func Check(s string) error {
	if s == "" {
		return ErrEmpty
	}
	return nil
}

// Plain calls nothing.
func Plain(x int) int { return x }

// Store owns its map.
//
// @Owns items
type Store struct{ items map[string]int }

func NewStore() *Store { return &Store{items: map[string]int{}} }

func (s *Store) Get(k string) int { return s.items[k] }
