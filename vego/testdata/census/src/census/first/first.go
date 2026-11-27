// Package first holds functions that carry the weakest contract in source,
// whose first refusal in the ordinary run the census must report as its
// first cause.
package first

import (
	"os"
	"strings"
)

type pair struct{ a, b int }

// @Ensures True
func Address(p *pair) (n int) {
	q := &p.a
	return *q
}

// @Ensures True
func Stat(name string) (found bool) {
	_, err := os.Stat(name)
	return err == nil
}

// @Ensures True
func Channel() (n int) {
	ch := make(chan int, 1)
	ch <- 1
	return <-ch
}

// @Ensures True
func Mixed(s string) (n int) {
	n = strings.Index(s, "a")
	go func() {}()
	ch := make(chan int)
	_ = ch
	return n
}
