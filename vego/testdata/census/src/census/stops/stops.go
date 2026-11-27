// Package stops holds functions with the refusals the census reports.
package stops

import (
	"encoding/json"
	"io"
	"net/http"
	"os"
	"sort"
)

// Channel makes a channel and receives from it.
func Channel() int {
	ch := make(chan int, 1)
	ch <- 1
	return <-ch
}

type pair struct{ a, b int }

// Address takes the address of a field, and then of an element.
func Address(p *pair, xs []int) int {
	q := &p.a
	r := &xs[0]
	return *q + *r
}

// Stat calls a function of the standard library without an entry.
func Stat(name string) bool {
	_, err := os.Stat(name)
	return err == nil
}

// Goroutine starts a goroutine whose literal is walked on its own.
func Goroutine(xs []int) {
	go func() {
		ch := make(chan int)
		_ = ch
	}()
}

// Generic is a generic function of the project, which the census does not
// look into.
func Generic[T any](x T) T { return x }

// HandedThenExit hands sort.Slice a comparison that the census refuses
// inside, and then ends the process outside it: the exit is no cause, and
// nothing of the hand-over outlives the refusal (F1 of the review).
func HandedThenExit(xs []int) {
	sort.Slice(xs, func(i, j int) bool {
		ch := make(chan int)
		_ = ch
		return xs[i] < xs[j]
	})
	os.Exit(1)
}

// Broken carries an annotation that cannot be read.
//
// @Requires x >
func Broken(x int) int { return x }

type record struct{ Name string }

// EncodeThenChannel encodes, appends, and makes a channel: the census goes
// on past the encoder's cut and the append (F9 of the review).
func EncodeThenChannel(w io.Writer, r record, xs []int) []int {
	_ = json.NewEncoder(w).Encode(r)
	xs = append(xs, 1)
	ch := make(chan int)
	_ = ch
	return xs
}

// Twice meets the same refusal on two lines and another one.
func Twice() {
	a := make(chan int)
	b := make(chan string)
	_, _ = a, b
	_, _ = os.Getwd()
}

// UnusableThenChannel calls what has an entry that cannot be used without a
// declaration, which cuts its path, and then appends and makes a channel
// (F9 of the review).
func UnusableThenChannel(name string, xs []int) []int {
	data, _ := os.ReadFile(name)
	xs = append(xs, len(data))
	ch := make(chan int)
	_ = ch
	return xs
}

type recorder struct{ w http.ResponseWriter }

// Wrap keeps the writer of a handler, which the ownership walk refuses
// with a report (F11 of the review).
func Wrap(w http.ResponseWriter) *recorder {
	return &recorder{w: w}
}

// Sink has a contract and takes a channel, which refuses it where it is
// declared.
//
// @Ensures True
type Sink func(ch chan int)

// Feed calls a value of Sink: the use counts as the channel that refused
// it (F12 of the review).
func Feed(s Sink) {
	s(nil)
}
