package guide

import "io"

// The programs of the section "Functions that keep what they are given".

// Event is called with a number that is not negative.
//
// @Requires n >= 0
// @Ensures True
type Event func(n int)

// Hub keeps events and calls them when it fires. It is not verified; its
// methods have trusted contracts.
type Hub struct {
	events []Event
}

// Add keeps e in h.
func (h *Hub) Add(e Event) { h.events = append(h.events, e) }

// Fire calls every event kept in h with n.
func (h *Hub) Fire(n int) {
	for _, e := range h.events {
		e(n)
	}
}

// @Requires n >= 0
// @Ensures True
func record(n int) {}

// @Requires h != nil
// @Modifies h
// @Ensures True
func Subscribe(h *Hub) {
	h.Add(record)
	h.Fire(1)
}

// Prefetcher reads ahead from r on a goroutine of its own. Its constructor
// keeps r only in what it returns, and still has no true entry under keeps.
type Prefetcher struct {
	r     io.Reader
	ahead chan []byte
}

// NewPrefetcher returns a prefetcher over r.
func NewPrefetcher(r io.Reader) *Prefetcher {
	p := &Prefetcher{r: r, ahead: make(chan []byte, 1)}
	go p.fill()
	return p
}

func (p *Prefetcher) fill() {
	buf := make([]byte, 512)
	n, _ := p.r.Read(buf)
	p.ahead <- buf[:n]
}
