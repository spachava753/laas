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

// tell is trusted, and its entry lists neither runs nor keeps.
func tell(e error) {}

// @Ensures True
func TellsUnknown(e error) {
	tell(e) // want `^vego: cannot verify TellsUnknown: e is passed to tell, which is trusted, and is an error whose origin is not known; tell could run code through it that nobody has seen. If its contract holds whatever that code does, list e under runs in the contract if tell runs it only while the call lasts, or under keeps, with where it keeps it, if it keeps it in a result or a parameter for later calls$`
}
