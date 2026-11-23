package guide

import "io"

// The programs of "What keeps an invariant between boundaries" in the
// guide (F30).

// Card is one card of a board.
type Card struct {
	Text string
	Tags []string
}

// Board bounds every card it holds.
//
// @Owns cards
// @Invariant cards != nil And (Forall k in cards : |cards[k].Text| <= 1000 And |cards[k].Tags| <= 10 And (Forall j in [0, |cards[k].Tags|) : |cards[k].Tags[j]| <= 100))
type Board struct {
	cards map[int]Card
}

// Answer writes a card's text twice: the writes through w keep the
// invariant of b, which nothing here reads.
//
// @Requires b != nil And w != nil
// @Modifies w
// @Ensures True
func (b *Board) Answer(w io.Writer, id int) {
	text := []byte(b.cards[id].Text)
	w.Write(text)
	w.Write(text)
}

// Longest finds the longest text, writing only its own result.
//
// @Requires b != nil
// @Ensures n <= 1000
func (b *Board) Longest() (n int) {
	// @Invariant n <= 1000
	for _, c := range b.cards {
		if len(c.Text) > n {
			n = len(c.Text)
		}
	}
	return n
}

// Gauge keeps its first level not negative.
//
// @Invariant |levels| > 0 And levels[0] >= 0
type Gauge struct {
	levels []int
}

// fill sets every element of xs to x.
//
// @Modifies xs
// @Ensures |xs| = 0 Or xs'[0] = x
func fill(xs []int, x int) {
	// @Invariant i = 0 Or xs[0] = x
	for i := range xs {
		xs[i] = x
	}
}

// filled sets every element of xs to x and returns how many.
//
// @Modifies xs
// @Ensures n = |xs| And (|xs| = 0 Or xs'[0] = x)
func filled(xs []int, x int) (n int) {
	// @Invariant i = 0 Or xs[0] = x
	for i := range xs {
		xs[i] = x
	}
	return len(xs)
}

// SetBelow assigns a level the invariant does not allow.
//
// @Requires g != nil
// @Modifies g.levels
// @Ensures True
func SetBelow(g *Gauge) {
	g.levels[0] = -1
} // want `vego: invariant of Gauge may not hold for g on return: levels\[0\] >= 0; it was not kept from entry, since levels\[0\] may have changed: the assignment to g\.levels\[0\] at kept\.go:84:2 may write it`

// FillBelow hands the levels to a function that writes them.
//
// @Requires g != nil
// @Modifies g.levels
// @Ensures True
func FillBelow(g *Gauge) {
	fill(g.levels, -1)
} // want `vego: invariant of Gauge may not hold for g on return: levels\[0\] >= 0; it was not kept from entry, since levels\[0\] may have changed: the call to fill at kept\.go:93:2 may write it`

// FillAndCount does the same in an assignment.
//
// @Requires g != nil
// @Modifies g.levels
// @Ensures True
func FillAndCount(g *Gauge) (n int) {
	n = filled(g.levels, -1)
	return n // want `vego: invariant of Gauge may not hold for g on return: levels\[0\] >= 0; it was not kept from entry, since levels\[0\] may have changed: the call to filled in the assignment to n at kept\.go:102:2 may write it`
}

// FillInLoop writes the levels in a loop.
//
// @Requires g != nil
// @Modifies g.levels
// @Ensures True
func FillInLoop(g *Gauge) {
	for i := range g.levels {
		g.levels[i] = -1
	}
} // want `vego: invariant of Gauge may not hold for g on return: levels\[0\] >= 0; it was not kept from entry, since levels\[0\] may have changed: the loop at kept\.go:112:2 may write it`

// FillIf writes the levels in the condition of an if statement.
//
// @Requires g != nil
// @Modifies g.levels
// @Ensures n <= 1
func FillIf(g *Gauge) (n int) {
	if filled(g.levels, -1) > 0 {
		n = 1
	}
	return n // want `vego: invariant of Gauge may not hold for g on return: levels\[0\] >= 0; it was not kept from entry, since levels\[0\] may have changed: the condition of the if statement at kept\.go:123:5 may write it`
}

// FillDeferred writes the levels in a deferred call.
//
// @Requires g != nil
// @Modifies g.levels
// @Ensures True
func FillDeferred(g *Gauge) {
	defer fill(g.levels, -1)
} // want `vego: invariant of Gauge may not hold for g on return: levels\[0\] >= 0; it was not kept from entry, since levels\[0\] may have changed: what runs at the return at kept\.go:136:1 may write it`

// drop removes a card, and may replace any of the others.
//
// @Requires b != nil
// @Modifies b
// @Ensures True
func drop(b *Board, id int) {
	delete(b.cards, id)
}

// DropThenAnswer removes a card through a call that lists the whole board,
// then writes through w, which may write what the call left.
//
// @Requires b != nil And w != nil
// @Modifies b, w
// @Ensures True
func DropThenAnswer(b *Board, w io.Writer, id int, p []byte) {
	drop(b, id)
	w.Write(p)
} // want `vego: invariant of Board may not hold for b on return: \(Forall k in cards : \|cards\[k\]\.Text\| <= 1000 And \|cards\[k\]\.Tags\| <= 10 And \(Forall j in \[0, \|cards\[k\]\.Tags\|\) : \|cards\[k\]\.Tags\[j\]\| <= 100\)\); it was not kept from the call to drop at kept\.go:154:2, since what it reads may have changed: the call to w\.Write at kept\.go:155:2 may write it`

// Clip is a text with tags, which the invariant of its type bounds.
//
// @Invariant |Text| <= 1000 And |Tags| <= 10 And (Forall j in [0, |Tags|) : |Tags[j]| <= 100)
type Clip struct {
	ID   int
	Text string
	Tags []string
}

// Clips appends a clip for each card: at the end of an iteration only the
// new clip is proved.
//
// @Requires b != nil And |b.cards| <= 1000
// @Ensures Forall i in [0, |out|) : valid(out[i])
func (b *Board) Clips() (out []Clip) {
	// @Visited done
	// @Invariant |out| <= |done| And (Forall i in [0, |out|) : valid(out[i]))
	for k, c := range b.cards {
		out = append(out, Clip{ID: k, Text: c.Text, Tags: c.Tags})
	}
	return out
}

// dropOne removes a card and lists only that entry.
//
// @Requires b != nil
// @Modifies b.cards[id]
// @Ensures ~has(b.cards', id)
func dropOne(b *Board, id int) {
	delete(b.cards, id)
}

// DropOneThenAnswer removes a card through a call that lists only its
// entry, then writes through w: the other cards are the ones b held on
// entry, which w's methods do not write.
//
// @Requires b != nil And w != nil
// @Modifies b.cards[id], w
// @Ensures True
func DropOneThenAnswer(b *Board, w io.Writer, id int, p []byte) {
	dropOne(b, id)
	w.Write(p)
}

// PushThenAnswer pushes onto a pile, then writes through w: what the push
// made is no part of what w's methods write.
//
// @Requires p != nil And w != nil And |p.items| = 0
// @Modifies p, w
// @Ensures |p.items'| = 1 And p.items'[0] = 5
func PushThenAnswer(p *Pile, w io.Writer, b []byte) {
	p.Push(5)
	w.Write(b)
}
