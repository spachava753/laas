package footprints

// Facts under a quantifier about what the other parameters reach, kept
// across a write through a footprint as a fact about one element is (O1 of
// the orchestrator's review of part 1).

// QBook records names behind its receiver.
type QBook interface {
	// @Receiver b
	// @Requires |name| <= 100
	// @Modifies b
	// @Ensures True
	Record(name string)
}

// QOwner names an owner.
type QOwner struct{ Name string }

// QItem has a name, an owner, tags, and a quantity.
type QItem struct {
	Name  string
	Owner *QOwner
	Tags  []string
	Qty   int
}

// recordOne records the name of one item.
//
// @Requires b != nil And it != nil And |it.Name| <= 100
// @Modifies b
// @Ensures True
func recordOne(b QBook, it *QItem) {
	b.Record(it.Name)
}

// RecordAllThrough records each item through a helper, which the
// invariant about every item survives.
//
// @Requires b != nil And (Forall k in [0, |items|) : items[k] != nil And |items[k].Name| <= 100)
// @Modifies b
// @Ensures True
func RecordAllThrough(b QBook, items []*QItem) {
	// @Invariant Forall k in [0, |items|) : items[k] != nil And |items[k].Name| <= 100
	for _, it := range items {
		recordOne(b, it)
	}
}

// RecordAll records each item directly.
//
// @Requires b != nil And (Forall k in [0, |items|) : items[k] != nil And |items[k].Name| <= 100)
// @Modifies b
// @Ensures True
func RecordAll(b QBook, items []*QItem) {
	// @Invariant Forall k in [0, |items|) : items[k] != nil And |items[k].Name| <= 100
	for _, it := range items {
		b.Record(it.Name)
	}
}

// KeepsEvery keeps a fact about every item across a write.
//
// @Requires b != nil And (Forall k in [0, |items|) : items[k] != nil And |items[k].Name| <= 100)
// @Modifies b
// @Ensures Forall k in [0, |items|) : |items'[k].Name| <= 100
func KeepsEvery(b QBook, items []*QItem) {
	b.Record("x")
}

// KeepsOwners keeps a fact two pointers deep.
//
// @Requires b != nil And (Forall k in [0, |items|) : items[k] != nil And items[k].Owner != nil And |items[k].Owner.Name| <= 100)
// @Modifies b
// @Ensures Forall k in [0, |items|) : |items'[k].Owner.Name| <= 100
func KeepsOwners(b QBook, items []*QItem) {
	b.Record("x")
}

// KeepsTags keeps a fact about a slice field of every item.
//
// @Requires b != nil And (Forall k in [0, |items|) : items[k] != nil And |items[k].Tags| > 0 And |items[k].Tags[0]| <= 100)
// @Modifies b
// @Ensures Forall k in [0, |items|) : |items'[k].Tags[0]| <= 100
func KeepsTags(b QBook, items []*QItem) {
	b.Record("x")
}

// KeepsMapValues keeps a fact about what every value of a map points to.
//
// @Requires b != nil And (Forall k in m : m[k] != nil And m[k].Qty >= 0)
// @Modifies b
// @Ensures Forall k in m : m'[k].Qty >= 0
func KeepsMapValues(b QBook, m map[string]*QItem) {
	b.Record("x")
}

// countValid promises a fact about every item it is handed.
//
// @Requires b != nil And (Forall k in [0, |items|) : items[k] != nil)
// @Modifies b
// @Ensures Forall k in [0, |items|) : items'[k] != nil And items'[k].Qty = items[k].Qty
func countValid(b QBook, items []*QItem) {
	b.Record("x")
}

// KeepsAfterCallee keeps, across a second write, the fact a callee
// promised about every item.
//
// @Requires b != nil And (Forall k in [0, |items|) : items[k] != nil And items[k].Qty >= 0)
// @Modifies b
// @Ensures Forall k in [0, |items|) : items'[k].Qty >= 0
func KeepsAfterCallee(b QBook, items []*QItem) {
	countValid(b, items)
	b.Record("y")
}

// QLister hands out items that may lie in what a QBook writes.
type QLister interface {
	// @Ensures |items| <= 100 And (Forall k in [0, |items|) : items[k] != nil And |items[k].Name| <= 100)
	List() (items []*QItem)
}

// ListedAcross keeps, across a write, a fact about items that an
// interface value handed out, whose memory the write may reach: the fact
// is not kept.
//
// @Requires b != nil And l != nil
// @Modifies b
// @Ensures True
func ListedAcross(b QBook, l QLister) {
	items := l.List()
	b.Record("x")
	// @Assert Forall k in [0, |items|) : |items[k].Name| <= 100 // want `vego: assertion may not hold: Forall k in \[0, \|items\|\) : \|items\[k\].Name\| <= 100`
	_ = items
}

// QBookOf hands out the items it holds behind its receiver.
type QBookOf interface {
	// @Receiver b
	// @Requires |name| <= 100
	// @Modifies b
	// @Ensures True
	Record(name string)

	// @Receiver b
	// @Ensures within(items, b) And (Forall k in [0, |items|) : items[k] != nil And items[k].Qty >= 0)
	Items() (items []*QItem)
}

// OwnItemsAcross keeps a fact about the items the book itself holds,
// which its write may change: it is not kept.
//
// @Requires b != nil
// @Modifies b
// @Ensures True
func OwnItemsAcross(b QBookOf) {
	items := b.Items()
	b.Record("x")
	// @Assert Forall k in [0, |items|) : items[k] != nil // want `vego: assertion may not hold: Forall k in \[0, \|items\|\) : items\[k\] != nil`
	_ = items
}

// ItemsOfBookAcross keeps, in a slice it made, a pointer that the book
// handed out. The slice is kept across the write, but what its elements point
// to may be written: the fact about them is not kept.
//
// @Requires b != nil
// @Modifies b
// @Ensures True
func ItemsOfBookAcross(b QBookOf) {
	src := b.Items()
	if len(src) == 0 {
		return
	}
	items := []*QItem{src[0]}
	// @Assert Forall k in [0, |items|) : items[k] != nil And items[k].Qty >= 0
	b.Record("x")
	// @Assert Forall k in [0, |items|) : items[k] != nil
	// @Assert Forall k in [0, |items|) : items[k].Qty >= 0 // want `vego: assertion may not hold: Forall k in \[0, \|items\|\) : items\[k\].Qty >= 0`
	_ = items
}
