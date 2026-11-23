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

// QChecker checks items, with a contract whose quantifier reads memory
// on entry (F43 of the review of O1).
type QChecker interface {
	// @Ensures r -> (Forall k in [0, |ps|) : ps[k] != nil)
	Check(ps []*QItem) (r bool)
}

// CountChecked uses a QChecker, whose contract the existence check accepts.
//
// @Requires c != nil
// @Ensures 0 <= n And n <= 1
func CountChecked(c QChecker, ps []*QItem) (n int) {
	if c.Check(ps) {
		return 1
	}
	return 0
}

// KeepsLengths keeps the length of every inner slice across a write, from
// a Requires that quantifies inside over pointers (F44 of the review of
// O1).
//
// @Requires b != nil And (Forall i in [0, |xss|) : |xss[i]| <= 5 And (Forall j in [0, |xss[i]|) : xss[i][j] != nil))
// @Modifies b
// @Ensures Forall i in [0, |xss|) : |xss'[i]| <= 5
func KeepsLengths(b QBook, xss [][]*QItem) {
	b.Record("x")
}

// KeepsSome keeps an Exists across a write.
//
// @Requires b != nil And (Exists k in [0, |items|) : items[k] != nil And items[k].Qty = 5)
// @Modifies b
// @Ensures Exists k in [0, |items|) : items'[k] != nil And items'[k].Qty = 5
func KeepsSome(b QBook, items []*QItem) {
	b.Record("x")
}

// KeepsSomeOf is KeepsSome through a book that also hands out memory
// within it.
//
// @Requires b != nil And (Exists k in [0, |items|) : items[k] != nil And items[k].Qty = 5)
// @Modifies b
// @Ensures Exists k in [0, |items|) : items'[k] != nil And items'[k].Qty = 5
func KeepsSomeOf(b QBookOf, items []*QItem) {
	b.Record("x")
}

// KeepsNested keeps a fact two quantifiers deep across a write. It is true
// and not proved at the default limit (F45 of the review of O1).
//
// @Requires b != nil And (Forall i in [0, |xss|) : Forall j in [0, |xss[i]|) : xss[i][j] != nil And xss[i][j].Qty >= 0)
// @Modifies b
// @Ensures Forall i in [0, |xss|) : Forall j in [0, |xss[i]|) : xss'[i][j].Qty >= 0
func KeepsNested(b QBook, xss [][]*QItem) {
	b.Record("x")
} // want `vego: postcondition may not hold: Forall i in \[0, \|xss\|\) : Forall j in \[0, \|xss\[i\]\|\) : xss'\[i\]\[j\].Qty >= 0`

// QOwners hands out items that lie in what it writes, each with an owner.
type QOwners interface {
	// @Receiver b
	// @Requires |name| <= 100
	// @Modifies b
	// @Ensures True
	Record(name string)

	// @Receiver b
	// @Ensures within(items, b) And (Forall k in [0, |items|) : items[k] != nil And items[k].Qty >= 0 And items[k].Owner != nil)
	Items() (items []*QItem)
}

// ReownedAcross makes the first item's owner one the book handed out and
// writes through the book. That every item has an owner is about the
// items' own fields, which the write keeps; what the new owner holds may
// change.
//
// @Requires b != nil And |items| > 0 And (Forall k in [0, |items|) : items[k] != nil And items[k].Owner != nil And |items[k].Owner.Name| <= 10)
// @Modifies b, items[0]
// @Ensures True
func ReownedAcross(b QOwners, items []*QItem) {
	src := b.Items()
	if len(src) == 0 || src[0].Owner.Name != "" {
		return
	}
	items[0].Owner = src[0].Owner
	b.Record("x")
	// @Assert Forall k in [0, |items|) : items[k].Owner != nil
	// @Assert Forall k in [0, |items|) : |items[k].Owner.Name| <= 10 // want `vego: assertion may not hold: Forall k in \[0, \|items\|\) : \|items\[k\].Owner.Name\| <= 10`
}

// QCheckingBook checks items and writes behind its receiver, so its
// contract lists a footprint and quantifies over memory on entry (F43 of
// the review of O1).
type QCheckingBook interface {
	// @Receiver b
	// @Modifies b
	// @Ensures r -> (Forall k in [0, |ps|) : ps[k] != nil)
	Check(ps []*QItem) (r bool)
}

// CheckedBy uses a QCheckingBook, whose contract the existence check
// accepts.
//
// @Requires b != nil
// @Modifies b
// @Ensures 0 <= n And n <= 1
func CheckedBy(b QCheckingBook, ps []*QItem) (n int) {
	if b.Check(ps) {
		return 1
	}
	return 0
}

// QHolder keeps a book in a field.
type QHolder struct{ B QBook }

// KeepsOneThroughField lists the footprint by a path through a field, which
// gets no separation, so nothing the other parameters reach is kept across
// the write, not one element (F47 of the review of O1; under Not built).
//
// @Requires h != nil And h.B != nil And it != nil And |it.Name| <= 100
// @Modifies h.B
// @Ensures |it.Name'| <= 100
func KeepsOneThroughField(h *QHolder, it *QItem) {
	h.B.Record("x")
} // want `vego: postcondition may not hold: \|it.Name'\| <= 100`
