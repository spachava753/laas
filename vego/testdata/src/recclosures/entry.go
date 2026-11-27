package recclosures

// What memory held on entry refers to existed on entry: a map the function
// makes is none of the maps its parameter holds, at one key and at every
// key, while nothing writes the parameter's values.

// @Requires seen != g["a"]
// @Ensures True
func needOne(g map[string]map[string]bool, seen map[string]bool) {}

// @Requires Forall k in g : g[k] != seen
// @Ensures True
func needAll(g map[string]map[string]bool, seen map[string]bool) {}

// NewIsNoneOfOne verifies: g["a"] was in memory on entry.
//
// @Ensures True
func NewIsNoneOfOne(g map[string]map[string]bool) {
	seen := make(map[string]bool)
	needOne(g, seen)
}

// NewIsNoneOfAll verifies, under the quantifier of needAll.
//
// @Ensures True
func NewIsNoneOfAll(g map[string]map[string]bool) {
	seen := make(map[string]bool)
	needAll(g, seen)
}

// NewIsNoneOfField reads a pointer through a field and an element.
type holder struct{ next *holder }

// @Requires p != nil And |xs| > 0
// @Ensures True
func NewIsNoneOfField(p *holder, xs []*holder) {
	q := &holder{}
	// @Assert p.next != q
	// @Assert xs[0] != q
	_ = q
}

// Stored writes the new map into g before it asks: the region of g's
// values is written since entry, and nothing is known of what it holds.
//
// @Requires g != nil
// @Modifies g
// @Ensures True
func Stored(g map[string]map[string]bool) {
	seen := make(map[string]bool)
	g["a"] = seen
	needOne(g, seen) // want `precondition of needOne may not hold: seen != g\["a"\]`
}

// StoredField does the same through a pointer.
//
// @Requires p != nil
// @Modifies p
// @Ensures True
func StoredField(p *holder) {
	q := &holder{}
	p.next = q
	// @Assert p.next != q // want `assertion may not hold: p.next != q`
	_ = q
}

// makeChain is trusted; see testdata/trusted.yaml.
func makeChain() (p *holder) { return &holder{next: &holder{}} }

// NewChain reads what a new holder holds, which is new too: the region of
// next was not written since entry, but the holder did not exist then.
//
// @Ensures True
func NewChain() {
	p := makeChain()
	// @Assert p.next = nil // want `assertion may not hold: p.next = nil`
	_ = p
}
