package values

// The functions in this file have contracts that say when they succeed, with
// a success that needs a particular value somewhere in memory. The search
// for an input on which the contract forces success has to find it.

type quantity struct{ qty int }

// NeedsSeven succeeds for one value of a field behind a pointer.
//
// @Requires p != nil
// @Ensures err = nil <-> p.qty = 7
func NeedsSeven(p *quantity) (err error) {
	if p.qty != 7 {
		return errOutOfRange
	}
	return nil
}

// StartsWithSeven succeeds for one value of an element, among other numbers
// that the contract mentions.
//
// @Requires |xs| < 100
// @Ensures err = nil <-> (|xs| > 0 And xs[0] = 7)
func StartsWithSeven(xs []int) (err error) {
	if len(xs) > 0 && xs[0] == 7 {
		return nil
	}
	return errOutOfRange
}

// OneDigit succeeds for a string of one byte in a range.
//
// @Ensures (|s| = 1 And 48 <= s[0] <= 57) -> err = nil
func OneDigit(s string) (err error) {
	if len(s) == 1 && 48 <= s[0] && s[0] <= 57 {
		return nil
	}
	return errOutOfRange
}

type stocked struct{ qty, price int }

// Stocked succeeds when a map of structs has the key.
//
// @Ensures err = nil <-> has(m, k)
func Stocked(m map[string]stocked, k string) (err error) {
	if _, ok := m[k]; !ok {
		return errOutOfRange
	}
	return nil
}

// StockedFive succeeds for one value of a field of a struct in a map.
//
// @Ensures err = nil <-> (has(m, k) And m[k].qty = 5)
func StockedFive(m map[string]stocked, k string) (err error) {
	if it, ok := m[k]; !ok || it.qty != 5 {
		return errOutOfRange
	}
	return nil
}

// LongInput always succeeds, and takes only slices longer than the usual
// samples.
//
// @Requires |A| = 65
// @Ensures result = nil
func LongInput(A []int) (result error) { return nil }

type chain struct {
	next *chain
	v    int
}

// TwoLinks always succeeds, and takes only a chain of two.
//
// @Requires n != nil And n.next != nil And n.next.v = 4
// @Ensures result = nil
func TwoLinks(n *chain) (result error) { return nil }

// ThreeLinks always succeeds too, but its inputs lie outside the search,
// which follows two pointers and no more. That is reported, in words that
// say that it is the search that found nothing.
//
// @Requires n != nil And n.next != nil And n.next.next != nil
// @Ensures result = nil
func ThreeLinks(n *chain) (result error) { return nil } // want `the contract of ThreeLinks may also be met by a function that always returns an error: no simple input was found for which it forces success`

// SevenUnsaid says what success means and never that it happens; the wider
// search must not excuse it.
//
// @Requires p != nil
// @Ensures err = nil -> p.qty = 7
func SevenUnsaid(p *quantity) (err error) { // want `the contract of SevenUnsaid may also be met by a function that always returns an error`
	if p.qty != 7 {
		return errOutOfRange
	}
	return nil
}

// StockedNever demands a success that no map can give.
//
// @Ensures (has(m, k) And m[k].qty = 5 And m[k].qty = 6) -> err = nil
func StockedNever(m map[string]stocked, k string) (err error) { // want `the contract of StockedNever may also be met by a function that always returns an error`
	return errOutOfRange
}

// EitherFails has two error results and returns an error on every call.
// One input makes the first nil and another the second, which is not a
// success.
//
// @Ensures x = 0 -> err1 = nil
// @Ensures x = 1 -> err2 = nil
func EitherFails(x int) (err1, err2 error) { // want `the contract of EitherFails may also be met by a function that always returns an error`
	if x == 0 {
		return nil, errOutOfRange
	}
	return errOutOfRange, nil
}

// BothSucceed has one input that makes both nil.
//
// @Ensures x = 0 -> (err1 = nil And err2 = nil)
func BothSucceed(x int) (err1, err2 error) {
	if x == 0 {
		return nil, nil
	}
	return errOutOfRange, errOutOfRange
}

type shelf struct{ items map[string]*quantity }

// Reserve succeeds when a map holds a pointer to a struct with enough in
// it, which takes a sample of a map with an object behind its key.
//
// @Requires w != nil And n >= 0
// @Requires has(w.items, sku) -> w.items[sku] != nil
// @Ensures result = nil <-> (has(w.items, sku) And w.items[sku].qty >= n)
func Reserve(w *shelf, sku string, n int) (result error) {
	it, ok := w.items[sku]
	if !ok || it.qty < n {
		return errOutOfRange
	}
	return nil
}

// ReserveUnsaid has the same inputs and never says that it succeeds.
//
// @Requires w != nil And n >= 0
// @Requires has(w.items, sku) -> w.items[sku] != nil
// @Ensures result = nil -> (has(w.items, sku) And w.items[sku].qty >= n)
func ReserveUnsaid(w *shelf, sku string, n int) (result error) { // want `the contract of ReserveUnsaid may also be met by a function that always returns an error`
	return errOutOfRange
}

type looped struct {
	next map[int]*looped
	v    int
}

// LoopedMap takes a map of pointers to structs that hold such a map again.
// The samples follow it two pointers deep and stop.
//
// @Ensures result = nil
func LoopedMap(m map[int]*looped) (result error) { return nil }

type ping struct{ to map[string]*pong }

type pong struct {
	back *ping
	v    int
}

// PingPong takes two types that reach each other through a map and a
// pointer.
//
// @Ensures result = nil
func PingPong(p *ping) (result error) { return nil }

// TwoMapsDeep succeeds for a value two pointers into such a map.
//
// @Requires has(m, 1) And m[1] != nil And has(m[1].next, 1) And m[1].next[1] != nil
// @Ensures err = nil <-> m[1].next[1].v = 9
func TwoMapsDeep(m map[int]*looped) (err error) {
	if m[1].next[1].v != 9 {
		return errOutOfRange
	}
	return nil
}

// ThreeMapsDeep needs a third pointer, which no sample has.
//
// @Requires has(m, 1) And m[1] != nil And has(m[1].next, 1) And m[1].next[1] != nil
// @Requires has(m[1].next[1].next, 1) And m[1].next[1].next[1] != nil
// @Ensures result = nil
func ThreeMapsDeep(m map[int]*looped) (result error) { return nil } // want `the contract of ThreeMapsDeep may also be met by a function that always returns an error: no simple input was found`

// CountHole can only fail: a map with five keys has a key, so the loop
// returns an error. Its contract forces success only for a map that has
// five keys and none of them, which no map is, although the logic, which
// does not tie the count of a map to its keys, has such a state. A model of
// the logic must not count as an input.
//
// @Ensures (Forall k in Z : ~has(m, k)) And |m| = 5 -> err = nil
func CountHole(m map[int]int) (err error) { // want `the contract of CountHole may also be met by a function that always returns an error: no simple input was found`
	if len(m) == 5 {
		for k := range m {
			_ = k
			// @Assert has(m, k)
			return errOutOfRange
		}
		return nil
	}
	return errOutOfRange
}
