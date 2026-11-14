package values

// The functions in this file have contracts that say when they succeed, with
// a success that needs a particular value somewhere in memory. The search
// for an input on which the contract forces success has to find it.

type quantity struct{ qty int }

// NeedsSeven succeeds for one value of a field behind a pointer.
//
// @ Requires p != nil
func NeedsSeven(p *quantity) (err error) {
	if p.qty != 7 {
		return errOutOfRange
	}
	return nil
}

//@ Ensures err = nil <-> p.qty = 7

// StartsWithSeven succeeds for one value of an element, among other numbers
// that the contract mentions.
//
// @ Requires |xs| < 100
func StartsWithSeven(xs []int) (err error) {
	if len(xs) > 0 && xs[0] == 7 {
		return nil
	}
	return errOutOfRange
}

//@ Ensures err = nil <-> (|xs| > 0 And xs[0] = 7)

// OneDigit succeeds for a string of one byte in a range.
func OneDigit(s string) (err error) {
	if len(s) == 1 && 48 <= s[0] && s[0] <= 57 {
		return nil
	}
	return errOutOfRange
}

//@ Ensures (|s| = 1 And 48 <= s[0] <= 57) -> err = nil

type stocked struct{ qty, price int }

// Stocked succeeds when a map of structs has the key.
func Stocked(m map[string]stocked, k string) (err error) {
	if _, ok := m[k]; !ok {
		return errOutOfRange
	}
	return nil
}

//@ Ensures err = nil <-> has(m, k)

// StockedFive succeeds for one value of a field of a struct in a map.
func StockedFive(m map[string]stocked, k string) (err error) {
	if it, ok := m[k]; !ok || it.qty != 5 {
		return errOutOfRange
	}
	return nil
}

//@ Ensures err = nil <-> (has(m, k) And m[k].qty = 5)

// LongInput always succeeds, and takes only slices longer than the usual
// samples.
//
// @ Requires |A| = 65
func LongInput(A []int) error { return nil }

//@ Ensures result = nil

type chain struct {
	next *chain
	v    int
}

// TwoLinks always succeeds, and takes only a chain of two.
//
// @ Requires n != nil And n.next != nil And n.next.v = 4
func TwoLinks(n *chain) error { return nil }

//@ Ensures result = nil

// ThreeLinks always succeeds too, but its inputs lie outside the search,
// which follows two pointers and no more. That is reported, in words that
// say that it is the search that found nothing.
//
// @ Requires n != nil And n.next != nil And n.next.next != nil
func ThreeLinks(n *chain) error { return nil } // want `the contract of ThreeLinks may also be met by a function that always returns an error: no simple input was found for which it forces success`

//@ Ensures result = nil

// SevenUnsaid says what success means and never that it happens; the wider
// search must not excuse it.
//
// @ Requires p != nil
func SevenUnsaid(p *quantity) (err error) { // want `the contract of SevenUnsaid may also be met by a function that always returns an error`
	if p.qty != 7 {
		return errOutOfRange
	}
	return nil
}

//@ Ensures err = nil -> p.qty = 7

// StockedNever demands a success that no map can give.
func StockedNever(m map[string]stocked, k string) (err error) { // want `the contract of StockedNever may also be met by a function that always returns an error`
	return errOutOfRange
}

//@ Ensures (has(m, k) And m[k].qty = 5 And m[k].qty = 6) -> err = nil

// EitherFails has two error results and returns an error on every call.
// One input makes the first nil and another the second, which is not a
// success.
func EitherFails(x int) (err1, err2 error) { // want `the contract of EitherFails may also be met by a function that always returns an error`
	if x == 0 {
		return nil, errOutOfRange
	}
	return errOutOfRange, nil
}

//@ Ensures x = 0 -> err1 = nil
//@ Ensures x = 1 -> err2 = nil

// BothSucceed has one input that makes both nil.
func BothSucceed(x int) (err1, err2 error) {
	if x == 0 {
		return nil, nil
	}
	return errOutOfRange, errOutOfRange
}

//@ Ensures x = 0 -> (err1 = nil And err2 = nil)

type shelf struct{ items map[string]*quantity }

// Reserve succeeds when a map holds a pointer to a struct with enough in
// it, which takes a sample of a map with an object behind its key.
//
// @ Requires w != nil And n >= 0
// @ Requires has(w.items, sku) -> w.items[sku] != nil
func Reserve(w *shelf, sku string, n int) error {
	it, ok := w.items[sku]
	if !ok || it.qty < n {
		return errOutOfRange
	}
	return nil
}

//@ Ensures result = nil <-> (has(w.items, sku) And w.items[sku].qty >= n)

// ReserveUnsaid has the same inputs and never says that it succeeds.
//
// @ Requires w != nil And n >= 0
// @ Requires has(w.items, sku) -> w.items[sku] != nil
func ReserveUnsaid(w *shelf, sku string, n int) error { // want `the contract of ReserveUnsaid may also be met by a function that always returns an error`
	return errOutOfRange
}

//@ Ensures result = nil -> (has(w.items, sku) And w.items[sku].qty >= n)
