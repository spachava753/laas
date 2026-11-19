// Package ordering holds programs in which a call that modifies memory
// stands inside a larger expression. Go fixes the order of the calls among
// themselves, but not when the other operands are read relative to them. A
// read that may give two values is reported; one that gives the same value
// in every order Go allows verifies.
package ordering

type Counter struct {
	n int
	m int
}

// @Requires c != nil And c.n < 1000
// @Modifies c.n
// @Ensures c.n' = c.n + 1 And result = c.n'
func (c *Counter) Inc() (result int) {
	c.n++
	return c.n
}

// @Requires c != nil And c.m < 1000
// @Modifies c.m
// @Ensures c.m' = c.m + 1 And result = c.m'
func (c *Counter) IncM() (result int) {
	c.m++
	return c.m
}

// @Requires c != nil
// @Modifies c.n
// @Ensures c.n' = x
func (c *Counter) Set(x int) {
	c.n = x
}

// @Ensures result = c.n
func (c Counter) Value() (result int) {
	return c.n
}

// @Requires -1000 <= c.n <= 1000 And -1000 <= x <= 1000
// @Ensures result = c.n + x
func (c Counter) Plus(x int) (result int) {
	return c.n + x
}

// @Ensures result = x
func id(x int) (result int) {
	return x
}

// @Requires -1000 <= a <= 1000 And -1000 <= b <= 1000
// @Ensures result = a - b
func pair(a, b int) (result int) {
	return a - b
}

// IncTwice adds what two calls return. Go runs them left to right.
//
// @Requires c != nil And 0 <= c.n < 100
// @Modifies c.n
// @Ensures result = 2*c.n + 3 And c.n' = c.n + 2
func IncTwice(c *Counter) (result int) {
	return c.Inc() + c.Inc()
}

// Difference passes what two calls return to a third.
//
// @Requires c != nil And 0 <= c.n < 100
// @Modifies c.n
// @Ensures result = -1
func Difference(c *Counter) (result int) {
	return pair(c.Inc(), c.Inc())
}

// IncInto stores what a call returns into what the call changes. The store
// comes after the call.
//
// @Requires c != nil And 0 <= c.n < 100
// @Modifies c.n
// @Ensures c.n' = c.n + 1
func IncInto(c *Counter) {
	c.n = c.Inc()
}

// AddUp adds to a variable the verifier holds, which no call can change.
//
// @Requires c != nil And 0 <= c.n < 100
// @Modifies c.n
// @Ensures result = 2*c.n + 3
func AddUp(c *Counter) (result int) {
	total := c.Inc()
	total += c.Inc()
	return total
}

// OtherField reads a field that the call leaves as it is.
//
// @Requires c != nil And 0 <= c.n < 100 And 0 <= c.m < 100
// @Modifies c.n
// @Ensures result = c.m + c.n + 1
func OtherField(c *Counter) (result int) {
	return c.m + c.Inc()
}

// Separate reads a counter that the call is known not to change.
//
// @Requires c != nil And d != nil And c != d And 0 <= c.n < 100 And 0 <= d.n < 100
// @Modifies c.n
// @Ensures result = d.n + c.n + 1
func Separate(c, d *Counter) (result int) {
	return d.n + c.Inc()
}

// LaterCall reads c.n for id, which runs before Inc.
//
// @Requires c != nil And 0 <= c.n < 100
// @Modifies c.n
// @Ensures result = 2*c.n + 1
func LaterCall(c *Counter) (result int) {
	return id(c.n) + c.Inc()
}

// AfterDecision reads c.n on the right of &&, which Go evaluates after the
// left operand and so after Inc.
//
// @Requires c != nil And 0 <= c.n < 100
// @Modifies c.n
// @Ensures result <-> c.n + 1 > 50
func AfterDecision(c *Counter) (result bool) {
	return c.Inc() > 0 && c.n > 50
}

// InCondition calls Inc in the condition of an if.
//
// @Requires c != nil And 0 <= c.n < 100
// @Modifies c.n
// @Ensures result <-> c.n = 0
func InCondition(c *Counter) (result bool) {
	if c.Inc() == 1 {
		return true
	}
	return false
}

// InSwitch calls Inc in the tag of a switch.
//
// @Requires c != nil And 0 <= c.n < 100
// @Modifies c.n
// @Ensures result <-> c.n = 1
func InSwitch(c *Counter) (result bool) {
	switch c.Inc() {
	case 2:
		return true
	}
	return false
}

// DeferArgument evaluates a modifying call as the argument of a deferred
// call.
//
// @Requires c != nil And d != nil And c != d And 0 <= c.n < 100
// @Modifies c.n, d.n
// @Ensures d.n' = c.n + 1 And c.n' = c.n + 1
func DeferArgument(c, d *Counter) {
	defer d.Set(c.Inc())
}

// BoxedField reads one field of a variable whose address is taken. IncM
// changes only the other field.
//
// @Ensures result = 3
func BoxedField() (result int) {
	var x Counter
	x.n = 2
	return x.n + x.IncM()
}

// PointerReceiver calls a method with a pointer receiver on a variable that
// lives in memory, which reads nothing of it.
//
// @Ensures x.n = 7
func PointerReceiver() (x Counter) {
	var c Counter
	c.Set(c.IncM() + 6)
	return c
}

// FreshSlice reads an element of a slice that the expression allocates.
//
// @Requires c != nil And 0 <= c.n < 100 And 0 <= i < 2
// @Modifies c.n
// @Ensures result = i + c.n + 2
func FreshSlice(c *Counter, i int) (result int) {
	return []int{1, 2}[i] + c.Inc()
}

// FreshStruct reads a field of a struct that the expression allocates, of
// the type the call changes.
//
// @Requires c != nil And 0 <= c.n < 100
// @Modifies c.n
// @Ensures result = c.n + 2
func FreshStruct(c *Counter) (result int) {
	return (&Counter{n: 1}).n + c.Inc()
}

// FreshReceiver calls a value method on a struct that the expression
// allocates.
//
// @Requires c != nil And 0 <= c.n < 100
// @Modifies c.n
// @Ensures result = c.n + 2
func FreshReceiver(c *Counter) (result int) {
	return (&Counter{n: 1}).Value() + c.Inc()
}

type Buf struct {
	a []int
}

// @Requires b != nil And |b.a| = 2
// @Modifies b.a
// @Ensures b.a'[0] = 7 And b.a'[1] = b.a[1] And result = 0
func set(b *Buf) (result int) {
	b.a[0] = 7
	return 0
}

// IndexAfter reads an element at an index that a call returns, so after the
// call. The slice itself may be read before or after it, which is the same.
//
// @Requires b != nil And |b.a| = 2
// @Modifies b.a
// @Ensures result = 7
func IndexAfter(b *Buf) (result int) {
	return b.a[set(b)]
}

type List struct {
	items []int
	k     int
}

// @Requires l != nil And l.k < 1000
// @Modifies l.k
// @Ensures l.k' = l.k + 1 And result = 0
func (l *List) Bump() (result int) {
	l.k++
	return 0
}

// @Requires l != nil
// @Modifies l
// @Ensures |l.items'| = 0 And l.k' = l.k And result = 0
func (l *List) Reset() (result int) {
	l.items = nil
	return 0
}

// RangeBump calls Bump in the range expression, which also reads l.items.
//
// @Requires l != nil And l.k < 1000
// @Modifies l.k
// @Ensures l.k' = l.k + 1
func RangeBump(l *List) {
	for range l.items[l.Bump():] {
	}
}

// SameField reads c.n, which Inc changes. Go may read it before or after
// the call.
//
// @Requires c != nil And 0 <= c.n < 100
// @Modifies c.n
func SameField(c *Counter) (result int) {
	return c.n + c.Inc() // want `vego: c.n may be read before or after the call to Inc, which may change it, and Go does not fix the order; split the statement so that the order is the one you mean`
}

// MaybeSame reads a counter that may be the one Inc changes.
//
// @Requires c != nil And d != nil And 0 <= c.n < 100 And 0 <= d.n < 100
// @Modifies c.n
func MaybeSame(c, d *Counter) (result int) {
	return d.n + c.Inc() // want `vego: d.n may be read before or after the call to Inc`
}

// InLiteral reads c.n beside a call that changes it in a slice literal.
//
// @Requires c != nil And 0 <= c.n < 100
// @Modifies c.n
func InLiteral(c *Counter) (result []int) {
	return []int{c.n, c.Inc()} // want `vego: c.n may be read before or after the call to Inc`
}

// AsArgument reads c.n for pair, which runs after Inc. Inc is not ordered
// with the read.
//
// @Requires c != nil And 0 <= c.n < 100
// @Modifies c.n
func AsArgument(c *Counter) (result int) {
	return pair(c.n, c.Inc()) // want `vego: c.n may be read before or after the call to Inc`
}

// EarlierCall reads c.n for id, which runs after Inc. The read itself is not
// ordered with Inc.
//
// @Requires c != nil And 0 <= c.n < 100
// @Modifies c.n
func EarlierCall(c *Counter) (result int) {
	return c.Inc() + id(c.n) // want `vego: c.n may be read before or after the call to Inc`
}

// AddAssign reads c.n once, as an operand, beside the call.
//
// @Requires c != nil And 0 <= c.n < 100
// @Modifies c.n
func AddAssign(c *Counter) {
	c.n += c.Inc() // want `vego: c.n may be read before or after the call to Inc`
}

// TwoResults returns c.n and the result of Inc.
//
// @Requires c != nil And 0 <= c.n < 100
// @Modifies c.n
func TwoResults(c *Counter) (a, b int) {
	return c.n, c.Inc() // want `vego: c.n may be read before or after the call to Inc`
}

// Negated reads c.n under a negation.
//
// @Requires c != nil And 0 <= c.n < 100
// @Modifies c.n
func Negated(c *Counter) (result int) {
	return -c.n + c.Inc() // want `vego: c.n may be read before or after the call to Inc`
}

// ValueReceiver copies *c for Plus, which Go may do before or after Inc.
//
// @Requires c != nil And 0 <= c.n < 100
// @Modifies c.n
func ValueReceiver(c *Counter) (result int) {
	return c.Plus(c.Inc()) // want `vego: the receiver of c.Plus may be read before or after the call to Inc`
}

// BoxedSame reads the field of a variable that IncM changes.
//
// @Ensures True
func BoxedSame() (result int) {
	var x Counter
	return x.m + x.IncM() // want `vego: x.m may be read before or after the call to IncM`
}

// DeferRead reads c.n for a deferred call beside a call that changes it.
//
// @Requires c != nil And d != nil And c != d And 0 <= c.n < 100
// @Modifies c.n, d.n
func DeferRead(c, d *Counter) {
	defer d.Set(c.n + c.Inc()) // want `vego: c.n may be read before or after the call to Inc`
}

type Holder struct {
	c *Counter
}

// @Requires h != nil
// @Modifies h
// @Ensures fresh(h.c) And h.c'.n = 0 And result = 5
func replace(h *Holder) (result int) {
	h.c = &Counter{}
	return 5
}

// TargetOperand assigns through h.c, which replace changes. Go evaluates
// h.c, an operand of the target, before or after the call.
//
// @Requires h != nil And h.c != nil
// @Modifies h, h.c
func TargetOperand(h *Holder) {
	h.c.n = replace(h) // want `vego: h.c may be read before or after the call to replace`
}

// RangeReset ranges over l.items beside a call that replaces it.
//
// @Requires l != nil
// @Modifies l
func RangeReset(l *List) {
	for range l.items[l.Reset():] { // want `vego: l.items may be read before or after the call to Reset`
	}
}

// @Requires m != nil And |m| < 1000
// @Modifies m
// @Ensures m'[1] = 5 And result = 0
func put(m map[int]int) (result int) {
	m[1] = 5
	return 0
}

// MapRead reads an entry that put changes.
//
// @Requires m != nil And |m| < 1000
// @Modifies m
func MapRead(m map[int]int) (result int) {
	return m[1] + put(m) // want `vego: m\[1\] may be read before or after the call to put`
}

// MapLength reads the number of keys, which put may change.
//
// @Requires m != nil And |m| < 1000
// @Modifies m
func MapLength(m map[int]int) (result int) {
	return len(m) + put(m) // want `vego: len\(m\) may be read before or after the call to put`
}

type P struct {
	list []int
}

// @Requires |t| = 1
// @Modifies t
// @Ensures t'[0] = 9 And result = p
func touch(p *P, t []int) (result *P) {
	t[0] = 9
	return p
}

// @Ensures result = 5
func five() (result int) {
	return 5
}

// CopyRead moves t to a new array. Since append is not ordered like a call,
// Go may copy the elements of t before or after touch changes them.
//
// @Requires p != nil And |t| = 1 And t[0] = 1
// @Modifies t, p
func CopyRead(p *P, t []int) {
	touch(p, t).list = append(t[:1:1], 5) // want `vego: the elements of t\[:1:1\] that append copies may be read before or after the call to touch`
}

// CopyAfterCall has a call among the operands of append, which orders the
// copy after touch.
//
// @Requires p != nil And |t| = 1 And t[0] = 1
// @Modifies t, p
// @Ensures |p.list'| = 2 And p.list'[0] = 9
func CopyAfterCall(p *P, t []int) {
	touch(p, t).list = append(t[:1:1], five())
}

// @Ensures result = x
func key(x int) (result int) {
	return x
}

// @Ensures (b -> result = 1) And (~b -> result = 0)
func b2i(b bool) (result int) {
	if b {
		return 1
	}
	return 0
}

type Q struct {
	i int
}

// @Requires q != nil
// @Ensures result = q.i
func get(q *Q) (result int) {
	return q.i
}

// InPlaceIndex reads t[0] for the index of the target, and the append may
// write t[0]. Go does not order the two.
//
// @Requires |u| = 6 And |t| = 1 And t[0] = 0
// @Modifies u, t
func InPlaceIndex(u [][]int, t []int) {
	u[t[0]] = append(t[:0], 5) // want `vego: t\[0\] may be read before or after the write of append into the array of t\[:0\], which may change it`
}

// PureIndex calls key in the target. key changes nothing and reads no
// memory, so it does the same before or after the append.
//
// @Requires |u| = 2 And |t| = 1 And 0 <= k < 2
// @Modifies u, t
// @Ensures |u'[k]| = 2
func PureIndex(u [][]int, t []int, k int) {
	u[key(k)] = append(t[:1], 5)
}

// KeyOfElement reads t[0] for key, which Go may call after the append wrote
// t[0].
//
// @Requires |u| = 6 And |t| = 1 And t[0] = 0
// @Modifies u, t
func KeyOfElement(u [][]int, t []int) {
	u[key(t[0])] = append(t[:0], 5) // want `vego: t\[0\] may be read before or after the write of append into the array of t\[:0\]`
}

// ImpureIndex calls get in the target, which reads memory, so it cannot be
// moved across the write of the append.
//
// @Requires |u| = 2 And |t| = 1 And q != nil And 0 <= q.i < 2
// @Modifies u, t
func ImpureIndex(u [][]int, t []int, q *Q) {
	u[get(q)] = append(t[:0], 5) // want `vego: cannot verify ImpureIndex: get is called in the target of this assignment, and Go may call it before or after append writes into the array of t\[:0\]; assign the result of get to a variable in a statement of its own first`
}

// OrderedIndex has a call among the operands of append, which orders the
// append after get.
//
// @Requires |u| = 2 And |t| = 1 And q != nil And 0 <= q.i < 2
// @Modifies u, t
// @Ensures u'[q.i][0] = 5
func OrderedIndex(u [][]int, t []int, q *Q) {
	u[get(q)] = append(t[:0], five())
}

// LogicalIndex has && in the target, which orders nothing with the append.
//
// @Requires |u| = 2 And |t| = 1
// @Modifies u, t
// @Ensures True
func LogicalIndex(u [][]int, t []int, x, y bool) {
	u[b2i(x && y)] = append(t[:0], 5)
}

// LogicalRead reads t[0] on the right of && in the target.
//
// @Requires |u| = 2 And |t| = 1
// @Modifies u, t
func LogicalRead(u [][]int, t []int, x bool) {
	u[b2i(x && t[0] == 0)] = append(t[:0], 5) // want `vego: t\[0\] may be read before or after the write of append into the array of t\[:0\]`
}

// DistinctKeys builds a map from two keys that differ.
//
// @Requires a != b
// @Ensures result[a] = 1 And result[b] = 2
func DistinctKeys(a, b int) (result map[int]int) {
	return map[int]int{a: 1, b: 2}
}

// ConstantKeys builds a map from constant keys, which Go requires to differ,
// and one more.
//
// @Requires k > 2
// @Ensures result[1] = 10 And result[2] = 20 And result[k] = 0
func ConstantKeys(k int) (result map[int]int) {
	return map[int]int{1: 10, 2: 20, k: 0}
}

// RepeatedKey builds a map from two keys that may be the same. Go does not
// fix which of the two entries the map then keeps.
//
// @Ensures True
func RepeatedKey(a, b int) (result map[int]int) {
	return map[int]int{a: 1, b: 2} // want `vego: the keys a and b of this map literal may be equal, and Go does not fix which of their entries the map keeps; build the map with assignments instead`
}

// RepeatedName builds a map from a constant key and one that may equal it.
//
// @Ensures True
func RepeatedName(s string) (result map[string]int) {
	return map[string]int{"x": 1, s: 2} // want `vego: the keys "x" and s of this map literal may be equal`
}
