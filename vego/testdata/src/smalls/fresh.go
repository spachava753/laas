package smalls

// fresh in a body says that memory was allocated since the function was
// entered.

// grow appends x.
//
// @Requires |s| < 1000000
// @Modifies s
// @Ensures |r| = |s| + 1
// @Ensures fresh(r) Or within(r, s)
func grow(s []int, x int) (r []int) {
	return append(s, x)
}

// @Requires |A| <= 1000
// @Ensures |out| = |A|
func CopyThrough(A []int) (out []int) {
	// @Invariant |out| = i And fresh(out)
	for i := range A {
		out = grow(out, A[i])
	}
	return out
}

// @Requires |A| <= 1000
// @Ensures |out| = |A|
func CopyThroughForgets(A []int) (out []int) {
	// @Invariant |out| = i
	for i := range A {
		out = grow(out, A[i]) // want `grow may modify out, which CopyThroughForgets may not modify; out is a result, and a // @Modifies clause names memory only by a path from a parameter: if what out refers to may be memory of the caller, list it by the parameter it comes from; if it is memory that CopyThroughForgets made, nothing here shows that, since a loop that assigns out forgets where its memory came from: say so with // @Invariant fresh\(out\) on the loop`
	}
	return out
}

// The advice cannot work when the memory is the caller's: here out starts
// as the caller's slice.

// @Requires |A| <= 1000
// @Ensures True
func GrowsCallers(A []int) (out []int) {
	out = A
	// @Invariant |out| = |A| + i
	for i := range A {
		out = grow(out, A[i]) // want `grow may modify out, which GrowsCallers may not modify; out is a result, and a // @Modifies clause names memory only by a path from a parameter: if what out refers to may be memory of the caller, list it by the parameter it comes from; if it is memory that GrowsCallers made, nothing here shows that, since a loop that assigns out forgets where its memory came from: say so with // @Invariant fresh\(out\) on the loop`
	}
	return out
}

// @Requires |A| <= 1000
// @Ensures True
func GrowsCallersFresh(A []int) (out []int) {
	out = A
	// @Invariant |out| = |A| + i And fresh(out)
	for i := range A { // want `loop invariant may not hold on entry: fresh\(out\)`
		out = grow(out, A[i])
	}
	return out
}

// Node is linked to its neighbours.
type Node struct {
	next, prev *Node
}

// NewRing links n new nodes into a ring. fresh(p) also says that p is not
// nil.
//
// @Requires n >= 1
// @Ensures result != nil And fresh(result)
func NewRing(n int) (result *Node) {
	r := new(Node)
	p := r
	// @Invariant fresh(p)
	// @Variant n - i
	for i := 1; i < n; i++ {
		p.next = &Node{prev: p}
		p = p.next
	}
	p.next = r
	r.prev = p
	return r
}

// @Requires n >= 1
// @Ensures result != nil
func NewRingForgets(n int) (result *Node) {
	r := new(Node)
	p := r
	// @Invariant p != nil
	// @Variant n - i
	for i := 1; i < n; i++ {
		p.next = &Node{prev: p} // want `p.next is assigned, which NewRingForgets may not modify; p is a local variable, and a // @Modifies clause names memory only by a path from a parameter: if what p refers to may be memory of the caller, list it by the parameter it comes from; if it is memory that NewRingForgets made, nothing here shows that, since a loop that assigns p forgets where its memory came from: say so with // @Invariant fresh\(p\) on the loop`
		p = p.next
	}
	p.next = r // want `p.next is assigned, which NewRingForgets may not modify; list it in a // @Modifies clause`
	r.prev = p
	return r
}

// buf is written through its methods, as path's lazybuf is.
type buf struct {
	b []byte
	w int
}

// @Requires b != nil And 0 <= b.w < |b.b|
// @Modifies b, b.b
// @Ensures b.w' = b.w + 1 And |b.b'| = |b.b| And within(b.b', b.b)
func (b *buf) put(c byte) {
	b.b[b.w] = c
	b.w++
}

// @Requires 0 < n <= 1000
// @Ensures True
func Fill(n int) {
	out := buf{b: make([]byte, n)}
	// @Invariant |out.b| = n And 0 <= i And out.w = i And fresh(out.b)
	// @Variant n - i
	for i := 0; i < n; i++ {
		out.put('x')
	}
}

// @Requires 0 < n <= 1000
// @Ensures True
func FillForgets(n int) {
	out := buf{b: make([]byte, n)}
	// @Invariant |out.b| = n And 0 <= i And out.w = i
	// @Variant n - i
	for i := 0; i < n; i++ {
		out.put('x') // want `put may modify what it calls b.b, which FillForgets may not modify`
	}
}

// fresh stands in an Assert too, and of a value that was passed in it is
// not proved.

// @Requires p != nil
// @Ensures True
func Passed(p *Node) {
	q := new(Node)
	// @Assert fresh(q) And q != p
	q = p
	_ = q
	// @Assert fresh(q) // want `assertion may not hold: fresh\(q\)`
}

// A nil interface value holds nothing, so it is fresh; a nil pointer is
// not.

// @Ensures fresh(r) And r = nil
func NoValue() (r any) {
	return nil
}

// @Ensures True
func NilFresh() {
	var x any
	var p *Node
	_, _ = x, p
	// @Assert fresh(x)
	// @Assert fresh(p) // want `assertion may not hold: fresh\(p\)`
}

// fresh cannot say anything where nothing was allocated yet.

// @Requires fresh(p) // want `in Requires annotation: fresh says what was allocated since a call began, and nothing has been allocated where this annotation is read; fresh is allowed in an Ensures, where it says what the call allocated, and in an Invariant or an Assert inside a body, where it says what the function allocated since it was entered`
// @Ensures True
func FreshRequired(p *Node) {
}

// Owner keeps a node.
//
// @Invariant fresh(n) // want `an invariant of a type describes one state, so it cannot say what was allocated since a call began; fresh is allowed in an Ensures`
type Owner struct {
	n *Node
}
