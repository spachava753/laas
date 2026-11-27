package guide

// The programs of the section on recursive closures.

// Nodes is a set of nodes.
type Nodes map[string]bool

// Graph maps each node to its successors.
type Graph map[string]Nodes

// Reachable returns the nodes reachable from roots, by a depth-first
// search.
//
// @Ensures result != nil And fresh(result)
func (g Graph) Reachable(roots Nodes) (result Nodes) {
	seen := make(Nodes)
	var visit func(node string)
	// @Requires seen != nil And Forall k in g : g[k] != seen
	// @Requires Forall k in seen : seen[k]
	// @Modifies seen
	// @Variant |g \ seen|
	// @Ensures Forall k in seen : has(seen', k)
	// @Ensures Forall k in seen' : seen'[k]
	visit = func(node string) {
		if !seen[node] {
			seen[node] = true
			// @Invariant has(seen, node) And Forall k in old(seen) : has(seen, k)
			// @Invariant Forall k in seen : seen[k]
			for e := range g[node] {
				visit(e)
			}
		}
	}
	// @Invariant Forall k in seen : seen[k]
	for root := range roots {
		visit(root)
	}
	return seen
}

// CountedDown adds what a closure counts to a variable of the function.
//
// @Requires 0 <= n <= 1000
// @Ensures total = n
func CountedDown(n int) (total int) {
	var count func(k int)
	// @Requires 0 <= k And 0 <= total And total + k <= 1000
	// @Modifies total
	// @Variant k
	// @Ensures total' = total + k
	count = func(k int) {
		if k > 0 {
			total++
			count(k - 1)
		}
	}
	count(n)
	return total
}

// Untold assigns a variable that the contract of its closure does not
// list.
//
// @Ensures True
func Untold() {
	calls := 0
	var visit func(k int)
	// @Requires 0 <= k <= 3 And 0 <= calls And calls + k <= 10
	// @Variant k
	visit = func(k int) {
		if k > 0 {
			calls++ // want `vego: calls is assigned, which the closure visit may not modify; list it in a // @Modifies clause above visit = func\.\.\.`
			visit(k - 1)
		}
	}
	visit(3)
}

// Copied uses the variable of a closure as a value.
//
// @Ensures True
func Copied() {
	var visit func(k int)
	// @Ensures True
	visit = func(k int) {}
	other := visit // want `vego: cannot verify Copied: visit holds a recursive closure and is used here other than by calling it; a recursive closure may only be called, so it cannot be copied, passed, returned, stored, or compared; to use a function as a value, declare a named function type with a contract`
	other(1)
}
