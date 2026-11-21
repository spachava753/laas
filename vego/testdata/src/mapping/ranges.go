package mapping

// The programs of a range over a map as a walk of one order of its keys,
// with the keys a loop has visited named by a Visited annotation.

// Keys fills a slice of len(s) elements, one for each key.
//
// @Ensures |result| = |s|
func Keys(s map[string]bool) (result []string) {
	nodes := make([]string, len(s))
	var i int
	// @Visited done
	// @Invariant i = |done|
	for node := range s {
		nodes[i] = node
		i++
	}
	return nodes
}

// KeysPastEnd writes one element further on.
//
// @Ensures True
func KeysPastEnd(s map[string]bool) (result []string) {
	nodes := make([]string, len(s))
	var i int
	// @Visited done
	// @Invariant i = |done|
	for node := range s {
		nodes[i+1] = node // want `vego: index may be out of range`
		i++
	}
	return nodes
}

type task struct {
	id   int
	text string
	tags []string
}

// AllTasks appends one value for each key into a slice made with room for
// all of them, so no append moves it.
//
// @Ensures |all| = |tasks|
func AllTasks(tasks map[int]task) (all []task) {
	all = make([]task, 0, len(tasks))
	// @Visited done
	// @Invariant |all| = |done| And cap(all) = |tasks|
	for _, t := range tasks {
		all = append(all, t)
	}
	return all
}

// AllTasksUnbounded appends without room made first, so an append may
// move the slice, and nothing bounds how large it grows.
//
// @Ensures True
func AllTasksUnbounded(tasks map[int]task) (all []task) {
	// @Visited done
	// @Invariant |all| = |done|
	for _, t := range tasks {
		all = append(all, t) // want `vego: the slice that append grows may be more than can be allocated`
	}
	return all
}

// Sum adds up values that are each at most 100.
//
// @Requires Forall k in Z : 0 <= m[k] <= 100
// @Ensures 0 <= total <= 100 * |m|
func Sum(m map[int]int) (total int) {
	// @Visited done
	// @Invariant 0 <= total <= 100 * |done|
	for _, n := range m {
		total += n
	}
	return total
}

// SumTooTight claims a bound one less for each key.
//
// @Requires Forall k in Z : 0 <= m[k] <= 100
// @Ensures total <= 99 * |m|
func SumTooTight(m map[int]int) (total int) {
	// @Visited done
	// @Invariant 0 <= total <= 100 * |done|
	for _, n := range m {
		total += n
	}
	return total // want `vego: postcondition may not hold: total <= 99 \* \|m\|`
}

// CopyKeys copies the keys into a map of another type. It needs the keys
// of different iterations to differ: each one is new to c.
//
// @Ensures |c| = |m| And (Forall k in Z : has(c, k) <-> has(m, k))
func CopyKeys(m map[int]bool) (c map[int]int) {
	c = make(map[int]int)
	// @Visited done
	// @Invariant |c| = |done| And (Forall k in Z : has(c, k) <-> has(done, k))
	for k := range m {
		c[k] = 1
	}
	return c
}

// CopyKeysCountedTwice claims a count the copy cannot have.
//
// @Ensures |c| = |m| + 1
func CopyKeysCountedTwice(m map[int]bool) (c map[int]int) {
	c = make(map[int]int)
	// @Visited done
	// @Invariant |c| = |done| And (Forall k in Z : has(c, k) <-> has(done, k))
	for k := range m {
		c[k] = 1
	}
	return c // want `vego: postcondition may not hold: \|c\| = \|m\| \+ 1`
}

// Pairs counts the pairs of keys with two loops over one map.
//
// @Requires |m| <= 1000
// @Ensures n = |m| * |m|
func Pairs(m map[int]bool) (n int) {
	// @Visited outer
	// @Invariant n = |outer| * |m|
	for range m {
		// @Visited inner
		// @Invariant n = |outer| * |m| + |inner|
		for range m {
			n++
		}
	}
	return n
}

// NonEmpty claims that every map has a key. The map may be empty, and then
// the loop runs no iteration, of which nothing is known.
//
// @Ensures r
func NonEmpty(m map[int]int) (r bool) {
	// @Invariant |m| >= 1
	for range m { // want `vego: loop invariant may not hold on entry: \|m\| >= 1`
	}
	return len(m) >= 1
}

// LastIteration counts the iterations of a map with one key, and claims
// none. After the last iteration there is no key, and nothing about one is
// known.
//
// @Requires |m| = 1
// @Ensures r = 0
func LastIteration(m map[int]int) (r int) {
	n := 0
	// @Invariant n = 0
	for range m { // want `vego: loop invariant may not be preserved: n = 0`
		n++
	}
	return n
}

// LastIterationVisited is LastIteration with the order of the walk in the
// problem.
//
// @Requires |m| = 1
// @Ensures r = 0
func LastIterationVisited(m map[int]int) (r int) {
	n := 0
	// @Visited done
	// @Invariant n = 0 And (Forall k in Z : has(done, k) -> has(m, k))
	for range m { // want `vego: loop invariant may not be preserved: n = 0`
		n++
	}
	return n
}

// MoreKeysThanCount asks for a map with one key that has two. No map is
// such a map, and the range says so: what follows it would be proved, since
// nothing holds after it.
//
// @Requires |m| = 1 And has(m, 1) And has(m, 2)
// @Ensures r = 7
func MoreKeysThanCount(m map[int]int) (r int) {
	// @Visited done
	// @Invariant Forall k in Z : has(done, k) -> has(m, k)
	for range m { // want `vego: what is known here says that m has a number of keys other than \|m\|, which no map can; check the clauses that say which keys it has`
	}
	return 3
}

// ForcedKeys asks for the same through a quantifier, which no read of a key
// shows.
//
// @Requires |m| = 1 And (Forall k in [0, 5) : has(m, k))
// @Ensures r = 7
func ForcedKeys(m map[int]int) (r int) {
	for range m { // want `vego: what is known here says that m has a number of keys other than \|m\|, which no map can; check the clauses that say which keys it has`
	}
	return 3 // want `vego: postcondition may not hold: r = 7`
}

var table = map[string]int{"a": 1, "b": 2, "c": 3}

// Names ranges over a package-level map whose contents nothing changes.
//
// @Ensures |result| = |table|
func Names() (result []string) {
	result = make([]string, 0, len(table))
	// @Visited done
	// @Invariant |result| = |done| And cap(result) = |table|
	for name := range table {
		result = append(result, name)
	}
	return result
}

type wide struct{ a, b, c int }

// Widen makes a slice of len(m) values of 24 bytes from a map whose entries
// take 16. The memory the map takes bounds len(m) only by 16 bytes a key.
//
// @Ensures True
func Widen(m map[int]int) (result []wide) {
	return make([]wide, len(m)) // want `vego: the slice made may be more than can be allocated`
}

// Narrow makes a slice of len(m) values of 8 bytes from the same map.
//
// @Ensures |result| = |m|
func Narrow(m map[int]int) (result []int) {
	return make([]int, len(m))
}

func twoKeys() map[int]int { return map[int]int{1: 1, 2: 2} }

// AfterTrusted ranges over what a trusted function returns whose entry no
// map can meet.
//
// @Ensures True
func AfterTrusted() {
	m := twoKeys()
	for range m { // want `vego: what is known here says that m has a number of keys other than \|m\|, which no map can; check the clauses that say which keys it has`
	}
}

// keyed is an interface whose method promises a map no map can be. Such a
// contract is refused where it is declared, since no result is shown to
// meet it, so a call cannot use it.
type keyed interface {
	// @Ensures |result| = 1 And has(result, 1) And has(result, 2)
	Keys() (result map[int]int) // want `vego: the Ensures clauses of keyed.Keys are not proved to be satisfiable`
}

// AfterMethod ranges over what such a method returns.
//
// @Requires k != nil
// @Ensures True
func AfterMethod(k keyed) {
	m := k.Keys() // want `vego: the contract of keyed.Keys cannot be used: it was refused where it is declared`
	for range m {
	}
}

// NotYetVisited asserts that the key of an iteration is not among those
// visited before it, and that every earlier key is.
//
// @Ensures True
func NotYetVisited(m map[int]bool) {
	c := map[int]int{}
	// @Visited done
	// @Invariant Forall k in Z : has(c, k) <-> has(done, k)
	for k := range m {
		// @Assert ~has(done, k) And ~has(c, k)
		c[k] = 1
	}
}

// AlreadyVisited asserts that the key of an iteration is among those
// visited before it.
//
// @Ensures True
func AlreadyVisited(m map[int]bool) {
	// @Visited done
	// @Invariant |done| >= 0
	for k := range m {
		_ = k
		// @Assert has(done, k) // want `vego: assertion may not hold: has\(done, k\)`
	}
}

// LastIterationAsked is LastIteration with the key of each iteration asked
// of the visited set, which puts what the order says of that key in the
// problem.
//
// @Requires |m| = 1
// @Ensures r = 0
func LastIterationAsked(m map[int]int) (r int) {
	n := 0
	// @Visited done
	// @Invariant n = 0
	for k := range m { // want `vego: loop invariant may not be preserved: n = 0`
		_ = k
		// @Assert ~has(done, k)
		n++
	}
	return n
}

// NonEmptyValues is NonEmpty with the value of each key read, which puts in
// the problem that a key the map has makes its count positive.
//
// @Ensures True
func NonEmptyValues(m map[int]int) {
	// @Invariant |m| >= 1
	for _, v := range m { // want `vego: loop invariant may not hold on entry: \|m\| >= 1`
		_ = v
	}
}

// SameFirst claims that two walks of one map that nothing changes start at
// the same key. Go fixes no order, also not between two walks of one map:
// each walk has an order of its own.
//
// @Requires |m| = 2
// @Ensures r
func SameFirst(m map[int]int) (r bool) {
	first, second := 0, 0
	// @Visited one
	// @Invariant |one| = 0
	for k := range m {
		first = k
		break
	}
	// @Visited two
	// @Invariant |two| = 0
	for k := range m {
		second = k
		break
	}
	return first == second // want `vego: postcondition may not hold: r`
}
