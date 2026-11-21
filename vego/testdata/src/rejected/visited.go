package rejected

// Each use of a Visited annotation that is refused. A Visited annotation
// names the keys that a range over a map has visited, and stands directly
// above one.

// VisitedNoLoop has one above a statement that is no loop.
//
// @Ensures True
func VisitedNoLoop(m map[int]int) {
	x := 0
	// @Visited done // want `vego: Visited done: a Visited annotation names the keys that a range over a map has visited, and stands directly above one; the statement below it is no range`
	x++
	_ = x
}

// VisitedLast has one below the last statement.
//
// @Ensures True
func VisitedLast(m map[int]int) {
	_ = m
	// @Visited done // want `vego: Visited done: a Visited annotation names the keys that a range over a map has visited, and stands directly above one; there is no statement below it`
}

// VisitedSlice has one above a range over a slice.
//
// @Ensures True
func VisitedSlice(s []int) {
	// @Visited done // want `vego: Visited done: a Visited annotation names the keys that a range over a map has visited; this loop ranges over \[\]int, which has no keys to visit`
	// @Invariant |done| >= 0
	for range s {
	}
}

// VisitedFor has one above a for statement.
//
// @Ensures True
func VisitedFor(n int) {
	// @Visited done // want `vego: Visited done: a Visited annotation names the keys that a range over a map has visited; the loop below it is a for statement, which has no keys to visit`
	// @Invariant |done| >= 0
	// @Variant n - i
	for i := 0; i < n; i++ {
	}
}

// VisitedUnused has one that nothing names.
//
// @Ensures True
func VisitedUnused(m map[int]int) {
	// @Visited done // want `vego: Visited done: no annotation of the loop names done, so it says nothing; remove it, or name it in an Invariant`
	for range m {
	}
}

// VisitedTwice has two on one loop.
//
// @Ensures True
func VisitedTwice(m map[int]int) {
	// @Visited done
	// @Visited seen // want `vego: Visited seen: the loop already has the Visited annotation done; give it at most one`
	// @Invariant |done| = |seen|
	for range m {
	}
}

// VisitedTaken has one whose name is a parameter.
//
// @Ensures True
func VisitedTaken(m map[int]int, done int) {
	// @Visited done // want `vego: Visited done: done already names a variable here; choose a name that names nothing, so that a formula reads it one way`
	// @Invariant |done| >= 0
	for range m {
	}
}

// VisitedWord has one whose name is a word of the language.
//
// @Ensures True
func VisitedWord(m map[int]int) {
	// @Visited MaxInt // want `vego: Visited MaxInt: MaxInt is a word of the annotation language; choose another name`
	// @Invariant |MaxInt| >= 0
	for range m {
	}
}

// VisitedAgain declares the name again inside the loop.
//
// @Ensures True
func VisitedAgain(m map[int]int) {
	// @Visited done // want `vego: Visited done: done is declared again at .*, inside the loop of the Visited annotation; choose another name`
	// @Invariant |done| >= 0
	for range m {
		done := 1
		_ = done
	}
}

// VisitedIndexed reads a value of the set.
//
// @Ensures True
func VisitedIndexed(m map[int]int) {
	// @Visited done
	// @Invariant done[1] = 0 // want `vego: in Invariant annotation: done is the set of keys that the loop has visited; a formula reads it only as \|done\| and has\(done, k\)`
	for range m {
	}
}

// VisitedOld puts it in old().
//
// @Ensures True
func VisitedOld(m map[int]int) {
	// @Visited done
	// @Invariant |old(done)| >= 0 // want `vego: in Invariant annotation: done is the set of keys that the loop has visited, which has one value at each iteration; it cannot be primed or put in old\(\)`
	for range m {
	}
}

// VisitedBare compares the set as a whole.
//
// @Ensures True
func VisitedBare(m map[int]int) {
	// @Visited done
	// @Invariant done = done // want `vego: in Invariant annotation: done is the set of keys that the loop has visited; a formula reads it only as \|done\| and has\(done, k\)`
	for range m {
	}
}

// VisitedFresh asks fresh and cap of it.
//
// @Ensures True
func VisitedFresh(m map[int]int) {
	// @Visited done
	// @Invariant fresh(done) // want `vego: in Invariant annotation: done is the set of keys that the loop has visited; a formula reads it only as \|done\| and has\(done, k\)`
	for range m {
	}
}

// VisitedCap asks its capacity.
//
// @Ensures True
func VisitedCap(m map[int]int) {
	// @Visited done
	// @Invariant cap(done) = 0 // want `vego: in Invariant annotation: done is the set of keys that the loop has visited; a formula reads it only as \|done\| and has\(done, k\)`
	for range m {
	}
}

// VisitedPredicate passes it to a predicate.
//
// @Predicate small(n) ::= n < 10
// @Ensures True
func VisitedPredicate(m map[int]int) {
	// @Visited done
	// @Invariant small(done) // want `vego: in Invariant annotation: done is the set of keys that the loop has visited; a formula reads it only as \|done\| and has\(done, k\)`
	for range m {
	}
}

// VisitedBound binds the name in a quantifier.
//
// @Ensures True
func VisitedBound(m map[int]int) {
	// @Visited done
	// @Invariant Forall done in Z : done = done // want `vego: Invariant annotation binds done, which is the name of the Visited annotation at .*; name the bound variable otherwise`
	for range m {
	}
}

// VisitedAbove names it in an Assert above the loop, where it has no
// value.
//
// @Ensures True
func VisitedAbove(m map[int]int) {
	// @Assert |done| >= 0 // want `vego: Assert annotation names done, the keys that the loop below has visited, which have no value above the loop; name it in the loop's Invariant or inside the loop`
	// @Visited done
	// @Invariant |done| >= 0
	for range m {
	}
}

// VisitedInLiteral names it inside a function literal of the loop.
//
// @Ensures True
func VisitedInLiteral(m map[int]int) {
	// @Visited done
	// @Invariant |done| >= 0
	for range m {
		f := func() {
			// @Assert |done| >= 0 // want `vego: Assert annotation names done, the keys that the loop at .* has visited, from inside a function literal; a literal can name only what it declares or the function's own variables`
		}
		f()
	}
}

// VisitedWrongKey asks it of a key of another type.
//
// @Ensures True
func VisitedWrongKey(m map[string]int) {
	// @Visited done
	// @Invariant ~has(done, 1) // want `vego: in Invariant annotation: has\(...\): the key has type int, which is not what the map the loop ranges over is indexed by`
	for range m {
	}
}

// VisitedSpellings writes the keyword in ways that are not read.
//
// @Ensures True
func VisitedSpellings(m map[int]int) {
	// @Visted done // want `vego: unknown annotation "Visted"`
	// @visited done // want `vego: unknown annotation "visited"`
	// @Visiteddone // want `vego: unknown annotation "Visiteddone"`
	// @Visited // want `vego: syntax error in Visited annotation: a Visited annotation is written as one name, as in // @Visited done`
	// @Visited done more // want `vego: syntax error in Visited annotation: unexpected "more"`
	for range m {
	}
}

// VisitedPrimed primes it.
//
// @Ensures True
func VisitedPrimed(m map[int]int) {
	// @Visited done
	// @Invariant |done'| >= 0 // want `vego: in Invariant annotation: done is the set of keys that the loop has visited, which has one value at each iteration; it cannot be primed or put in old\(\)`
	for range m {
	}
}
