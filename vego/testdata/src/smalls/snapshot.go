package smalls

// A Snapshot names the value a formula has where it stands.

// Runs counts the runs of equal elements. The inner loop moves past where
// the iteration began, which start names, so the outer Variant decreases.
//
// @Requires |A| <= 1000
// @Ensures 0 <= runs <= |A|
func Runs(A []int) (runs int) {
	i := 0
	// @Invariant 0 <= i <= |A| And 0 <= runs <= i
	// @Variant |A| - i
	for i < len(A) {
		// @Snapshot start = i
		i++
		// @Invariant start < i <= |A| And 0 <= runs <= start
		// @Variant |A| - i
		for i < len(A) && A[i] == A[i-1] {
			i++
		}
		runs++
	}
	return runs
}

// RunsLate takes the snapshot after the step, where start < i does not
// hold.
//
// @Requires |A| <= 1000
// @Ensures 0 <= runs <= |A|
func RunsLate(A []int) (runs int) {
	i := 0
	// @Invariant 0 <= i <= |A| And 0 <= runs <= i
	// @Variant |A| - i
	for i < len(A) {
		i++
		// @Snapshot start = i
		// @Invariant start < i <= |A| And 0 <= runs < start
		// @Variant |A| - i
		for i < len(A) && A[i] == A[i-1] { // want `loop invariant may not hold on entry: start < i <= \|A\|`
			i++
		}
		runs++
	}
	return runs
}

// A snapshot holds a boolean, and a later one can name an earlier one.

// @Requires |A| <= 1000
// @Ensures True
func Flags(A []int, found bool) {
	// @Snapshot was = found
	// @Snapshot size = |A| + 1
	// @Snapshot both = (was And size > 0)
	found = !found
	// @Assert found <-> ~was
	// @Assert both <-> was
}

// @Requires x < 100
// @Ensures True
func Changed(x int) {
	// @Snapshot x0 = x
	x++
	// @Assert x = x0 // want `assertion may not hold: x = x0`
	_ = x
}

// A snapshot in a case clause lasts to the end of the clause.

// @Ensures r >= 0
func InCase(x int) (r int) {
	switch {
	case x > 0:
		// @Snapshot x0 = x
		x--
		// @Assert x < x0
		return x
	default:
		return 0
	}
}

// What is refused.

// @Ensures True
func Unused(x int) {
	// @Snapshot x0 = x // want `Snapshot x0: no annotation after it, in the block that holds it, names x0, so it says nothing; remove it, or move it to where it is used`
	_ = x
}

// @Ensures True
func NamesVariable(x, y int) {
	// @Snapshot y = x // want `Snapshot y: y already names a variable here; choose a name that names nothing, so that a formula reads it one way`
	// @Assert y = x
	_ = y
}

// @Ensures True
func NamesFunction(x int) {
	// @Snapshot max = x // want `Snapshot max: max already names a function here`
	// @Assert max = x
}

// @Ensures True
func NamesWord(x int) {
	// @Snapshot cap = x // want `Snapshot cap: cap is a word of the annotation language; choose another name`
	// @Assert x = x
}

// @Ensures True
func DeclaredAgain(x int) {
	// @Snapshot x0 = x // want `Snapshot x0: x0 is declared again at .*snapshot.go:\d+:\d+, inside the scope of the snapshot; choose another name`
	// @Assert x0 = x
	x0 := 1
	_ = x0
}

// @Ensures True
func SnapshotAgain(x int) {
	// @Snapshot x0 = x // want `Snapshot x0: x0 is declared again at`
	// @Snapshot x0 = x + 1
	// @Assert x0 = x
}

// @Requires |A| > 0
// @Ensures True
func Quantified(A []int) {
	// @Snapshot k = |A|
	// @Assert Forall k in [0, 1) : A[k] = A[k] // want `Assert annotation binds k, which is the name of the snapshot at .*; name the bound variable otherwise`
	// @Assert k > 0
}

// @Ensures True
func Primed(x int) {
	// @Snapshot x0 = x
	// @Assert old(x0) = x // want `in Assert annotation: x0 is a snapshot, which has one value; it cannot be primed or put in old\(\)`
}

// @Ensures True
func OfSlice(A []int) {
	// @Snapshot A0 = A // want `in Snapshot annotation: a snapshot holds an integer or a boolean, and A is a slice or a string`
	// @Assert |A0| = |A|
}

// @Ensures True
func Field(p *Node) {
	// @Snapshot q = p != nil
	// @Assert q.next = nil // want `in Assert annotation: q is a snapshot of an integer or a boolean, and has no fields or elements`
}

// @Ensures True
func InLiteral(x int) {
	// @Snapshot x0 = x
	func() {
		// @Assert x0 = x // want `Assert annotation names the snapshot x0, which was taken outside the function literal it stands in; take the snapshot inside the literal`
	}()
	// @Assert x0 = x
}

// @Requires x < 100
// @Ensures True
func InsideLiteral(x int) {
	func() {
		// @Snapshot x0 = x
		x++
		// @Assert x = x0 + 1
	}()
}

// @Requires |A| <= 1000
// @Ensures True
func BelowInvariant(A []int) {
	i := 0
	// @Invariant 0 <= i <= |A|
	// @Snapshot i0 = i // want `Snapshot i0 stands below an Invariant or Variant of the loop; put it above the annotations of the loop`
	// @Invariant i0 <= i
	// @Variant |A| - i
	for i < len(A) {
		i++
	}
}

// @Ensures True
func Malformed(x int) {
	// @Snapshot x0 // want `syntax error in Snapshot annotation: a Snapshot is written as name = value, as in // @Snapshot r0 = r`
	// @Snapshot(x0 = x) // want `syntax error in Snapshot annotation: expected a name, found "\("`
	// @Snapto x0 = x // want `unknown annotation "Snapto"`
	// @snapshot x0 = x // want `unknown annotation "snapshot"`
	//@Snapshot x0 = x // want `an annotation is written "// @Keyword ...", with one space before the @ and none after it`
	// note: @Snapshot x0 = x // want `an annotation is written "// @Keyword ...", with nothing but one space between // and @`
	/* @Snapshot x0 = x */ // want `annotations are only read from // comments, not from /\* \*/ comments`
	_ = x
}

// InDoc has a snapshot in its doc comment.
//
// @Snapshot x0 = x // want `Snapshot annotations belong inside a function body`
// @Ensures True
func InDoc(x int) {
}

// @Snapshot y0 = 1 // want `Snapshot annotation is not attached to anything; it stands inside a function body`
