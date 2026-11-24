// Package initcalls reads fixed variables whose initialisers call
// functions, and runs every initialiser as code (step 5 of F32).
package initcalls

// buildTable makes a table of three.
//
// @Ensures |t| = 3
func buildTable() (t []int) {
	return []int{1, 2, 3}
}

var table = buildTable()

// third reads the last element, whose index the Ensures of buildTable
// bounds.
//
// @Ensures True
func third() (r int) {
	return table[2]
}

// fourth reads past it.
//
// @Ensures True
func fourth() (r int) {
	return table[3] // want `vego: index may be out of range`
}

// five returns five.
//
// @Ensures r = 5
func five() (r int) { return 5 }

var six = five() + 1

// readSix knows the value of six.
//
// @Ensures r = 6
func readSix() (r int) {
	return six
}

// Config holds a number.
type Config struct{ n int }

var cfg = Config{n: five()}

// readCfg knows the field.
//
// @Ensures r = 5
func readCfg() (r int) {
	return cfg.n
}

// double doubles a small number.
//
// @Requires 0 <= k And k <= 1000
// @Ensures r = 2 * k
func double(k int) (r int) { return 2 * k }

// doubled is declared before what it reads, which Go initialises first.
var doubled = double(later)

var later = 3

// readDoubled knows it.
//
// @Ensures r = 6
func readDoubled() (r int) {
	return doubled
}

var tooMuch = double(5000) // want `vego: precondition of double may not hold in an initialiser, where a verified function relies on it for what it writes: k <= 1000`

// readTooMuch knows nothing of a variable whose initialiser does not
// verify.
//
// @Ensures r = 10000
func readTooMuch() (r int) {
	return tooMuch // want `vego: postcondition may not hold: r = 10000`
}

var short = []int{1}

var past = short[0] + pick(short) // want `vego: precondition of pick may not hold in an initialiser, where a verified function relies on it for what it writes: \|s\| >= 2`

// pick reads the second element.
//
// @Requires |s| >= 2
// @Ensures r = s[1]
func pick(s []int) (r int) { return s[1] }

// @Invariant n >= 0
var n int

// set sets n.
//
// @Requires k >= 0
// @Modifies n
// @Ensures True
func set(k int) (r int) {
	n = k
	return 0
}

var _ = set(-1) // want `vego: precondition of set may not hold in an initialiser, where a verified function relies on it for what it writes: k >= 0`

var setOne = set(1)

// Get reads n.
//
// @Ensures r >= 0
func Get() (r int) {
	return n
}

// Box holds a number.
type Box struct{ n int }

// newBox makes a box.
//
// @Ensures b != nil And fresh(b)
func newBox() (b *Box) { return &Box{} }

var box = newBox()

// poke writes the box without listing it: the box is not new memory of
// poke's, though newBox made it fresh where the initialiser ran.
//
// @Ensures True
func poke() {
	box.n = 1 // want `vego: box\.n is assigned, which poke may not modify; it is memory that the package-level variable box refers to; list box in a // @Modifies clause`
}

// pokeListed lists it, and knows box is not nil from the Ensures of newBox.
//
// @Modifies box
// @Ensures True
func pokeListed() {
	box.n = 1
}
