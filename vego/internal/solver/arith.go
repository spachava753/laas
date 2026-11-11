package solver

import (
	"math"
	"math/big"
	"sort"
	"strconv"
	"strings"
)

// overflow is panicked when the 64-bit fast path of the arithmetic would
// overflow. The check is then repeated with arbitrary precision.
type overflow struct{}

func addChecked(a, b int64) int64 {
	if (b > 0 && a > math.MaxInt64-b) || (b < 0 && a < math.MinInt64-b) {
		panic(overflow{})
	}
	return a + b
}

func mulChecked(a, b int64) int64 {
	if a == 0 || b == 0 {
		return 0
	}
	c := a * b
	if c/b != a || (a == -1 && b == math.MinInt64) || (b == -1 && a == math.MinInt64) {
		panic(overflow{})
	}
	return c
}

// negChecked returns -a. The smallest int64 has no negation.
func negChecked(a int64) int64 {
	if a == math.MinInt64 {
		panic(overflow{})
	}
	return -a
}

func abs(a int64) int64 {
	if a < 0 {
		return negChecked(a)
	}
	return a
}

// poly is a polynomial with integer coefficients over atoms. Each key of m is
// a monomial: the identifiers of its atoms in ascending order joined by "*".
// Coefficients have arbitrary precision. A poly and the numbers in it are
// immutable once built.
type poly struct {
	c *big.Int
	m map[string]*big.Int
}

var bigZero, bigOne = big.NewInt(0), big.NewInt(1)

func constPoly(c int64) poly { return poly{c: big.NewInt(c)} }

// monomialPoly returns the polynomial consisting of one monomial.
func monomialPoly(mono string) poly {
	return poly{c: bigZero, m: map[string]*big.Int{mono: bigOne}}
}

func (a poly) isConst() bool { return len(a.m) == 0 }

// quo divides a polynomial by a number, and reports whether that leaves
// every coefficient whole.
func (a poly) quo(by int64) (poly, bool) {
	divisor := big.NewInt(by)
	result := poly{c: new(big.Int), m: map[string]*big.Int{}}
	rem := new(big.Int)
	if result.c.QuoRem(a.c, divisor, rem); rem.Sign() != 0 {
		return poly{}, false
	}
	for mono, coef := range a.m {
		part := new(big.Int)
		if part.QuoRem(coef, divisor, rem); rem.Sign() != 0 {
			return poly{}, false
		}
		result.m[mono] = part
	}
	return result, true
}

// coef returns the coefficient of a monomial, zero when it does not occur.
func (a poly) coef(mono string) *big.Int {
	if c, ok := a.m[mono]; ok {
		return c
	}
	return bigZero
}

// add returns a + scale*b.
func (a poly) add(b poly, scale int64) poly { return a.addScaled(b, big.NewInt(scale)) }

func (a poly) addScaled(b poly, scale *big.Int) poly {
	result := poly{c: new(big.Int).Mul(scale, b.c), m: make(map[string]*big.Int, len(a.m)+len(b.m))}
	result.c.Add(result.c, a.c)
	for mono, coef := range a.m {
		result.m[mono] = coef
	}
	for mono, coef := range b.m {
		sum := new(big.Int).Mul(scale, coef)
		sum.Add(sum, result.coef(mono))
		if sum.Sign() == 0 {
			delete(result.m, mono)
			continue
		}
		result.m[mono] = sum
	}
	return result
}

// mul returns the product a*b, expanding products of sums into monomials.
func (a poly) mul(b poly) poly {
	result := poly{c: new(big.Int).Mul(a.c, b.c)}
	result = result.addScaled(poly{c: bigZero, m: a.m}, b.c).addScaled(poly{c: bigZero, m: b.m}, a.c)
	for monoA, coefA := range a.m {
		for monoB, coefB := range b.m {
			result = result.addScaled(monomialPoly(joinMonomials(monoA, monoB)), new(big.Int).Mul(coefA, coefB))
		}
	}
	return result
}

func monomialAtoms(mono string) []int {
	parts := strings.Split(mono, "*")
	ids := make([]int, len(parts))
	for i, part := range parts {
		ids[i], _ = strconv.Atoi(part)
	}
	return ids
}

func joinMonomials(a, b string) string {
	ids := append(monomialAtoms(a), monomialAtoms(b)...)
	sort.Ints(ids)
	parts := make([]string, len(ids))
	for i, id := range ids {
		parts[i] = strconv.Itoa(id)
	}
	return strings.Join(parts, "*")
}

func (a poly) monomials() []string {
	monos := make([]string, 0, len(a.m))
	for mono := range a.m {
		monos = append(monos, mono)
	}
	sort.Strings(monos)
	return monos
}

// key returns a canonical string, equal for equal polynomials.
func (a poly) key() string {
	var b strings.Builder
	b.WriteString(a.c.String())
	for _, mono := range a.monomials() {
		b.WriteByte(';')
		b.WriteString(mono)
		b.WriteByte(':')
		b.WriteString(a.m[mono].String())
	}
	return b.String()
}

// system is a set of arithmetic constraints: each eq = 0 and each le <= 0.
type system struct{ eqs, les []poly }

// partition is the arithmetic facts of a branch, split into systems that
// share no unknown. Constraints in different systems cannot contradict each
// other, so each system is decided on its own, which keeps the eliminations
// small however many unrelated facts a proof carries.
type partition struct {
	find    func(mono string) string
	systems map[string]*system
	order   []string
}

// parts returns the partition of the arithmetic facts of a branch. It is
// kept until a fact is added.
func (p *prover) parts(b *branch) *partition {
	if b.parts != nil {
		return b.parts
	}
	part := &partition{find: groups(b.eqs, b.les), systems: map[string]*system{}}
	for i, group := range [][]poly{b.eqs, b.les} {
		for _, pl := range group {
			root := ""
			for mono := range pl.m {
				root = part.find(mono)
				break
			}
			if part.systems[root] == nil {
				part.systems[root] = &system{}
				part.order = append(part.order, root)
			}
			if i == 0 {
				part.systems[root].eqs = append(part.systems[root].eqs, pl)
			} else {
				part.systems[root].les = append(part.systems[root].les, pl)
			}
		}
	}
	b.parts = part
	return part
}

// infeasible reports whether the arithmetic facts of a branch have no
// integer solution. The answer true is always correct; false means "not
// refuted".
func (p *prover) infeasible(b *branch) bool {
	p.step()
	part := p.parts(b)
	for _, root := range part.order {
		if p.eliminate(part.systems[root].eqs, part.systems[root].les) {
			return true
		}
	}
	return false
}

// contradicts reports whether one more constraint, pl = 0 or pl <= 0, has no
// integer solution together with the arithmetic facts of a branch. Only the
// facts connected to the constraint are consulted: the others were found
// feasible when the branch was last examined, and the constraint cannot
// change that.
func (p *prover) contradicts(b *branch, pl poly, equality bool) bool {
	p.step()
	part := p.parts(b)
	var eqs, les []poly
	joined := map[string]bool{}
	for mono := range pl.m {
		root := part.find(mono)
		if sys := part.systems[root]; sys != nil && !joined[root] {
			eqs, les = append(eqs, sys.eqs...), append(les, sys.les...)
		}
		joined[root] = true
	}
	if equality {
		eqs = append(eqs, pl)
	} else {
		les = append(les, pl)
	}
	return p.eliminate(eqs, les)
}

// step counts one arithmetic check against the budget of the proof.
func (p *prover) step() {
	p.steps++
	if p.steps > p.maxSteps {
		panic(giveUp{})
	}
}

// groups joins the unknowns that occur together in a constraint, directly
// or through other constraints, and returns the function that maps an
// unknown to the representative of its group.
func groups(eqs, les []poly) (find func(mono string) string) {
	parent := map[string]string{}
	find = func(mono string) string {
		up, ok := parent[mono]
		if !ok || up == mono {
			parent[mono] = mono
			return mono
		}
		root := find(up)
		parent[mono] = root
		return root
	}
	for _, group := range [][]poly{eqs, les} {
		for _, pl := range group {
			anchor := ""
			for mono := range pl.m {
				if anchor == "" {
					anchor = mono
				}
				parent[find(mono)] = find(anchor)
			}
		}
	}
	return find
}

// eliminate decides whether constraints have no integer solution. It
// eliminates equalities by substitution and inequalities by Fourier–Motzkin
// elimination, tightening every derived inequality to the integers. The
// elimination runs on 64-bit numbers when the constraints fit and nothing
// overflows, and is repeated with arbitrary precision otherwise.
func (p *prover) eliminate(eqs, les []poly) bool {
	columns := map[string]int{}
	for _, group := range [][]poly{eqs, les} {
		for _, pl := range group {
			for mono := range pl.m {
				if _, ok := columns[mono]; !ok {
					columns[mono] = len(columns)
				}
			}
		}
	}
	width := len(columns)
	dense := func(group []poly) [][]*big.Int {
		rows := make([][]*big.Int, len(group))
		for i, pl := range group {
			rows[i] = make([]*big.Int, width+1)
			for j := range rows[i] {
				rows[i][j] = bigZero
			}
			for mono, coef := range pl.m {
				rows[i][columns[mono]] = coef
			}
			rows[i][width] = pl.c
		}
		return rows
	}
	eqRows, leRows := dense(eqs), dense(les)
	if !p.bigOnly {
		if unsat, ok := infeasibleSmall(eqRows, leRows, width); ok {
			return unsat
		}
	}
	return infeasibleBig(eqRows, leRows, width)
}

// infeasibleSmall runs the elimination on 64-bit numbers. Its second result
// is false when a number did not fit, in which case the first is meaningless.
func infeasibleSmall(eqs, les [][]*big.Int, width int) (unsat, ok bool) {
	defer func() {
		if r := recover(); r != nil {
			if _, isOverflow := r.(overflow); !isOverflow {
				panic(r)
			}
			unsat, ok = false, false
		}
	}()
	narrow := func(rows [][]*big.Int) [][]int64 {
		small := make([][]int64, len(rows))
		for i, row := range rows {
			small[i] = make([]int64, len(row))
			for j, value := range row {
				if !value.IsInt64() {
					panic(overflow{})
				}
				small[i][j] = value.Int64()
			}
		}
		return small
	}
	eqRows, rows := narrow(eqs), narrow(les)
	for len(eqRows) > 0 {
		eq := eqRows[len(eqRows)-1]
		eqRows = eqRows[:len(eqRows)-1]
		g := rowGCD(eq)
		if g == 0 {
			if eq[width] != 0 {
				return true, true
			}
			continue
		}
		if eq[width]%g != 0 {
			return true, true
		}
		pivot := -1
		for j := range width {
			eq[j] /= g
			if eq[j] != 0 && (pivot < 0 || abs(eq[j]) < abs(eq[pivot])) {
				pivot = j
			}
		}
		eq[width] /= g
		for _, group := range [][][]int64{eqRows, rows} {
			for _, row := range group {
				substitute(row, eq, pivot)
			}
		}
	}
	return fourierMotzkin(rows, width), true
}

// rowGCD returns the greatest common divisor of the coefficients of a dense
// row, ignoring its trailing constant.
func rowGCD(row []int64) int64 {
	var g int64
	for _, coef := range row[:len(row)-1] {
		for coef = abs(coef); coef != 0; {
			g, coef = coef, g%coef
		}
	}
	return g
}

// substitute eliminates the pivot column from row using the equality eq. The
// row is scaled by a positive factor, so an inequality keeps its direction.
func substitute(row, eq []int64, pivot int) {
	coef := row[pivot]
	if coef == 0 {
		return
	}
	scaleRow, scaleEq := abs(eq[pivot]), coef
	if eq[pivot] < 0 {
		scaleEq = negChecked(coef)
	}
	for k := range row {
		row[k] = addChecked(mulChecked(scaleRow, row[k]), negChecked(mulChecked(scaleEq, eq[k])))
	}
}

const maxFMRows = 800

// fourierMotzkin decides rational infeasibility of rows (each meaning
// coefficients·x + constant <= 0) by eliminating one column at a time. Rows
// are divided by the gcd of their coefficients with the constant rounded up,
// which is the integer tightening that makes strict bounds usable.
func fourierMotzkin(rows [][]int64, width int) bool {
	var keyBuf []byte
	for {
		index := map[string]int{}
		kept := rows[:0]
		for _, row := range rows {
			g := rowGCD(row)
			if g == 0 {
				if row[width] > 0 {
					return true
				}
				continue
			}
			keyBuf = keyBuf[:0]
			for j := range width {
				row[j] /= g
				keyBuf = strconv.AppendInt(keyBuf, row[j], 10)
				keyBuf = append(keyBuf, ',')
			}
			// Round the constant up: for a negative constant Go's
			// truncating division already rounds toward zero, which is up.
			if c := row[width]; c >= 0 {
				row[width] = addChecked(c, g-1) / g
			} else {
				row[width] = c / g
			}
			if i, dup := index[string(keyBuf)]; dup {
				if row[width] > kept[i][width] {
					kept[i] = row
				}
				continue
			}
			index[string(keyBuf)] = len(kept)
			kept = append(kept, row)
		}
		rows = kept
		if len(rows) == 0 {
			return false
		}
		best := cheapestColumn(width, func(j int) (pos, neg int) {
			for _, row := range rows {
				if row[j] > 0 {
					pos++
				} else if row[j] < 0 {
					neg++
				}
			}
			return pos, neg
		})
		var next, lower, upper [][]int64
		for _, row := range rows {
			switch {
			case row[best] > 0:
				upper = append(upper, row)
			case row[best] < 0:
				lower = append(lower, row)
			default:
				next = append(next, row)
			}
		}
		if len(next)+len(upper)*len(lower) > maxFMRows {
			return false
		}
		for _, up := range upper {
			for _, low := range lower {
				combined := make([]int64, width+1)
				for k := range combined {
					combined[k] = addChecked(mulChecked(negChecked(low[best]), up[k]), mulChecked(up[best], low[k]))
				}
				next = append(next, combined)
			}
		}
		rows = next
	}
}

// cheapestColumn picks the column whose elimination creates the fewest rows.
// count reports how many rows have a positive and a negative coefficient in a
// column; at least one column must occur in some row.
func cheapestColumn(width int, count func(column int) (pos, neg int)) int {
	best, bestCost := -1, 0
	for j := range width {
		pos, neg := count(j)
		if cost := pos*neg - pos - neg; pos+neg > 0 && (best < 0 || cost < bestCost) {
			best, bestCost = j, cost
		}
	}
	return best
}

// maxBits bounds the size of the numbers the arbitrary-precision elimination
// will carry before it gives up.
const maxBits = 4096

// infeasibleBig is the arbitrary-precision twin of infeasibleSmall. It follows
// the same steps, so the two must be kept in line with each other.
func infeasibleBig(eqRows, rows [][]*big.Int, width int) bool {
	gcdOf := func(row []*big.Int) *big.Int {
		g := new(big.Int)
		for _, coef := range row[:width] {
			g.GCD(nil, nil, g, new(big.Int).Abs(coef))
		}
		return g
	}
	for len(eqRows) > 0 {
		eq := eqRows[len(eqRows)-1]
		eqRows = eqRows[:len(eqRows)-1]
		g := gcdOf(eq)
		if g.Sign() == 0 {
			if eq[width].Sign() != 0 {
				return true
			}
			continue
		}
		if new(big.Int).Rem(eq[width], g).Sign() != 0 {
			return true
		}
		pivot := -1
		reduced := make([]*big.Int, width+1)
		for j := range reduced {
			reduced[j] = new(big.Int).Quo(eq[j], g)
			if j < width && reduced[j].Sign() != 0 && (pivot < 0 || reduced[j].CmpAbs(reduced[pivot]) < 0) {
				pivot = j
			}
		}
		scaleRow := new(big.Int).Abs(reduced[pivot])
		for _, group := range [][][]*big.Int{eqRows, rows} {
			for i, row := range group {
				if row[pivot].Sign() == 0 {
					continue
				}
				scaleEq := new(big.Int).Set(row[pivot])
				if reduced[pivot].Sign() < 0 {
					scaleEq.Neg(scaleEq)
				}
				group[i] = combine(scaleRow, row, new(big.Int).Neg(scaleEq), reduced)
			}
		}
	}
	for {
		index := map[string]int{}
		kept := rows[:0]
		for _, row := range rows {
			g := gcdOf(row)
			if g.Sign() == 0 {
				if row[width].Sign() > 0 {
					return true
				}
				continue
			}
			tightened := make([]*big.Int, width+1)
			var key strings.Builder
			for j := range width {
				tightened[j] = new(big.Int).Quo(row[j], g)
				key.WriteString(tightened[j].String())
				key.WriteByte(',')
			}
			// Round the constant up; Quo truncates toward zero.
			constant := new(big.Int).Set(row[width])
			if constant.Sign() >= 0 {
				constant.Add(constant, g).Sub(constant, bigOne)
			}
			tightened[width] = constant.Quo(constant, g)
			if tightened[width].BitLen() > maxBits {
				return false
			}
			if i, dup := index[key.String()]; dup {
				if tightened[width].Cmp(kept[i][width]) > 0 {
					kept[i] = tightened
				}
				continue
			}
			index[key.String()] = len(kept)
			kept = append(kept, tightened)
		}
		rows = kept
		if len(rows) == 0 {
			return false
		}
		best := cheapestColumn(width, func(j int) (pos, neg int) {
			for _, row := range rows {
				if sign := row[j].Sign(); sign > 0 {
					pos++
				} else if sign < 0 {
					neg++
				}
			}
			return pos, neg
		})
		var next, lower, upper [][]*big.Int
		for _, row := range rows {
			switch row[best].Sign() {
			case 1:
				upper = append(upper, row)
			case -1:
				lower = append(lower, row)
			default:
				next = append(next, row)
			}
		}
		if len(next)+len(upper)*len(lower) > maxFMRows {
			return false
		}
		for _, up := range upper {
			for _, low := range lower {
				next = append(next, combine(new(big.Int).Neg(low[best]), up, up[best], low))
			}
		}
		rows = next
	}
}

// combine returns a*x + b*y for two rows.
func combine(a *big.Int, x []*big.Int, b *big.Int, y []*big.Int) []*big.Int {
	result := make([]*big.Int, len(x))
	scratch := new(big.Int)
	for k := range result {
		result[k] = new(big.Int).Mul(a, x[k])
		result[k].Add(result[k], scratch.Mul(b, y[k]))
	}
	return result
}
