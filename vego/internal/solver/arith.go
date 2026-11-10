package solver

import (
	"math"
	"sort"
	"strconv"
	"strings"
)

// overflow is panicked when exact 64-bit arithmetic would overflow. The prover
// treats it as "unknown", never as a proof.
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

// poly is a polynomial with integer coefficients over atoms. Each key of m is
// a monomial: the identifiers of its atoms in ascending order joined by "*".
// A poly is immutable once built.
type poly struct {
	c int64
	m map[string]int64
}

func constPoly(c int64) poly { return poly{c: c} }

func (a poly) isConst() bool { return len(a.m) == 0 }

// add returns a + scale*b.
func (a poly) add(b poly, scale int64) poly {
	result := poly{c: addChecked(a.c, mulChecked(scale, b.c)), m: make(map[string]int64, len(a.m)+len(b.m))}
	for mono, coef := range a.m {
		result.m[mono] = coef
	}
	for mono, coef := range b.m {
		sum := addChecked(result.m[mono], mulChecked(scale, coef))
		if sum == 0 {
			delete(result.m, mono)
			continue
		}
		result.m[mono] = sum
	}
	return result
}

// mul returns the product a*b, expanding products of sums into monomials.
func (a poly) mul(b poly) poly {
	result := constPoly(mulChecked(a.c, b.c))
	result = result.add(poly{m: a.m}, b.c).add(poly{m: b.m}, a.c)
	for monoA, coefA := range a.m {
		for monoB, coefB := range b.m {
			product := poly{m: map[string]int64{joinMonomials(monoA, monoB): mulChecked(coefA, coefB)}}
			result = result.add(product, 1)
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
	b.WriteString(strconv.FormatInt(a.c, 10))
	for _, mono := range a.monomials() {
		b.WriteByte(';')
		b.WriteString(mono)
		b.WriteByte(':')
		b.WriteString(strconv.FormatInt(a.m[mono], 10))
	}
	return b.String()
}

func gcd(a, b int64) int64 {
	if a < 0 {
		a = -a
	}
	if b < 0 {
		b = -b
	}
	for b != 0 {
		a, b = b, a%b
	}
	return a
}

// rowGCD returns the greatest common divisor of the coefficients of a dense
// row, ignoring its trailing constant.
func rowGCD(row []int64) int64 {
	var g int64
	for _, coef := range row[:len(row)-1] {
		g = gcd(g, coef)
	}
	return g
}

// infeasible reports whether the constraints eq = 0 and le <= 0 have no
// integer solution. It eliminates equalities by substitution and inequalities
// by Fourier–Motzkin elimination, tightening every derived inequality to the
// integers. The answer true is always correct; false means "not refuted".
func (p *prover) infeasible(eqs, les []poly) (unsat bool) {
	p.steps++
	if p.steps > p.maxSteps {
		panic(giveUp{})
	}
	defer func() {
		if r := recover(); r != nil {
			if _, ok := r.(overflow); !ok {
				panic(r)
			}
			unsat = false
		}
	}()
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
	dense := func(group []poly) [][]int64 {
		rows := make([][]int64, len(group))
		for i, pl := range group {
			rows[i] = make([]int64, width+1)
			for mono, coef := range pl.m {
				rows[i][columns[mono]] = coef
			}
			rows[i][width] = pl.c
		}
		return rows
	}
	eqRows, rows := dense(eqs), dense(les)
	for len(eqRows) > 0 {
		eq := eqRows[len(eqRows)-1]
		eqRows = eqRows[:len(eqRows)-1]
		g := rowGCD(eq)
		if g == 0 {
			if eq[width] != 0 {
				return true
			}
			continue
		}
		if eq[width]%g != 0 {
			return true
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
	return fourierMotzkin(rows, width)
}

func abs(a int64) int64 {
	if a < 0 {
		return -a
	}
	return a
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
		scaleEq = -coef
	}
	for k := range row {
		row[k] = addChecked(mulChecked(scaleRow, row[k]), -mulChecked(scaleEq, eq[k]))
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
			if c := row[width]; c >= 0 {
				row[width] = (c + g - 1) / g
			} else {
				row[width] = -(-c / g)
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
		best, bestCost := -1, 0
		for j := range width {
			pos, neg := 0, 0
			for _, row := range rows {
				if row[j] > 0 {
					pos++
				} else if row[j] < 0 {
					neg++
				}
			}
			if cost := pos*neg - pos - neg; pos+neg > 0 && (best < 0 || cost < bestCost) {
				best, bestCost = j, cost
			}
		}
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
					combined[k] = addChecked(mulChecked(-low[best], up[k]), mulChecked(up[best], low[k]))
				}
				next = append(next, combined)
			}
		}
		rows = next
	}
}
