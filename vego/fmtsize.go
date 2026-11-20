package vego

import (
	"go/types"
	"slices"
	"strings"
	"unicode/utf8"

	"github.com/spachava753/laas/vego/internal/logic"
)

// What fmt builds must be something the runtime can allocate. fmt grows a
// buffer with append and panics, as append does, when the capacity the
// runtime picks for it is more than can be allocated. So at each call of a
// function that formats, vego proves a bound on the bytes fmt writes, from
// the format and from the lengths of the strings and slices it formats.
//
// The bound counts what the logic has terms for. What it has none for is
// left to an assumption in the guide: the text of an error, what a String or
// Error method returns, the elements of slices held in a slice or a struct
// that is itself an element of a slice (a []string, a [][]int), and the
// prefix and header a logger adds. What the bound counts of these is only
// what lies around them: brackets, separators, widths, and type names.

// fmtMaxWidth is the largest width or precision fmt uses: it reads digits
// while the number so far is at most a million, so one more digit after a
// million is read too.
const fmtMaxWidth = 10_000_009

// fmtSpec is what the bound needs to know of a format.
type fmtSpec struct {
	// verbs is how many verbs the format has, at most, and length the
	// bytes it has; for a format that is not a constant, both are its
	// length.
	verbs, length *logic.Term
	// width and precision are the largest that any verb uses.
	width, precision int64
	// expands is set when a verb may write a string or a byte slice at more
	// than one byte for each of its bytes: q, x, X, or # with v.
	expands bool
	// line is set for the functions without a format, which print each
	// operand once with %v, with a separator between and a newline. A
	// format that is not a constant has as many verbs as bytes, each with
	// the largest width and precision, any of which may be q or x.
	line bool
}

// fmtPointerCost is what a pointer to a struct takes beyond the struct.
const fmtPointerCost = 8

// fmtVerbCost bounds what a verb writes apart from its operand: a wrapper
// such as %!d(MISSING), %!(BADWIDTH), or %!(NOVERB), and the separator
// and parenthesis of %!(EXTRA ...).
const fmtVerbCost = 32

// constantSpec reads a format that is a constant. Every '%' starts a verb;
// counting a %% or a verb that fmt refuses as a verb only makes the bound
// larger. Width and precision are the numbers written after a '%', or the
// largest fmt uses where one is given by an operand with '*'.
func constantSpec(format string) fmtSpec {
	spec := fmtSpec{length: logic.IntLit(int64(len(format)))}
	verbs := int64(0)
	for i := 0; i < len(format); i++ {
		if format[i] != '%' {
			continue
		}
		verbs++
		sharp, inPrecision, inIndex := false, false, false
		number := int64(0)
		end := func() {
			if inPrecision {
				spec.precision = max(spec.precision, number)
			} else {
				spec.width = max(spec.width, number)
			}
			number = 0
		}
		j := i + 1
	reading:
		for ; j < len(format); j++ {
			c := format[j]
			switch {
			case c == '#':
				sharp = true
			case c == '0' && number == 0 && !inIndex && !inPrecision, c == '+', c == '-', c == ' ':
			case c >= '0' && c <= '9':
				if !inIndex {
					number = min(number*10+int64(c-'0'), fmtMaxWidth)
				}
			case c == '[':
				end()
				inIndex = true
			case c == ']':
				inIndex = false
			case c == '*':
				number = fmtMaxWidth
			case c == '.':
				end()
				inPrecision = true
			default:
				break reading
			}
		}
		end()
		if j < len(format) {
			verb, size := utf8.DecodeRuneInString(format[j:])
			if strings.ContainsRune("qxX", verb) || (sharp && verb == 'v') {
				spec.expands = true
			}
			j += size - 1
		}
		i = j
	}
	spec.verbs = logic.IntLit(verbs)
	return spec
}

// fmtOperand is a value that is formatted, with its type. For a pointer,
// val and t are what it points to and pointer is set. assumed is set for a
// value whose String or Error method fmt may call, whose result has no
// term. name spells the value, for messages, and param says that it is a
// parameter or a field of one, which a Requires clause can name.
type fmtOperand struct {
	val     value
	t       types.Type
	pointer bool
	assumed bool
	name    string
	param   bool
}

// fmtLen is a length the bound counts: of a string or a slice, how many
// bytes each of its units may take, and how it is spelled.
type fmtLen struct {
	length *logic.Term
	coef   int64
	name   string
	param  bool
}

// fmtLinear is a constant and lengths, each with its coefficient.
type fmtLinear struct {
	c    int64
	lens []fmtLen
}

// plus adds two linear forms.
func (l fmtLinear) plus(o fmtLinear) fmtLinear {
	return fmtLinear{c: l.c + o.c, lens: append(slices.Clip(l.lens), o.lens...)}
}

// term is the linear form as a term.
func (l fmtLinear) term() *logic.Term {
	terms := []*logic.Term{logic.IntLit(l.c)}
	for _, n := range l.lens {
		terms = append(terms, logic.Mul(n.length, logic.IntLit(n.coef)))
	}
	return sumOf(terms)
}

// fmtSize is a bound on what fmt writes: fixed, plus the format's own bytes
// and, for each of its verbs, its width, precision, and wrapper, plus each
// operand under the widest verb once for each use, verbs + 1 times, or once
// without a format. complete says that nothing of it is assumed.
type fmtSize struct {
	spec     fmtSpec
	each     fmtLinear
	complete bool
	count    int64
}

// fmtBound returns the bound on the bytes that fmt writes when it formats
// the operands under the spec, apart from the parts the logic has no terms
// for.
//
// Each verb formats one operand, or none, so with V verbs no operand is
// formatted more than V times, and once more after the last verb as an
// extra operand. The bound is the format's own bytes, plus for each verb
// its width, its precision, and what wraps it, plus V + 1 times what each
// operand takes under the widest verb the format has. Without a format,
// each operand is formatted once with %v.
func fmtBound(spec fmtSpec, operands []fmtOperand) fmtSize {
	size := fmtSize{spec: spec, complete: true, count: int64(len(operands))}
	for _, op := range operands {
		weight, whole := fmtWeight(op.val, op.t, spec, true, op.name)
		for i := range weight.lens {
			weight.lens[i].param = op.param
		}
		if op.pointer {
			// A pointer is printed as & and what it points to, or as
			// <nil>, which takes less.
			weight.c += fmtPointerCost
		}
		size.each = size.each.plus(weight)
		size.complete = size.complete && whole && !op.assumed
	}
	return size
}

// term is the bound as a term.
func (z fmtSize) term() *logic.Term {
	if z.spec.line {
		// A separator or a newline after each operand.
		return logic.Add(logic.IntLit(fmtVerbCost+z.count), z.each.term())
	}
	perVerb := logic.IntLit(z.spec.width + z.spec.precision + fmtVerbCost)
	uses := logic.Add(z.spec.verbs, logic.IntLit(1))
	return sumOf([]*logic.Term{logic.IntLit(fmtVerbCost), z.spec.length, logic.Mul(z.spec.verbs, perVerb), logic.Mul(uses, z.each.term())})
}

// fmtFormatHint is the length of a format that is not a constant that a
// message suggests bounding it by.
const fmtFormatHint = 100

// suggest returns a bound N such that the bound is at most room when every
// length it counts is at most N, and a format that is not a constant at
// most fmtFormatHint; or 0 when there is none.
func (z fmtSize) suggest(room int64) int64 {
	verbs, length, uses := int64(0), int64(0), int64(1)
	if !z.spec.line {
		if known := z.spec.verbs.Value(); z.spec.verbs.Op == logic.OpIntLit && known.IsInt64() {
			verbs = known.Int64()
			length = z.spec.length.Value().Int64()
		} else {
			verbs, length = fmtFormatHint, fmtFormatHint
		}
		uses = verbs + 1
	}
	coefs := int64(0)
	for _, n := range z.each.lens {
		coefs += n.coef
	}
	avail := room - fmtVerbCost - z.count - length - verbs*(z.spec.width+z.spec.precision+fmtVerbCost) - uses*z.each.c
	if coefs == 0 || avail <= 0 {
		return 0
	}
	return avail / (uses * coefs)
}

// fmtTypeName bounds how many bytes fmt writes for the name of a type, which
// %T, %#v, and the wrappers of bad verbs and extra operands print: the
// spelling go/types gives it with the names of packages, twice over, which
// covers the spaces reflect adds and the quoting of tags.
func fmtTypeName(t types.Type) int64 {
	name := types.TypeString(t, func(p *types.Package) string { return p.Name() })
	return int64(2*len(name) + 16)
}

// fmtWeight bounds what fmt writes for one value of a type under the widest
// verb of the spec, and says whether it counts all of it. top is set for an
// operand itself, whose elements and fields have terms; below the elements
// of a slice, the lengths of what they hold have none and count as
// nothing. name spells the value.
func fmtWeight(val value, t types.Type, spec fmtSpec, top bool, name string) (fmtLinear, bool) {
	pad := spec.width + spec.precision + fmtTypeName(t)
	perByte := int64(1)
	if spec.expands && !spec.line {
		// % #x writes "0xNN " for each byte, %#v of a []byte "0xNN, ", and
		// %q at most \xNN or \u00NN for each byte it quotes.
		perByte = 6
	}
	switch u := t.Underlying().(type) {
	case *types.Basic:
		switch {
		case u.Info()&types.IsString != 0:
			if !top {
				return fmtLinear{c: pad + 2}, false
			}
			return fmtLinear{c: pad + 2, lens: []fmtLen{{length: logic.Len(val[0]), coef: perByte, name: name}}}, true
		case u.Info()&types.IsComplex != 0:
			// Each part takes the width and the precision, and %f of
			// MaxFloat64 is 317 bytes.
			return fmtLinear{c: 2*(spec.width+spec.precision+330) + fmtTypeName(t) + 4}, true
		case u.Info()&types.IsFloat != 0:
			return fmtLinear{c: pad + 330}, true
		}
		// %#b of MinInt64 is 67 bytes, and nil prints as <nil>.
		return fmtLinear{c: pad + 80}, true
	case *types.Slice:
		elem := u.Elem()
		if !top {
			return fmtLinear{c: pad + 4}, false
		}
		// Each element takes the width and the precision, as %5v of a
		// []int shows, and a separator. A byte slice written as a string
		// takes less for each byte than that, at most six with %#v. What an
		// element takes is a constant: below the top nothing has a term.
		weight, whole := fmtWeight(nil, elem, spec, false, "")
		return fmtLinear{c: pad + 4, lens: []fmtLen{{length: val[2], coef: weight.c + 2, name: name}}}, whole
	case *types.Struct:
		total := fmtLinear{c: pad + 4}
		complete := true
		for i := range u.NumFields() {
			field := u.Field(i)
			total.c += int64(len(field.Name()) + 2)
			lo, hi, _ := fieldLeaves(t, i)
			var leaves value
			if top {
				leaves = val[lo:hi]
			}
			weight, whole := fmtWeight(leaves, field.Type(), spec, top, name+"."+field.Name())
			total = total.plus(weight)
			complete = complete && whole
		}
		return total, complete
	}
	// An error, whose text has no term, and anything else that may be
	// formatted holds what is assumed; around it come the width, the
	// precision, and a name.
	return fmtLinear{c: pad + 64}, false
}

// sumOf adds up terms, of which there is at least one.
func sumOf(terms []*logic.Term) *logic.Term {
	total := terms[0]
	for _, t := range terms[1:] {
		total = logic.Add(total, t)
	}
	return total
}
