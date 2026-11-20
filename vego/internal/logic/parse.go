package logic

import (
	"fmt"
	"math/big"
	"strconv"
	"strings"
	"unicode"
	"unicode/utf8"
)

// NodeKind identifies the syntactic form of a parsed annotation node.
type NodeKind int

// Syntactic forms of the annotation language.
const (
	NInt     NodeKind = iota
	NBool             // Val is 1 for True
	NIdent            // Name, Primed
	NCall             // Name(Kids...)
	NIndex            // Kids[0][Kids[1]]
	NRange            // Kids[0][Kids[1]:Kids[2]) or, when Closed, Kids[0][Kids[1]:Kids[2]]
	NLen              // |Kids[0]|
	NUnary            // Op is "-" or "~"
	NBinary           // Op is an arithmetic or logical connective
	NCompare          // Kids[0] Ops[0] Kids[1] Ops[1] Kids[2] ...
	NQuant            // Op is "Forall" or "Exists"; Kids is [body] or [lo, hi, body]
	NNil              // nil: the nil error or the nil pointer
	NField            // Kids[0].Name, possibly Primed
	NStr              // a string literal; Name holds its value
	NAddr             // &Kids[0]: the address of a struct reached through memory
)

// Walk calls visit for the node and everything below it.
func (n *Node) Walk(visit func(*Node)) {
	if n == nil {
		return
	}
	visit(n)
	for _, kid := range n.Kids {
		kid.Walk(visit)
	}
}

// Node is an untyped syntax tree node of an annotation clause. Start and End
// are byte offsets into the clause text.
type Node struct {
	Kind   NodeKind
	Op     string
	Ops    []string
	Name   string
	Primed bool
	Val    int64
	Big    *big.Int // NInt
	Vars   []string
	LoOpen bool
	HiOpen bool
	Closed bool
	Kids   []*Node
	Start  int
	End    int
}

// Conjuncts returns the top-level conjuncts of a parsed formula so that each
// can be checked and reported separately.
func (n *Node) Conjuncts() []*Node {
	if n.Kind == NBinary && n.Op == "And" {
		return append(n.Kids[0].Conjuncts(), n.Kids[1].Conjuncts()...)
	}
	return []*Node{n}
}

// String writes the node the way an annotation spells it, for diagnostics.
func (n *Node) String() string {
	kid := func(i int) string {
		if n.Kids[i].Kind == NBinary || n.Kids[i].Kind == NCompare || n.Kids[i].Kind == NQuant {
			return "(" + n.Kids[i].String() + ")"
		}
		return n.Kids[i].String()
	}
	prime := ""
	if n.Primed {
		prime = "'"
	}
	switch n.Kind {
	case NInt:
		if n.Name != "" {
			return n.Name
		}
		return n.Big.String()
	case NAddr:
		return "&" + kid(0)
	case NBool:
		return map[int64]string{0: "False", 1: "True"}[n.Val]
	case NIdent:
		return n.Name + prime
	case NField:
		return kid(0) + "." + n.Name + prime
	case NCall:
		args := make([]string, len(n.Kids))
		for i, arg := range n.Kids {
			args[i] = arg.String()
		}
		return n.Name + "(" + strings.Join(args, ", ") + ")"
	case NIndex:
		return kid(0) + "[" + n.Kids[1].String() + "]"
	case NRange:
		closing := ")"
		if n.Closed {
			closing = "]"
		}
		return kid(0) + "[" + n.Kids[1].String() + ":" + n.Kids[2].String() + closing
	case NLen:
		return "|" + n.Kids[0].String() + "|"
	case NUnary:
		return n.Op + kid(0)
	case NBinary:
		return kid(0) + " " + n.Op + " " + kid(1)
	case NCompare:
		text := kid(0)
		for i, op := range n.Ops {
			text += " " + op + " " + kid(i+1)
		}
		return text
	case NQuant:
		return n.Op + " " + strings.Join(n.Vars, ", ") + " : " + n.Kids[len(n.Kids)-1].String()
	case NNil:
		return "nil"
	}
	return strconv.Quote(n.Name)
}

// PredDecl is a parsed "name(params) ::= body" predicate definition.
type PredDecl struct {
	Name   string
	Params []string
	Body   *Node
}

type token struct {
	size int  // length of the token in the source
	kind byte // 'i' identifier, 'n' number, 'c' character, 's' string, 'o' operator, 'e' end of input
	text string
	pos  int
}

// SyntaxError describes a malformed annotation clause.
type SyntaxError struct {
	Offset int
	Msg    string
}

func (e *SyntaxError) Error() string { return e.Msg }

var operators = []string{
	"<->", "::=", "->", "<=", ">=", "!=", "==", "&&", "||",
	"=", "<", ">", "+", "-", "*", "/", "%", "~", "!", "(", ")", "[", "]", ",", ":", "|", "'", ".", "&",
}

// lex splits clause text into tokens. Identifiers follow Go's rules, numbers
// are decimal, and operators are matched longest first. A quote directly
// after an identifier is a prime, as in x'; any other quote starts a
// character literal, as in '/', which uses Go's syntax and stands for the
// number of its character.
func lex(src string) ([]token, error) {
	// gofmt rewrites two quotes in a row in a doc comment as a closing
	// quotation mark, and two backquotes as an opening one, so in a
	// formula, in a string as well as outside, one of them is taken for
	// what gofmt made of an annotation and is refused.
	if at := strings.IndexAny(src, "“”"); at >= 0 {
		return nil, &SyntaxError{at, "this formula has “ or ”, which gofmt makes of two backquotes or two quotes in a row in a doc comment; " +
			"write '\\x27' for a quote character, \\x27\\x27 for two quotes in a string, and \\u201c or \\u201d in a string for the mark itself"}
	}
	var toks []token
	for i := 0; i < len(src); {
		r, size := utf8.DecodeRuneInString(src[i:])
		switch {
		case r == '\'' && !(len(toks) > 0 && toks[len(toks)-1].kind == 'i' && toks[len(toks)-1].pos+toks[len(toks)-1].size == i):
			end := i + 1
			for end < len(src) && src[end] != '\'' {
				if src[end] == '\\' {
					end++
				}
				end++
			}
			value, ok := characterValue(src[i:min(end+1, len(src))])
			if !ok {
				return nil, &SyntaxError{i, "malformed character literal; a prime follows a name directly, as in x', and a character is written as in Go, as in '/' or '\\n'"}
			}
			toks = append(toks, token{end + 1 - i, 'c', strconv.Itoa(int(value)), i})
			i = end + 1
		case unicode.IsSpace(r):
			i += size
		case unicode.IsLetter(r) || r == '_':
			start := i
			for i < len(src) {
				r, size = utf8.DecodeRuneInString(src[i:])
				if !unicode.IsLetter(r) && !unicode.IsDigit(r) && r != '_' {
					break
				}
				i += size
			}
			toks = append(toks, token{i - start, 'i', src[start:i], start})
		case r == '"':
			// A string literal uses Go's syntax for interpreted strings.
			end := i + 1
			for end < len(src) && src[end] != '"' {
				if src[end] == '\\' {
					end++
				}
				end++
			}
			text, err := strconv.Unquote(src[i:min(end+1, len(src))])
			if err != nil {
				return nil, &SyntaxError{i, "malformed string literal"}
			}
			toks = append(toks, token{end + 1 - i, 's', text, i})
			i = end + 1
		case r >= '0' && r <= '9':
			start := i
			for i < len(src) && src[i] >= '0' && src[i] <= '9' {
				i++
			}
			toks = append(toks, token{i - start, 'n', src[start:i], start})
		default:
			matched := false
			for _, op := range operators {
				if strings.HasPrefix(src[i:], op) {
					toks = append(toks, token{len(op), 'o', op, i})
					i += len(op)
					matched = true
					break
				}
			}
			if !matched {
				return nil, &SyntaxError{i, fmt.Sprintf("unexpected character %q", r)}
			}
		}
	}
	return append(toks, token{0, 'e', "", len(src)}), nil
}

// characterValue reads a character literal written as in Go: one character
// or one escape between single quotes. It reports false for anything else.
func characterValue(text string) (rune, bool) {
	if len(text) < 3 || text[0] != '\'' || text[len(text)-1] != '\'' {
		return 0, false
	}
	value, _, tail, err := strconv.UnquoteChar(text[1:len(text)-1], '\'')
	if err != nil || tail != "" {
		return 0, false
	}
	return value, true
}

type parser struct {
	src  string
	toks []token
	pos  int
}

// ParseFormula parses a formula or integer expression clause.
func ParseFormula(src string) (*Node, error) {
	return parse(src, func(p *parser) *Node { return p.formula() })
}

// ParseTargets parses the list of a Modifies clause: paths such as A, p,
// s.items, and cs[0], separated by commas.
func ParseTargets(src string) ([]*Node, error) {
	var targets []*Node
	_, err := parse(src, func(p *parser) *Node {
		for {
			target := p.postfix()
			for n := target; ; n = n.Kids[0] {
				if (n.Kind != NIdent && n.Kind != NField && n.Kind != NIndex) || n.Primed {
					panic(&SyntaxError{target.Start, "a Modifies clause lists what is reached from the parameters, as in \"A, s.items, cs[0]\""})
				}
				if n.Kind == NIdent {
					break
				}
			}
			targets = append(targets, target)
			if !p.accept(",") {
				return target
			}
		}
	})
	return targets, err
}

// ParseSnapshot parses a Snapshot clause, "name = value", where the value
// is a formula or an integer expression.
func ParseSnapshot(src string) (name string, value *Node, err error) {
	value, err = parse(src, func(p *parser) *Node {
		name = p.ident()
		if !p.accept("=") {
			p.fail("a Snapshot is written as name = value, as in // @Snapshot r0 = r")
		}
		return p.formula()
	})
	return name, value, err
}

// ParsePredicate parses a predicate definition clause.
func ParsePredicate(src string) (*PredDecl, error) {
	decl := &PredDecl{}
	_, err := parse(src, func(p *parser) *Node {
		decl.Name = p.ident()
		p.expect("(")
		for !p.accept(")") {
			if len(decl.Params) > 0 {
				p.expect(",")
			}
			decl.Params = append(decl.Params, p.ident())
		}
		p.expect("::=")
		decl.Body = p.formula()
		return decl.Body
	})
	if err != nil {
		return nil, err
	}
	return decl, nil
}

func parse(src string, production func(*parser) *Node) (n *Node, err error) {
	toks, err := lex(src)
	if err != nil {
		return nil, err
	}
	defer func() {
		if r := recover(); r != nil {
			syntaxErr, ok := r.(*SyntaxError)
			if !ok {
				panic(r)
			}
			n, err = nil, syntaxErr
		}
	}()
	p := &parser{src: src, toks: toks}
	n = production(p)
	if p.peek().kind != 'e' {
		p.fail("unexpected %q", p.peek().text)
	}
	return n, nil
}

func (p *parser) peek() token { return p.toks[p.pos] }

func (p *parser) fail(format string, args ...any) {
	panic(&SyntaxError{p.peek().pos, fmt.Sprintf(format, args...)})
}

// is reports whether the next token is the given operator or keyword.
func (p *parser) is(text string) bool {
	tok := p.peek()
	return (tok.kind == 'i' || tok.kind == 'o') && tok.text == text
}

func (p *parser) accept(text string) bool {
	if p.is(text) {
		p.pos++
		return true
	}
	return false
}

func (p *parser) acceptAny(texts ...string) (string, bool) {
	for _, text := range texts {
		if p.accept(text) {
			return text, true
		}
	}
	return "", false
}

func (p *parser) expect(text string) {
	if !p.accept(text) {
		found := p.peek().text
		if found == "" {
			found = "end of annotation"
		}
		p.fail("expected %q, found %q", text, found)
	}
}

func (p *parser) ident() string {
	tok := p.peek()
	if tok.kind != 'i' {
		p.fail("expected a name, found %q", tok.text)
	}
	p.pos++
	return tok.text
}

// end returns the offset just past the most recently consumed token.
func (p *parser) end() int {
	last := p.toks[p.pos-1]
	return last.pos + last.size
}

func (p *parser) binary(op string, left, right *Node) *Node {
	return &Node{Kind: NBinary, Op: op, Kids: []*Node{left, right}, Start: left.Start, End: right.End}
}

func (p *parser) formula() *Node {
	left := p.implication()
	for p.accept("<->") {
		left = p.binary("<->", left, p.implication())
	}
	return left
}

func (p *parser) implication() *Node {
	left := p.disjunction()
	if p.accept("->") {
		return p.binary("->", left, p.implication())
	}
	return left
}

func (p *parser) disjunction() *Node {
	left := p.conjunction()
	for {
		if _, ok := p.acceptAny("Or", "||"); !ok {
			return left
		}
		left = p.binary("Or", left, p.conjunction())
	}
}

func (p *parser) conjunction() *Node {
	left := p.negation()
	for {
		if _, ok := p.acceptAny("And", "&&"); !ok {
			return left
		}
		left = p.binary("And", left, p.negation())
	}
}

func (p *parser) negation() *Node {
	start := p.peek().pos
	if _, ok := p.acceptAny("~", "!"); ok {
		kid := p.negation()
		return &Node{Kind: NUnary, Op: "~", Kids: []*Node{kid}, Start: start, End: kid.End}
	}
	if p.is("Forall") || p.is("Exists") {
		return p.quantifier()
	}
	return p.comparison()
}

// quantifier parses "Forall x, y in domain : body". The domain is Z or an
// interval with square (closed) or round (open) ends; the body extends as far
// to the right as possible.
func (p *parser) quantifier() *Node {
	n := &Node{Kind: NQuant, Start: p.peek().pos, Op: p.ident()}
	n.Vars = append(n.Vars, p.ident())
	for p.accept(",") {
		n.Vars = append(n.Vars, p.ident())
	}
	p.expect("in")
	if _, unbounded := p.acceptAny("Z", "ℤ"); !unbounded {
		open, ok := p.acceptAny("[", "(")
		if !ok {
			p.fail("expected a quantifier domain: Z or an interval such as [0, n)")
		}
		lo := p.arith()
		p.expect(",")
		hi := p.arith()
		closing, ok := p.acceptAny("]", ")")
		if !ok {
			p.fail("expected ] or ) to close the interval")
		}
		n.LoOpen, n.HiOpen = open == "(", closing == ")"
		n.Kids = []*Node{lo, hi}
	}
	p.expect(":")
	body := p.formula()
	n.Kids = append(n.Kids, body)
	n.End = body.End
	return n
}

func (p *parser) comparison() *Node {
	first := p.arith()
	n := &Node{Kind: NCompare, Kids: []*Node{first}, Start: first.Start}
	for {
		op, ok := p.acceptAny("<=", ">=", "!=", "==", "=", "<", ">")
		if !ok {
			break
		}
		n.Ops = append(n.Ops, op)
		n.Kids = append(n.Kids, p.arith())
	}
	if len(n.Ops) == 0 {
		return first
	}
	n.End = p.end()
	return n
}

func (p *parser) arith() *Node {
	left := p.product()
	for {
		op, ok := p.acceptAny("+", "-")
		if !ok {
			return left
		}
		left = p.binary(op, left, p.product())
	}
}

func (p *parser) product() *Node {
	left := p.unary()
	for {
		op, ok := p.acceptAny("*", "/", "%")
		if !ok {
			return left
		}
		left = p.binary(op, left, p.unary())
	}
}

func (p *parser) unary() *Node {
	start := p.peek().pos
	if p.accept("-") {
		kid := p.unary()
		return &Node{Kind: NUnary, Op: "-", Kids: []*Node{kid}, Start: start, End: kid.End}
	}
	if p.accept("&") {
		kid := p.postfix()
		return &Node{Kind: NAddr, Kids: []*Node{kid}, Start: start, End: kid.End}
	}
	return p.postfix()
}

// postfix parses what may follow a primary expression: a field selection
// x.f, which may be primed, indexing A[i], and the slice-range shorthands
// A[lo:hi) and A[lo:hi].
func (p *parser) postfix() *Node {
	n := p.primary()
	for {
		if p.accept(".") {
			n = &Node{Kind: NField, Name: p.ident(), Kids: []*Node{n}, Start: n.Start}
			n.Primed = p.accept("'")
			n.End = p.end()
			continue
		}
		if !p.accept("[") {
			return n
		}
		index := p.arith()
		if !p.accept(":") {
			p.expect("]")
			n = &Node{Kind: NIndex, Kids: []*Node{n, index}, Start: n.Start, End: p.end()}
			continue
		}
		hi := p.arith()
		closing, ok := p.acceptAny(")", "]")
		if !ok {
			p.fail("expected ) or ] to close the slice range")
		}
		n = &Node{
			Kind: NRange, Kids: []*Node{n, index, hi}, Closed: closing == "]",
			Start: n.Start, End: p.end(),
		}
	}
}

// primary parses literals, names, predicate applications, parenthesised
// formulas, and the |A| length form.
func (p *parser) primary() *Node {
	tok := p.peek()
	n := &Node{Start: tok.pos}
	switch {
	case tok.kind == 'n':
		p.pos++
		value, _ := new(big.Int).SetString(tok.text, 10)
		n.Kind, n.Big = NInt, value
	case tok.kind == 'c':
		// A character is the number of its code point; the literal is kept
		// for messages.
		p.pos++
		value, _ := new(big.Int).SetString(tok.text, 10)
		n.Kind, n.Big, n.Name = NInt, value, p.src[tok.pos:tok.pos+tok.size]
	case tok.kind == 's':
		p.pos++
		n.Kind, n.Name = NStr, tok.text
	case p.accept("nil"):
		n.Kind = NNil
	case p.accept("True"):
		n.Kind, n.Val = NBool, 1
	case p.accept("False"):
		n.Kind = NBool
	case tok.kind == 'i':
		p.pos++
		n.Kind, n.Name = NIdent, tok.text
		if p.accept("(") {
			n.Kind = NCall
			for !p.accept(")") {
				if len(n.Kids) > 0 {
					p.expect(",")
				}
				n.Kids = append(n.Kids, p.formula())
			}
		} else if p.accept("'") {
			n.Primed = true
		}
	case p.accept("("):
		inner := p.formula()
		p.expect(")")
		inner.Start, inner.End = tok.pos, p.end()
		return inner
	case p.accept("|"):
		n.Kind, n.Kids = NLen, []*Node{p.arith()}
		p.expect("|")
	default:
		found := tok.text
		if found == "" {
			found = "end of annotation"
		}
		p.fail("expected an expression, found %q", found)
	}
	n.End = p.end()
	return n
}
