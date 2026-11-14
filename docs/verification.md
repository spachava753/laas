# Writing verified Go

## Introduction

`vego` proves things about Go functions. You say what a function must do in comments that start with `//@`, and `vego` either proves that the function does it for every input, or tells you the first thing it could not prove. The code stays ordinary Go: it builds, runs, and formats as before, and a program that does not use `vego` never notices the comments.

This guide shows how to write Go that `vego` can verify. It is meant to be read from the top once, and then used as a reference; the last section is a summary of every annotation and every piece of the formula language. Every program in it is checked: they all live in `vego/testdata/src/guide`, where the tests of `vego` run them.

Three things are worth knowing before you start.

**What it is good at.** Self-contained logic: index arithmetic, parsers and encoders, data structures, validation, the core of a package. For that code `vego` proves that nothing panics, that no integer overflows, that loops and recursion end, that the function meets its contract, and that it changes nothing it did not say it would.

**What it never does.** It never says a function is correct when it is not. When it cannot follow a piece of Go, it says `cannot verify` and names the construct. When it cannot find a proof, it says `may not hold`. That message means "not proved", which is not the same as "false": sometimes the code is wrong, sometimes the contract is, and sometimes both are right and the prover needs a hint. Most of this guide is about telling those apart.

**What it does not cover yet.** A good deal of everyday Go: interfaces other than `error`, closures, generics, goroutines, arrays, and more. [What is not supported](#what-is-not-supported) has the list. `vego` is experimental, and you will meet these limits quickly in code that talks to the outside world.

## Running it

`vego` is one of the analyzers of the `laas` command:

```sh
go install github.com/spachava753/laas/cmd/laas@latest
laas ./...
```

A function is verified when it has at least one `//@` annotation. Every other function is left alone, so you can start with one function in a large package.

Run `laas` directly. It refuses to verify under `go vet -vettool`, whose cache could keep a proof alive after the assumptions it rests on have changed.

## A first proof

Here is a function with a contract.

```go
// Max returns the larger of two numbers.
func Max(a, b int) int {
	if a > b {
		return a
	}
	return b
}

//@ Ensures result >= a And result >= b
//@ Ensures result = a Or result = b
```

`Ensures` says what holds when the function returns. `result` is the name of the value it returns. Running `laas` on this prints nothing: both clauses are proved for every `a` and `b`.

Now break it, by returning `b` on both branches:

```text
vego: postcondition may not hold: result >= a
```

The message points at the `return` that fails and names the part of the contract that fails there. A clause joined with `And` is checked piece by piece, so you are told which piece.

The next one is more interesting, because the code looks right.

```go
func Abs(x int) int {
	if x < 0 {
		return -x
	}
	return x
}

//@ Ensures result >= 0
```

```text
vego: negation may overflow int
```

There is one `int` whose negation is not an `int`: the smallest one. For that input Go returns a negative number from `Abs`, silently. `vego` found it without being asked, because it checks every arithmetic operation of a verified function. The fix is to say that the function is not meant for that input:

```go
// @ Requires x > MinInt
func Abs(x int) int {
	if x < 0 {
		return -x
	}
	return x
}

//@ Ensures result >= 0 And (result = x Or result = -x)
```

`Requires` is the other half of a contract: what must hold when the function is called. Inside the function it may be assumed. Every verified caller has to prove it.

That is the whole method. You write down what you expect, `vego` shows you where the code and the expectation part ways, and you change one of them.

## Annotations

An annotation is a `//` comment that starts with `@` and a keyword. There are eight keywords, and each has a place.

In the doc comment of a function: `Requires`, `Ensures`, `Modifies`, and `Measure`.

After the closing brace of a function: `Ensures`, which may go there or in the doc comment. A contract reads well with the precondition above the function and the postcondition below it, and this guide writes it that way.

Directly above a loop: `Invariant` and `Variant`.

Anywhere in a body, on a line of its own: `Assert`.

In the doc comment of a struct type: `Invariant`.

At the top level of a file: `Predicate`.

Write `//@` or `// @`; both are read. `gofmt` turns the first into the second inside doc comments, so you will see both in formatted code. A long annotation continues on the next `//@` line that does not start with a keyword, and `//` inside an annotation starts an ordinary comment.

A misspelt keyword is an error, not a comment that is silently skipped: `//@ Ensure`, `//@ensures`, and an annotation inside `/* */` are all reported.

## Formulas

The text after a keyword is a formula. Formulas look like Go conditions with a few differences.

Logic is written with words: `And`, `Or`, `->` for "implies", `<->` for "exactly when", and `~` for "not". Equality is a single `=`. Comparisons chain, so `0 <= i < n` means what it says.

```go
//@ Ensures result = -1 Or (0 <= result < |A| And A[result] = x)
```

Numbers are mathematical integers. `x + 1` in a formula is one more than `x` and never wraps, whatever the type of `x`. The limits of the Go types have names: `MaxInt`, `MinInt`, `MaxInt8` to `MaxInt64`, `MinInt8` to `MinInt64`, and `MaxUint` to `MaxUint64`. `/` and `%` round as they do in Go.

`|A|` is the length of a slice or a string, and the number of keys of a map. `A[i]` is an element. Fields are reached with a dot, through pointers as well: `c.count`, `s.items[i]`, `|s.items|`.

`Forall` and `Exists` range over an interval:

```go
//@ Requires Forall k in [0, |A|) : 0 <= A[k] <= 1000
//@ Ensures Exists k in [0, |A|) : A[k] = result
```

The interval is written as in mathematics: `[0, n)` includes `0` and leaves out `n`, `[0, n]` includes both. Several variables can share one interval, as in `Forall i, j in [0, n) : ...`, and `in Z` ranges over all integers.

A formula talks about values, so it can use strings and `nil` too: `role = "admin"`, `p != nil`, `err = nil`.

There are no bit operators, no function calls except to predicates, and no floating-point facts.

## Names, before and after

In a contract, the names are the parameters and the results of the function. An unnamed single result is `result`; several unnamed results are `result1`, `result2`, and so on. Named results keep their names.

A parameter in an `Ensures` clause means its value when the function was called. That needs care only for memory the function may change: the contents of a slice, the fields behind a pointer, a map. For those, a prime means the state on return.

```go
// @ Modifies A
func Fill(A []int, v int) {
	//@ Invariant Forall k in [0, i) : A[k] = v
	for i := range A {
		A[i] = v
	}
}

//@ Ensures Forall k in [0, |A|) : A'[k] = v
```

`A'[k]` is element `k` when `Fill` returns; `A[k]` would be the element it had on entry. For a field it is `c.n'` and `c.n`.

Inside a body the convention is the other way round. A name in an `Invariant` or an `Assert` means the value now, and `old(x)` means what a parameter was on entry.

## Safety comes free

You do not ask for the checks in this section. Every verified function gets them.

**Indexing.** An index must be proved to be in range.

```go
func First(A []int) int {
	return A[0]
}
```

```text
vego: index may be out of range
```

Add `// @ Requires |A| > 0` and the message goes away, and every verified caller of `First` now has to show that its slice is not empty.

**Nil.** A pointer must be proved not to be nil where it is followed. For a parameter or a receiver that usually means `Requires p != nil`.

**Division.** A divisor must be proved not to be zero.

**Overflow.** Every `+`, `-`, `*`, `/`, negation, conversion, and shift to the left must be proved to stay within its type.

```go
// @ Requires 0 <= lo <= hi
func Mid(lo, hi int) int {
	return (lo + hi) / 2
}
```

```text
vego: addition may overflow int
```

`lo + hi` can exceed the largest `int` although the midpoint never does. Write `lo + (hi-lo)/2` and it verifies.

Overflow is the check you will meet most often. Code that adds up values needs to know that they are small, so contracts acquire bounds on their inputs:

```go
// @ Requires |A| <= 1000
// @ Requires Forall k in [0, |A|) : 0 <= A[k] <= 1000
func Sum(A []int) int {
```

This is not busywork. It is the difference between a function that is correct and one that is correct for the inputs you happened to imagine.

Code that wraps on purpose, such as a hash function, cannot be verified, and neither can a conversion that drops bits: `byte(x)` is an error unless `x` is known to fit. `byte(x & 0xFF)` is fine.

**Allocation.** `make`, an `append` that has to grow, and a string concatenation must be proved not to ask for more than can be allocated, which again means bounding sizes.

**Panics.** A reachable `panic` is an error.

## Loops

`vego` does not run a loop. It reasons about one arbitrary iteration, and for that it needs to know what is true every time the loop is about to test its condition. You tell it with `Invariant`.

```go
// @ Requires n >= 0 And d > 0
func Divide(n, d int) (q, r int) {
	q, r = 0, n
	//@ Invariant n = d*q + r And 0 <= r
	//@ Variant r
	for d <= r {
		q, r = q+1, r-d
	}
	return q, r
}

//@ Ensures n = d*q + r And 0 <= r < d
```

Three things are checked. The invariant holds when the loop is first reached. If it holds before an iteration, it holds after. And when the loop ends, the invariant together with the failed condition is all that is known, which here is exactly the postcondition: `n = d*q + r`, `0 <= r`, and not `d <= r`.

That last point is the one to remember. **After a loop, `vego` knows the invariant and nothing else about what the loop changed.** If the proof of the code after a loop fails, the invariant is too weak: something you know about the loop variables is not written down.

`Variant` is a number that is never negative while the loop runs and gets smaller each time round, which proves that the loop ends. A `for` loop needs one.

A `range` loop needs no `Variant`, and it knows the bounds of its index without being told.

```go
// @ Requires |A| <= 1000
// @ Requires Forall k in [0, |A|) : 0 <= A[k] <= 1000
func Sum(A []int) int {
	total := 0
	//@ Invariant 0 <= total <= 1000 * i
	for i := range A {
		total += A[i]
	}
	return total
}

//@ Ensures 0 <= result <= 1000 * |A|
```

The invariant says how large `total` can be after `i` elements. That is what lets `total += A[i]` pass the overflow check, and with `i = |A|` at the end it gives the postcondition.

When a loop builds something up element by element, the invariant usually says "the part done so far is right":

```go
func Index(A []int, x int) int {
	//@ Invariant Forall k in [0, i) : A[k] != x
	for i := range A {
		if A[i] == x {
			return i
		}
	}
	return -1
}

//@ Ensures result = -1 Or (0 <= result < |A| And A[result] = x)
//@ Ensures result = -1 -> Forall k in [0, |A|) : A[k] != x
```

A good way to find an invariant is to take the postcondition and replace the end of the range by the loop counter.

`break`, `continue`, and `return` inside a loop all work. A `return` inside a loop has to establish the postcondition from the invariant and whatever the path to it adds.

## Recursion

A recursive function says why it stops with `Measure`: a number over its parameters that is never negative and is smaller at every recursive call. Functions that call each other need one each.

```go
// @ Requires n >= 0
// @ Measure n
func Steps(n int) int {
	if n == 0 {
		return 0
	}
	return 1 + Steps(n-1)
}

//@ Ensures result = n
```

At the recursive call, `vego` uses the contract of `Steps` for `n-1`, not its body, exactly as it would for any other call.

## Calls

A call is verified against the contract of what is called, and only the contract.

```go
// @ Requires lo <= hi
func Clamp(x, lo, hi int) int {
	if x < lo {
		return lo
	}
	if x > hi {
		return hi
	}
	return x
}

//@ Ensures lo <= result <= hi

func Percent(x int) int {
	return Clamp(x, 0, 100)
}

//@ Ensures 0 <= result <= 100
```

`Percent` must prove `0 <= 100`, and then knows `0 <= result <= 100` and nothing more. It does not know that `Clamp` returns `x` when `x` is already in range, because the contract does not say so. If a caller needs a fact about a function, the fact belongs in that function's `Ensures`.

This is what keeps verification manageable: each function is proved once, alone. It also means that an underspecified function is a problem for its callers, not for itself.

A function with no contract cannot be called from verified code at all:

```text
vego: cannot verify CallsHelper: it calls helper, which has no contract; annotate
helper with //@ so that it is verified, or add a trusted contract for guide.helper
to vego-trusted.yaml
```

Either verify the helper too, or see [Code that is not verified](#code-that-is-not-verified).

An exported function's contract is visible to other packages, so verified code can call verified code across package boundaries.

## Predicates

A formula you need more than once can be given a name.

```go
//@ Predicate sorted(A) ::= Forall i, j in [0, |A|) : i <= j -> A[i] <= A[j]

// @ Requires sorted(A) And |A| > 0
func Smallest(A []int) int {
	return A[0]
}

//@ Ensures Forall k in [0, |A|) : result <= A[k]
```

A predicate takes numbers and slices of numbers. It may be recursive, as long as the recursion does not pass through a negation.

## Helping the prover

The prover is sound and deliberately limited. It is good at linear arithmetic, at reading and writing slices, and at instantiating a `Forall` where it sees a use for it. It knows a little about products of two variables. When it fails on something true, the cure is nearly always to state an intermediate fact.

`Assert` does that. It must be proved where it stands, and everything after it may use it.

```go
//@ Assert lo < |A|
```

Use it to find out what `vego` knows: put the fact you believe in an `Assert` and move it up through the function until it is proved. The place where it stops being provable is where the knowledge is lost, often a loop whose invariant does not carry it.

Some things that work without help, so you know what to expect:

```go
// @ Requires 0 <= i < h And 0 <= j < w And h <= 1000 And w <= 1000
func Cell(i, j, w, h int) int {
	return i*w + j
}

//@ Ensures 0 <= result < h*w
```

If a proof is true and still does not go through, `-vego.max-steps` raises the effort the prover spends on each obligation.

## Slices

A slice parameter is a view of an array that the caller may also see, so a function has to say whether it writes it.

```go
// @ Modifies A
func Fill(A []int, v int) {
```

`Modifies A` allows writing the elements of `A`. Without it, the write is an error:

```text
vego: A[i] is assigned, which FillUnlisted may not modify; list it in a //@ Modifies clause
```

The clause works in both directions. A function may write only what it lists, and it must need everything it lists, so `Modifies` never claims more than the body does. A caller then knows that anything not listed is unchanged.

Two rules about slices save a great deal of annotation, and are worth knowing.

**Slice parameters of one element type do not overlap.** A function may assume that two `[]int` parameters are different memory, and every verified call has to prove it. `Copy(A, A[1:])` is rejected.

**`Modifies A` covers the capacity of `A`**, not only its length, because `append` may write there.

`append` is supported as the whole right-hand side of an assignment or as the returned value.

```go
// @ Requires |A| < 1000
// @ Modifies A
func Push(A []int, x int) []int {
	return append(A, x)
}

//@ Ensures |result| = |A| + 1 And result[|A|] = x
```

An `append` either writes into spare capacity, where other slices of the same array see it, or moves to a new array. `vego` verifies both outcomes unless it can rule one out. That is why `Push` needs `Modifies A`, and why it needs a bound on the length.

Slicing `A[i:j]` and `A[i:j:k]`, `len`, `cap`, `make`, and slice literals are supported. `copy` and `append(s, t...)` are not yet.

## Strings

A string is a sequence of bytes that nobody can change. `|s|`, `s[i]`, `==`, literals, concatenation, substrings, and conversion to and from `[]byte` are understood.

```go
// @ Requires |a| <= 1000 And |b| <= 1000
func Join(a, b string) string {
	return a + b
}

//@ Ensures |result| = |a| + |b|

func IsAdmin(role string) bool {
	return role == "admin"
}

//@ Ensures result <-> role = "admin"
```

Ordering with `<` is not known. Ranging over a string yields some character and moves on by one to four bytes; which character is not modelled.

## Structs and pointers

Fields are read and written as in Go, and a contract names them with a dot.

```go
type Counter struct {
	n     int
	limit int
}

// @ Requires c != nil And c.n < c.limit
// @ Modifies c.n
func (c *Counter) Inc() {
	c.n++
}

//@ Ensures c.n' = c.n + 1
```

`Modifies` takes paths that start at a parameter. `Modifies c` is every field of the struct `c` points to. `Modifies c.n` is one field, and tells callers that `c.limit` is untouched:

```go
// @ Requires c != nil And c.n = 0 And c.limit = 10
// @ Modifies c.n
func Twice(c *Counter) {
	c.Inc()
	c.Inc()
}

//@ Ensures c.n' = 2 And c.limit' = 10
```

Other forms: `Modifies ps[0]` for one element of a slice of structs, `Modifies s.items` for the elements of a slice in a struct, `Modifies m` for a map.

### Two names for one thing

Two pointers may point to the same struct. `vego` does not forbid that, and it does not assume that they differ. A proof has to hold in both cases.

```go
// @ Requires a != nil And b != nil
// @ Modifies a.n, b.n
func SameOrNot(a, b *Counter) int {
	a.n = 1
	b.n = 2
	return a.n
}

//@ Ensures result = 1
```

```text
vego: postcondition may not hold: result = 1
```

If `a` and `b` are the same counter, this returns 2. Either the function is meant to work for that case and the contract is wrong, or it is not and the contract should say so: add `And a != b` to the `Requires` and it verifies.

The same holds for memory inside other memory. A `*Point` may point at an element of a `[]Point` or at a field of a larger struct. `~within(p, ps)` says that it does not.

### New things

What a function creates itself, it may write freely: `&T{...}`, `new`, `make`, a literal, a local variable. To tell a caller that a result is new, and so cannot be anything the caller already had, say `fresh`:

```go
func NewCounter(limit int) *Counter {
	return &Counter{limit: limit}
}

//@ Ensures fresh(result) And result.n = 0 And result.limit = limit
```

Without `fresh(result)`, a caller must allow that the result is some counter it already holds.

`&x`, `&p.field`, and `&s[i]` are supported when they point to a struct, and so are methods with pointer receivers on variables, fields, and elements. A pointer to anything but a struct, such as `*int`, is not supported.

## Invariants of structs

A fact that should hold of every value of a type can be stated once, on the type.

```go
// Stack keeps a count that never exceeds what it holds.
//
// @ Invariant 0 <= n <= |items|
type Stack struct {
	items []int
	n     int
}

// @ Requires s != nil And s.n > 0
func (s *Stack) Top() int {
	return s.items[s.n-1]
}

//@ Ensures result = s.items[s.n-1]
```

`Top` may index with `s.n-1` because the invariant bounds `n`. An invariant works like a clause that is added to every contract: it may be assumed of every parameter and receiver of the type on entry, and must be proved of them, and of every result of the type, on return and at every call. In between, a function may break it and put it right again.

There is no way to switch an invariant off for one function.

## Maps

A map is a reference, like a pointer: two map variables may be the same map, and writing one needs `Modifies`. In a formula, `m[k]` is the value of a key, which is the zero value when the key is absent, as in Go. `has(m, k)` says whether the key is present, and `|m|` is the number of keys.

```go
func Get(m map[string]int, k string) (v int, err error) {
	v, ok := m[k]
	if !ok {
		return 0, ErrMissing
	}
	return v, nil
}

//@ Ensures err = nil <-> has(m, k)
//@ Ensures err = nil -> v = m[k]

// @ Requires m != nil And m[k] < 1000
// @ Modifies m
func Bump(m map[string]int, k string) {
	m[k] = m[k] + 1
}

//@ Ensures has(m', k) And m'[k] = m[k] + 1
```

Keys are integers or strings. Writing to a map needs a proof that it is not nil; reading and `delete` do not. A `range` over a map can check each value but cannot add them up: the verifier does not know that each key is visited once.

## Errors

About an error, `vego` knows one thing: whether it is `nil`. `errors.New` and `fmt.Errorf` return an error that is not nil, and so does a package-level variable declared with one of them.

A function that returns an error has to say when it succeeds.

```go
var ErrEmpty = errors.New("empty")

func Head(A []int) (first int, err error) {
	if len(A) == 0 {
		return 0, ErrEmpty
	}
	return A[0], nil
}

//@ Ensures err = nil <-> |A| > 0
//@ Ensures err = nil -> first = A[0]
```

The second clause alone would not do:

```text
vego: the contract of HeadWeak would also be met by a function that always
returns an error; state when it succeeds with a clause such as
"condition -> err = nil", where the condition is about the inputs and some
input satisfies it
```

A contract of the form "if it succeeds, then..." is met by a function that never succeeds. `vego` rejects such a contract, because it is the easiest way to write a specification that says nothing.

The exception is a function whose success truly depends on something outside the program:

```go
func ParsePort(s string) (port int, err error) {
	n, err := strconv.Atoi(s)
	if err != nil {
		return 0, err
	}
	if n < 1 || n > 65535 {
		return 0, ErrRange
	}
	return n, nil
}

//@ Ensures err = nil -> 1 <= port <= 65535
```

Nothing says which strings `strconv.Atoi` accepts, so `ParsePort` cannot promise success for any input, and is not asked to.

`fmt.Errorf` may format numbers, booleans, strings, and errors that the function made itself. Which error it is, as in `errors.Is` or a comparison with `io.EOF`, is not supported yet.

## Defer

A deferred call is verified where it runs: at every return of the function, after the results have their values, last one first.

```go
// @ Requires l != nil And ~l.held And c != nil And c.n < c.limit
// @ Modifies l, c.n
func Guarded(l *Lock, c *Counter, skip bool) {
	l.Acquire()
	defer l.Release()
	if skip {
		return
	}
	c.Inc()
}

//@ Ensures ~l.held'
```

Both ways out of `Guarded` release the lock, and the `Requires` of `Release` is proved at each. The receiver and the arguments of a deferred call are fixed where the `defer` is written, as in Go.

Only a call of a named function or method can be deferred, and not inside a loop. `defer func() { ... }()` is not supported yet.

## Bits

`vego` computes with whole numbers, so it understands shifts and bitwise operators through arithmetic.

```go
func Pack(hi, lo byte) uint16 {
	return uint16(hi)<<8 | uint16(lo)
}

//@ Ensures result = 256 * hi + lo
```

`x << k` is `x * 2^k` and must not lose bits. `x >> k` is a division by `2^k` that rounds down. `x & 0xFF` is `x % 256`, and any mask of low bits or of a single bit is understood exactly. Of `x & y` in general only the bounds are known. Formulas have no bit operators; write what you mean with `*`, `/`, and `%`.

## Code that is not verified

Verified code has to call code that is not: the standard library, other modules, and functions of your own that use Go `vego` cannot follow. Such a function gets a **trusted contract**, a claim that `vego` uses and does not check.

Trusted contracts live in one file, `vego-trusted.yaml`, next to `go.mod`. There is no way to declare trust in source, so that file holds every assumption your proofs rest on.

```yaml
version: 1

trusted:
  example.com/shop/internal/store.load:
    reason: Reads the stock file; reviewed 2026-11-10.
    modifies: []
    ensures:
      - "err = nil -> count >= 0"
```

The key is the function's full name as Go prints it, such as `sort.Ints` or `(*bytes.Buffer).Len`. `reason` is required and says why you believe the contract. `modifies` is required too, even when it is empty. `requires` and `ensures` are lists of formulas over the function's parameter and result names. Quote the formulas, because YAML gives its own meaning to several characters they use.

`vego` ships contracts for a few functions of the standard library, among them `sort.Ints`, `strings.HasPrefix`, `strings.Index`, `strconv.Itoa`, and `strconv.Atoi`. An entry of your own for the same function replaces the shipped one.

To see everything a project takes on trust, with reasons and the places that rely on it:

```sh
laas -vego.trust ./...
```

A trusted contract that is wrong makes every proof that uses it worthless. Keep them few and weak: claim only what the documentation of the function promises.

## Is the contract any good?

A function can be verified against a contract that says almost nothing. `-vego.audit` looks for that. It tries degenerate implementations against each contract, such as "return zero" or "leave the slice alone", and reports the ones the contract would accept.

```sh
laas -vego.audit ./...
```

```text
vego: specification of Sort has a hole [OBLIVIOUS]: it also accepts an implementation
that fills its slices with 0, 1, 2, ... whatever the input
```

A sort whose contract only says that the output is sorted gets this report, and rightly.

## When a proof fails

Work through these in order.

1. **Read the message as "not proved".** It names an obligation and a place. Ask first whether the obligation is true there for every input the `Requires` allows. Try the extremes: zero, negative numbers, the largest `int`, an empty slice, `nil`, two arguments that are the same object.
2. **If it is false, you have found a bug**, in the code or in the contract. Fix whichever is wrong. A missing `Requires` is the commonest case.
3. **If it is true and comes after a loop**, the invariant does not say enough. Everything the loop changes is forgotten except what the invariant states.
4. **If it is true and comes after a call**, the callee's `Ensures` does not say enough. Strengthen it there.
5. **If it is an overflow**, some input needs a bound, or the expression can be rearranged, as with the midpoint.
6. **If it involves two pointers or two slices**, ask whether they may be the same, and say so if they may not.
7. **Otherwise, help the prover.** Put the fact in an `Assert` just before the failure. If the `Assert` is proved and the failure remains, add a smaller step. If the `Assert` is not proved, move it up until it is.

A message that says `cannot verify` is different: the function uses Go that is not supported. The choices are to rewrite that part, or to move it into a function of its own with a trusted contract.

## What is not supported

A function that uses any of these is reported as `cannot verify`:

- interfaces other than `error`, and calls through them;
- function values and closures, including `defer func() { ... }()`;
- generic functions and types;
- goroutines, channels, and `select`;
- arrays, and any struct that holds one;
- pointers to anything but a struct;
- calls to variadic functions, `append(s, t...)`, and `copy`;
- a call that modifies memory inside a condition or a larger expression, as in `if !s.Push(x)`: such a call has to be a statement of its own;
- comparing structs or errors with `==`, `errors.Is`, and reading another package's error variable such as `io.EOF`;
- `goto`, labelled `break` and `continue`, and `defer` inside a loop.

Floats are allowed but opaque: they can be passed around and computed with, and nothing can be said or proved about their values.

## What a proof assumes

A proof by `vego` is a proof under these assumptions. They are about things it cannot see.

- **Trusted contracts are true**, and the functions behind them do not panic, write nothing beyond their `modifies`, and do not keep the pointers and slices they are given.
- **Callers that are not verified keep the contract**: they establish the `Requires`, hand over structs whose invariants hold, and do not pass overlapping slices where two slice parameters have one element type.
- **Code that is not verified keeps Go's types**: no `unsafe`, `reflect`, or cgo that makes one piece of memory two types or changes a string.
- **Nothing else runs at the same time.** A proof is about one goroutine.
- **The platform is the one `laas` ran for.** A proof for a 64-bit target is not a proof for a 32-bit one.
- **The machine has the memory and the stack.**

## Summary

### Annotations

| Annotation | Where | Meaning |
| --- | --- | --- |
| `Requires P` | doc comment of a function | Must hold when the function is called. |
| `Ensures P` | doc comment, or after the closing brace | Holds when the function returns. |
| `Modifies a, b.f` | doc comment of a function | What the function may write that a caller can see. |
| `Measure e` | doc comment of a recursive function | Never negative, smaller at each recursive call. |
| `Invariant P` | directly above a loop | Holds each time the loop tests its condition. |
| `Variant e` | directly above a `for` loop | Never negative, smaller each iteration. |
| `Assert P` | in a body | Must hold there; usable afterwards. |
| `Invariant P` | doc comment of a struct type | Holds of every value of the type at function boundaries. |
| `Predicate name(x, y) ::= P` | top level | Names a formula. |

### Formulas

| Form | Meaning |
| --- | --- |
| `P And Q`, `P Or Q`, `~P` | and, or, not |
| `P -> Q`, `P <-> Q` | implies, exactly when |
| `True`, `False` | |
| `=`, `!=`, `<`, `<=`, `>`, `>=` | comparisons; they chain: `0 <= i < n` |
| `+`, `-`, `*`, `/`, `%` | on mathematical integers; `/` and `%` round as in Go |
| `MaxInt`, `MinInt`, `MaxInt8` ... `MaxUint64` | limits of the Go types |
| `MaxAlloc` | most bytes one allocation can have |
| <code>&#124;A&#124;</code> | length of a slice or string, number of keys of a map |
| `A[i]`, `m[k]`, `p.f` | element, map value, field |
| `A[lo:hi) <= x` | every element of that part of `A` compares so |
| `Forall k in [a, b) : P`, `Exists k in [a, b] : P` | over an interval |
| `Forall k in Z : P` | over all integers |
| `"text"`, `nil` | a string, the nil pointer or error |
| `has(m, k)` | the map has the key |
| `name(x, y)` | a predicate |

### Before and after

| Where | Plain name | Marked |
| --- | --- | --- |
| `Requires` | value on entry | |
| `Ensures` | value on entry | `A'`, `c.f'`: on return |
| `Invariant`, `Assert` in a body | value now | `old(x)`: on entry |
| results | `result`, or `result1`, `result2`, or their own names | |

### Memory

| Form | Meaning |
| --- | --- |
| `Modifies p` | every field of the struct `p` points to |
| `Modifies p.f` | one field |
| `Modifies A`, `Modifies s.items` | the elements of a slice, up to its capacity |
| `Modifies ps[0]` | one element |
| `Modifies m` | a map |
| `fresh(x)` | the call created what `x` refers to |
| `within(a, b)` | `a` lies inside `b`; each is a slice or a pointer |

### Flags

| Flag | Effect |
| --- | --- |
| `-vego.audit` | also report contracts that degenerate implementations satisfy |
| `-vego.max-steps=n` | effort the prover spends on one obligation |
| `-vego.trusted=path` | the trust file, instead of the one next to `go.mod` |
| `-vego.trust` | print what the proofs take on trust |
