# Writing verified Go

## Introduction

`vego` proves things about Go functions. You say what a function must do in comments that start with `//@`, and `vego` either proves that the function does it for every input, or tells you what it could not prove. The code stays ordinary Go: it builds, runs, and formats as before, and a program that does not use `vego` never notices the comments.

This guide shows how to write Go that `vego` can verify. It is meant to be read from the top once, and then used as a reference: [Messages](#messages) explains what the tool prints, and the [Summary](#summary) lists every annotation and every piece of the formula language. The programs in it are checked: they live in `vego/testdata/src/guide`, where the tests of `vego` run them.

Three things are worth knowing before you start.

**What it is good at.** Self-contained logic: index arithmetic, parsers and encoders, data structures, validation, the core of a package. For that code `vego` proves that nothing panics, that no integer overflows, that loops and recursion end, that the function meets its contract, and that it changes nothing it did not say it would.

**What it never does.** It never says a function is correct when it is not. When it cannot follow a piece of Go, it says `cannot verify` and names the construct. When it cannot find a proof, it says `may not hold`. That message means "not proved", which is not the same as "false": sometimes the code is wrong, sometimes the contract is, and sometimes both are right and the prover needs a hint. Most of this guide is about telling those apart.

**What it does not cover yet.** A good deal of everyday Go: interfaces other than `error`, closures, generics, goroutines, arrays, package-level variables, and more. [What is not supported](#what-is-not-supported) has the list. `vego` is experimental, and you will meet these limits quickly in code that talks to the outside world. The usual answer is to keep such code at the edge and verify the logic it calls; [Adopting it](#adopting-it) says how.

## Running it

`vego` is one of the analyzers of the `laas` command.

```sh
go install github.com/spachava753/laas/cmd/laas@latest
laas -vego ./...
```

`laas -vego` runs the verifier alone. Plain `laas` runs it together with the other analyzers of the command, which have opinions about code that has nothing to do with verification. The arguments are package patterns, as for `go vet`: `./...`, or `./internal/core` for one package.

**A function is verified when it has at least one `//@` annotation.** Every other function is left alone, so you can start with one function in a large package. The smallest annotation is `//@ Ensures True`, which promises nothing and turns on [the checks every verified function gets](#safety-comes-free).

**Silence is success.** When everything annotated is proved, `laas` prints nothing and exits with status 0. With anything to report it exits with status 3, and with status 1 when it could not load the packages at all. It does not list what it verified.

A few more things about running it:

- **Toolchain.** The `go` command that `laas` finds when it runs must not be newer than the Go that built `laas`. Installing with the `go` you use every day, as above, takes care of that. If `laas` was built by an older Go, as a pinned build in CI may be, you get errors about the standard library and `analysis skipped`, which are not failed proofs; run it with `GOTOOLCHAIN` set to the version that built it, or rebuild it.
- **A package that does not compile is skipped**, with `vego: analysis skipped due to errors in package`.
- **Test files are included.** `-test=false` leaves them out.
- **`-exclude-packages`** takes a regular expression of import paths to skip.
- **Run `laas` directly.** It refuses to verify under `go vet -vettool`, whose cache could keep a proof alive after the assumptions it rests on have changed.

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

`Ensures` says what holds when the function returns. `result` is the name of the value it returns. Running `laas -vego` on this prints nothing: both clauses are proved for every `a` and `b`.

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

`~` binds tightest, then `And`, then `Or`, then `->`, then `<->`. `a -> b -> c` means `a -> (b -> c)`. When in doubt, use parentheses.

Numbers are mathematical integers. `x + 1` in a formula is one more than `x` and never wraps, whatever the type of `x`. The limits of the Go types have names: `MaxInt`, `MinInt`, `MaxInt8` to `MaxInt64`, `MinInt8` to `MinInt64`, and `MaxUint` to `MaxUint64`. `/` and `%` round as they do in Go.

`|A|` is the length of a slice or a string, and the number of keys of a map; `len(A)` means the same. `A[i]` is an element. Fields are reached with a dot, through pointers as well: `c.count`, `s.items[i]`, `|s.items|`.

`Forall` and `Exists` range over an interval:

```go
//@ Requires Forall k in [0, |A|) : 0 <= A[k] <= 1000
//@ Ensures Exists k in [0, |A|) : A[k] = result
```

The interval is written as in mathematics: `[0, n)` includes `0` and leaves out `n`, `[0, n]` includes both. Several variables can share one interval, as in `Forall i, j in [0, n) : ...`, and `in Z` ranges over all integers. The body of a quantifier runs to the end of the clause, or to the closing parenthesis around the quantifier. `A[lo:hi) <= x` is short for "every element from `lo` up to `hi` is at most `x`", with any comparison.

A formula talks about values, so it can use strings and `nil` too: `role = "admin"`, `p != nil`, `err = nil`.

**Names.** In a contract, the names are the parameters and the results of the function, and the integer and boolean constants of the package. A string constant cannot be named; write the string. An unnamed single result is `result`; several unnamed results are `result1`, `result2`, and so on. Named results keep their names.

**What a formula cannot say.** There are no bit operators, no function calls except to predicates, no character literals (write `48` for `'0'`), no `cap`, and no floating-point facts. A slice cannot be compared with `nil`; say `|A| = 0`. Two structs cannot be compared; compare their fields.

**A formula is not checked for meaning.** `A[i]` in a formula is not required to be in range, and `x / y` may have a divisor of zero. Such a term has some value nobody knows. A clause that depends on it can usually not be proved, but it can also be trivially true, as `A[999] = A[999]` is, and it is not reported. Guard what you write, as you would in code: `0 <= i < |A| And A[i] = x`.

## Safety comes free

You do not ask for the checks in this section. Every verified function gets them, whatever its contract says.

**Indexing.** An index must be proved to be in range.

```go
func First(A []int) int {
	return A[0]
}

//@ Ensures result = A[0]
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

**Termination.** Every loop and every recursion must be shown to end; the next two sections say how.

To get these checks and nothing else for a function, give it a contract that promises nothing:

```go
func SafeOnly(A []int, i int) int {
	if 0 <= i && i < len(A) {
		return A[i]
	}
	return 0
}

//@ Ensures True
```

This is a good first step for existing code.

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

An invariant like this one speaks of the position, so the loop has to name it. `for _, x := range A` gives the invariant nothing to call it; write `for i := range A` and use `A[i]`.

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

Two messages belong to loops. `loop invariant may not hold on entry` means it is not proved before the first iteration: usually it is false there, sometimes the prover needs a hint. `loop invariant may not be preserved` means that one iteration can break it, or that the invariant does not say enough for `vego` to see that it cannot: an invariant often needs a second clause to hold up the first.

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

An exported function's contract is visible to other packages, so verified code can call verified code across package boundaries. A function whose own verification failed cannot be relied on from another package.

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

A predicate takes numbers, slices of numbers, and strings.

```go
//@ Predicate digits(s) ::= Forall k in [0, |s|) : 48 <= s[k] <= 57
```

Its body may mention only its parameters, not constants or variables of the package: pass what it needs.

A predicate may be defined in terms of itself:

```go
//@ Predicate zeros(A, n) ::= n <= 0 Or (zeros(A, n-1) And A[n-1] = 0)
```

In such a definition the predicate may appear under `And`, `Or`, and the quantifiers, and on the right of `->`. It may not appear under `~`, on the left of `->`, or in a `<->`.

Recursive predicates are for facts that a `Forall` cannot state. The prover unfolds them a step at a time and does no induction of its own, so they carry less far than they promise. In particular, a sum or a count over a slice, defined this way, cannot yet be kept as the invariant of a loop that writes the slice. Prefer a `Forall` where one will do.

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

`-vego.max-steps` raises the effort the prover spends on one obligation. It is the last thing to try, not the first: a proof that needs it is slow for everyone who runs the tool after you, and most failures are a missing fact that no amount of effort supplies.

## Changing memory

Everything so far computed values. A function that writes memory its caller can see, such as the elements of a slice, the fields behind a pointer, or a map, has two more things to say: what it may write, and what is there afterwards.

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

**`Modifies` is a permission.** It lists what the function may write. A write to anything else is an error:

```text
vego: A[i] is assigned, which FillUnlisted may not modify; list it in a //@ Modifies clause
```

A caller knows that whatever is not listed is unchanged, and knows nothing about what is listed beyond what the `Ensures` say. So list as little as will do: `Modifies c.n` leaves a caller's knowledge of the other fields of `c` alone, and `Modifies c` does not. An entry that the body does not need is reported, so that a contract does not claim a permission out of caution.

**The prime means "on return".** In an `Ensures` clause, a plain name means the value when the function was called. That matters only for memory the function may change, and for that memory a prime means the state on return: `A'[k]` is element `k` when `Fill` returns, and `A[k]` is the element it had on entry. For a field it is `c.n'` and `c.n`. The prime goes after the name or the field, before any index: `s.items'[0]`.

**Inside a body it is the other way round.** A name in an `Invariant` or an `Assert` means the value now, and `old(x)` means what a parameter was on entry.

A path in `Modifies` is read when the function is called. `Modifies s.items` means the elements of the slice that `s.items` was on entry, also if the function later puts another slice there.

## Slices

A slice parameter is a view of an array that the caller may also see, so a function that writes its elements needs `Modifies A`.

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

A byte of a string is a number in a formula, so a parser's contract speaks of `48 <= s[i] <= 57` where the code says `'0' <= s[i] && s[i] <= '9'`.

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

What an entry covers depends on where its path ends:

- at a pointer, as in `Modifies c`: the fields of the struct it points to;
- at a field that holds a number, a string, or the like, as in `Modifies c.n`: that field;
- at a slice, as in `Modifies A` or `Modifies s.items`: the elements, up to the capacity. It does not cover the field `items` itself;
- at an element, as in `Modifies ps[0]`: that element, when it is a struct. A pointer, a slice, or a map found at the end of a longer path, as in `Modifies s.next` or `Modifies ps[0]` for a slice of pointers, is treated as above: the entry covers what it refers to, and not the field or element that holds it;
- at a map, as in `Modifies m`: the map. `Modifies m[k]` is the struct that the pointer stored under `k` points to.

The fields of a struct do not include the elements of a slice it holds. A method that assigns `s.n` and writes `s.items[i]` needs `Modifies s.n, s.items`.

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

`fresh(x)` says that what `x` refers to on return was created during the call. `within(a, b)` says that `a` lies inside the memory of `b`, where each is a pointer or a slice, and a slice counts with its whole capacity. Two edge cases follow from "memory": a slice with no capacity has no memory, so it is `fresh` and lies `within` anything, and a nil pointer lies within nothing.

`&x`, `&p.field`, and `&s[i]` are supported when they point to a struct, and so are methods with pointer receivers on variables, fields, and elements. A pointer to anything but a struct, such as `*int`, is not supported.

### A slice that grows inside a struct

A stack that appends to its own slice shows all of this at once.

```go
// @ Requires s != nil And s.n = |s.items| And s.n < 1000
// @ Modifies s, s.items
func (s *Stack) Push(x int) {
	s.items = append(s.items, x)
	s.n++
}

//@ Ensures s.n' = s.n + 1 And |s.items'| = s.n' And s.items'[s.n] = x
//@ Ensures fresh(s.items) Or within(s.items', s.items)
```

`Push` assigns the fields `items` and `n`, so it lists `s`. The `append` may write into the capacity of the old slice, so it lists `s.items` too.

The last clause is the one that is easy to miss. After `Push`, `s.items` may be a different slice from the one the caller's `Modifies s.items` named. Without that clause a caller that pushes twice is told that the second `Push` may write memory the caller has no permission for. The clause says where the new slice is: either newly created, which anyone may write, or inside the old one, which the caller had listed.

```go
// @ Requires s != nil And s.n = |s.items| And s.n < 100
// @ Modifies s, s.items
func PushTwo(s *Stack) {
	s.Push(1)
	s.Push(2)
}

//@ Ensures s.n' = s.n + 2
```

Write a clause of this kind on every function that may replace a slice its callers can reach, and make it say where the new slice really comes from. For a function that appends it is the clause above. For one that stores a slice it was given, it is `within(s.items', items)`. In `fresh`, the path is written without a prime and means the slice on return.

### Calls that change memory stand alone

A call to a function with a `Modifies` clause must be a statement of its own, the only returned expression, or the whole right-hand side of an assignment to plain variables or their fields. Take a method that changes the stack and returns a value:

```go
// @ Requires s != nil And s.n > 0
// @ Modifies s.n
func (s *Stack) Pop() int {
	s.n--
	return s.items[s.n]
}

//@ Ensures s.n' = s.n - 1 And result = s.items[s.n-1]
```

These two calls are accepted:

```go
x := s.Pop()
return s.Pop()
```

It is rejected inside a larger expression, as an argument, and in a condition:

```go
if s.Pop() > 0 {
```

```text
vego: cannot verify PopInCondition: Pop may modify s.n, so the call must be a statement
of its own or the whole right-hand side of an assignment to variables
```

Assign the result to a variable first.

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

`Top` may index with `s.n-1` because the invariant bounds `n`. An invariant works like a clause that is added to every contract:

- it may be assumed, on entry, of every parameter and receiver of the type or of a pointer to it;
- it must be proved of them, and of every result of the type, on return;
- it must be proved of every argument at a call, and is known again of what a verified function hands back.

In between, a function may break it and put it right again. There is no way to switch an invariant off for one function; a helper that has to run while the invariant is broken takes the fields it needs instead of the struct.

The invariant reaches less far than "every value of the type" suggests, in three ways.

**It applies to what is passed and returned directly.** It is not assumed, and not checked, of a struct inside a slice, inside a map, inside another struct, or behind a pointer field. Say it yourself where you need it:

```go
// @ Invariant 0 <= balance <= 1000000
type Account struct {
	mu      sync.Mutex
	balance int
}
```

```go
// @ Requires |as| <= 100
// @ Requires Forall k in [0, |as|) : as[k] != nil And 0 <= as[k].balance <= 1000000
func Total(as []*Account) int {
```

**A loop forgets it** along with everything else about what the loop changes. A loop that calls a method on a struct must restate the invariant of the type as its own:

```go
// @ Requires s != nil
// @ Modifies s.n
func Drain(s *Stack) {
	//@ Invariant 0 <= s.n <= |s.items|
	//@ Variant s.n
	for s.n > 0 {
		s.Pop()
	}
}

//@ Ensures s.n' = 0
```

Without that line the report is `invariant of Stack may not hold for what is passed to Pop as s`: `Pop` requires `s.n > 0`, which the loop condition gives, and a stack whose invariant holds, which after one iteration nothing gives any more.

**A trusted function does not restore it.** After a call to a trusted function that may modify a struct, the invariant of the struct is not assumed, since nobody proved it.

## Maps

A map is a reference, like a pointer: two map variables may be the same map, and writing one needs `Modifies`. In a formula, `m[k]` is the value of a key, which is the zero value when the key is absent, as in Go. `has(m, k)` says whether the key is present, and `|m|` is the number of keys.

```go
func Get(m map[string]int, k string) (v int, ok bool) {
	v, ok = m[k]
	return v, ok
}

//@ Ensures ok <-> has(m, k)
//@ Ensures v = m[k]

// @ Requires m != nil And m[k] < 1000
// @ Modifies m
func Bump(m map[string]int, k string) {
	m[k] = m[k] + 1
}

//@ Ensures has(m', k) And m'[k] = m[k] + 1
```

Keys are integers or strings. Writing to a map needs a proof that it is not nil; reading and `delete` do not.

A `range` over a map is limited in two ways. It can check each value but cannot add them up, because the verifier does not know that each key is visited once. And its body must not change a map of the type it ranges over, so the usual loop that deletes some keys is not supported:

```go
for k := range m {
	delete(m, k)
}
```

```text
vego: cannot verify Clear: the loop modifies a map of the type it ranges over, which is not supported
```

Quantifiers range over integers, so a formula can speak of every value of a map with integer keys in a range, and not of every value of a map with string keys.

## Errors

About an error, `vego` knows one thing: whether it is `nil`. `errors.New` and `fmt.Errorf` return an error that is not nil. So does a package-level variable that is declared with one of them and never assigned, the usual `var ErrEmpty = errors.New("empty")`.

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
vego: the contract of HeadWeak may also be met by a function that always returns an
error: no simple input was found for which it forces success; state when it succeeds
with a clause such as "condition -> err = nil", where the condition is about the
inputs and a small input satisfies it
```

A contract of the form "if it succeeds, then..." is met by a function that never succeeds. `vego` rejects such a contract, because it is the easiest way to write a specification that says nothing.

**How it decides.** `vego` looks for one small example input that meets the `Requires` and for which the `Ensures` leave no way to return an error. A function with two error results has to return `nil` for both on that one input. The examples it tries are built from the numbers and strings your contract mentions and a few small ones, slices whose elements are all the same, pointers to structs up to two steps deep, and maps with one key, whose value may be a pointer to a struct. That covers most contracts. If yours says when it succeeds and you still get this message, there are two possible reasons. Success may need an input outside that range: a slice with two different elements, say. Or an example was tried and the prover could not show that it meets the `Requires`, or that the `Ensures` then force success, which happens when one of them takes real arithmetic to check. Either way, add a clause that a simple input plainly satisfies, such as `|A| = 0 -> err = nil`. An `Assert` does not help, since no body is involved. `-vego.max-steps` cannot widen the range of examples, though it does apply to the proofs about each one.

**The exception** is a function whose success depends on a call whose contract does not say what comes back:

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

The contract of `strconv.Atoi` does not say which strings it accepts, so `ParsePort` cannot promise success for any input, and is not asked to. The same goes for anything that reads a file or the network.

**Wrapping.** `fmt.Errorf` may format numbers, booleans, strings, and errors that were made by `errors.New` or `fmt.Errorf` in verified code. It may not format an error that came from a trusted function or in as a parameter, because formatting runs that error's methods, which `vego` cannot see. An error like that cannot be passed to a trusted function either, unless its contract says so. So the commonest line in Go error handling is rejected:

```go
return 0, fmt.Errorf("bad quantity %q: %w", line, err)
```

```text
vego: cannot verify QuantityWrapped: formatting err would run the methods of an error
whose origin is not known; only an error made by errors.New or fmt.Errorf, here or in
a verified function, can be formatted
```

Return the error as it is, or wrap an error of your own:

```go
return 0, fmt.Errorf("bad quantity %q: %w", line, ErrRange)
```

**Which error it is** is not known. Comparing two errors with `==` is rejected. `errors.Is` and `errors.As` are not supported, so no contract can say "returns `ErrEmpty` when the slice is empty". They call the `Is` and `Unwrap` methods of whatever error they are handed, so a trusted contract for them can be given errors from outside only if it lists its parameters under `runs`, and then claims something nobody can check; see [Values that carry code](#values-that-carry-code). Even then nothing is known about the answer. Another package's error variable, such as `io.EOF`, cannot be read.

**A package-level error can lose its standing.** It is known not to be nil only if nothing in its package assigns to it or takes its address, and no code of the package can run before it is set. A package whose variable initialisers call function values or hand things to other packages gives that up, and `vego` says so where the variable is read.

## Defer

A deferred call is verified where it runs: at every return of the function, after the results have their values, last one first.

```go
type Lock struct{ held bool }

// @ Requires l != nil And ~l.held
// @ Modifies l
func (l *Lock) Acquire() {
	l.held = true
}

//@ Ensures l.held'

// @ Requires l != nil And l.held
// @ Modifies l
func (l *Lock) Release() {
	l.held = false
}

//@ Ensures ~l.held'

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

### Locks

`vego` ships no contract for `sync.Mutex`, and you should not write the obvious one. `Lock` blocks for ever on a mutex the goroutine already holds, and `Unlock` crashes on one that is not locked. An entry with no condition on the state of the lock would claim that both always return, and `vego` would then accept a double `Lock` and a stray `Unlock`. There is no portable way to state the condition: a formula could only name the private fields of the mutex, which would tie the contract to one version of Go's implementation.

So keep the locking outside the verified code. The function that locks is ordinary Go, and the work it protects is a verified function:

```go
// Deposit is not verified. It takes the lock, checks what the verified
// part requires, and leaves the arithmetic to it.
func (a *Account) Deposit(n int) bool {
	a.mu.Lock()
	defer a.mu.Unlock()
	if n < 0 || n > 1000000-a.balance {
		return false
	}
	a.deposit(n)
	return true
}

// @ Requires a != nil And 0 <= n And a.balance + n <= 1000000
// @ Modifies a.balance
func (a *Account) deposit(n int) {
	a.balance += n
}

//@ Ensures a.balance' = a.balance + n
```

A struct that verified code works on may hold a mutex. Verified code cannot call `Lock` or `Unlock` and should leave the field alone. What the proof of `deposit` says is that it is correct for one goroutine. That the lock keeps other goroutines out is what `Deposit` is for, and nobody proves it.

## Bits

`vego` computes with whole numbers, so it understands shifts and bitwise operators through arithmetic.

```go
func Pack(hi, lo byte) uint16 {
	return uint16(hi)<<8 | uint16(lo)
}

//@ Ensures result = 256 * hi + lo
```

- `x << k` is `x * 2^k` and must not lose bits. `x >> k` is a division by `2^k` that rounds down, also for a negative `x`. A count that may be negative is an error.
- `x & m` with a constant mask of low bits is the remainder: `x & 0xFF` is `x % 256` when `x` is not negative. For a negative `x` it is the remainder counted upwards, so `-1 & 0xFF` is 255 where `-1 % 256` is -1. With a mask of a single bit, `x & m` is that bit of `x`.
- Of `x & y` in general only bounds are known.
- `x | y`, `x ^ y`, and `x &^ y` are computed from `x & y`, and are known as well as it is. A flag that was just set is known to be set: after `f |= m`, `f & m` is `m`.

These facts are what the prover is given; it does not always get from them to everything that follows. Formulas have no bit operators; write what you mean with `*`, `/`, and `%`.

## Code that is not verified

Verified code has to call code that is not: the standard library, other modules, and functions of your own that use Go `vego` cannot follow. Such a function gets a **trusted contract**, a claim that `vego` uses and does not check.

Trusted contracts live in one file, `vego-trusted.yaml`, next to `go.mod`. There is no way to declare trust in source, so that file holds every contract your project takes on faith.

```yaml
version: 1

trusted:
  example.com/shop/internal/store.load:
    reason: Reads the stock file; reviewed 2026-11-10.
    modifies: []
    ensures:
      - "err = nil -> count >= 0"
```

- **The key** is the function's full name as Go prints it: `sort.Ints`, `example.com/pkg.Func`, `(*bytes.Buffer).Len`.
- **`reason`** is required and says why you believe the contract.
- **`requires` and `ensures`** are lists of formulas. Callers must prove every `requires` and may assume every `ensures`. Quote the formulas, because YAML gives its own meaning to several characters they use.
- **`modifies`** is required, even when it is empty. It lists what the function may write, as a `Modifies` clause would: `[x]` for the elements of slice `x`, `[b]` for the struct that `b` points to, `[b.count]` for one field. Anything not listed is taken to be unchanged.
- **`runs`** is optional. It lists the parameters whose code the function may run: the methods of an error or an interface, or a function, held in them however deep. See [Values that carry code](#values-that-carry-code) below.
- **The names** in all of these are the parameter and result names in the function's own source, the receiver included. For the standard library, `go doc -src bytes.Buffer.Len` shows that the receiver is `b`. Unnamed results are `result`, or `result1`, `result2`.

`vego` ships contracts for a few functions of the standard library: `sort.Ints`, `sort.IntsAreSorted`, `sort.SearchInts`, `strings.Contains`, `strings.HasPrefix`, `strings.HasSuffix`, `strings.Index`, `strings.TrimSpace`, `strings.Repeat`, `strings.ToUpper`, `strings.ToLower`, `unicode/utf8.RuneCountInString`, `strconv.Itoa`, `strconv.Atoi`, `math/rand.Intn`, and `math/rand.Int`. These are the keys to use when you replace one. The contracts themselves are in `vego/trusted/std` in the source of `laas`. An entry of your own for the same function replaces the shipped one.

### Values that carry code

A trusted contract is a claim about the function's own code. An `error`, or a struct with a field that is an interface or a function, brings code of its own: the function may call `err.Error()` or `l.sink(text)`, and that code could write memory your proof reasons about. So `vego` refuses to pass such a value to a trusted function:

```text
vego: cannot verify TellsUnknown: e is passed to tell, which is trusted, and is an error
whose origin is not known; tell could run code through it that nobody has seen. If its
contract holds whatever that code does, list e under runs in the contract
```

There are three ways on.

**Pass an error that verified code made itself**, with `errors.New` or `fmt.Errorf`. Its methods are the standard library's, and nothing from outside is wrapped in it. A package-level error counts as one of these when only plain values and other such errors went into it; `var ErrRead = fmt.Errorf("read: %w", io.EOF)` holds a foreign error and does not.

**Keep the call outside the verified code.** This is the answer for the ordinary case of logging an error that came from somewhere else: the function that is not verified logs it, and the verified function returns it.

**Say in the entry that the function runs what it is given**, with `runs`:

```yaml
  (*example.com/shop/internal/journal.Journal).Append:
    reason: Appends a line through the writer the journal holds. A Journal is
      built only by journal.Open, which gives it an *os.File; reviewed 2026-11-14.
    runs: [j]
    modifies: [j]
```

`runs: [j]` does not check anything, and it does not make the call safe. It widens the claim: the contract is now said to hold for the whole call, whatever value arrives in `j`. That includes that the call writes nothing beyond `modifies`, returns, and does not panic.

`vego` asks for `runs` by the type of the parameter, without knowing what the function does with it. So there are two cases in which the claim can be true. If the function never calls the code it is handed, as a function that only stores an error or reads a number from the struct, the contract does not depend on that code and `runs` costs nothing. If the function does call it, the claim is true only when you know every value that can arrive there and have read its code, as with a struct that one function of your own builds.

It is not true of a function that calls the methods of an `error` which callers you have not verified can fill with anything. Do not add `runs` to make the message go away there: the contract would be false, and every proof that uses it worthless. The trust report prints `runs` so that a reviewer of the trust file sees the wider claim.

### What a trusted contract cannot do

There are three such things:

- **It cannot make a signature acceptable.** A function with a parameter or result of a type `vego` does not support, such as an interface or a function value, cannot be called from verified code even with an entry: `cannot verify Sync: parameter s has unsupported type example.com/shop.Store`. Write a small function of your own around it whose signature uses supported types, and trust that.
- **It cannot sit beside annotations.** A function is verified or trusted, not both. When you get round to verifying a function you trusted, delete its entry.
- **It says nothing it does not say.** Nothing is known about a pointer or slice that a trusted function returns unless the contract says so, for example with `fresh(result)`.

To see everything a project takes on trust, with reasons and the places that rely on it:

```sh
laas -vego.trust ./...
```

A trusted contract that is wrong makes every proof that uses it worthless. Keep them few and weak: claim only what the documentation of the function promises.

## Is the contract any good?

A function can be verified against a contract that says almost nothing. `-vego.audit` looks for that. It tries degenerate implementations against each contract, such as "return zero" or "leave the slice alone", and reports the ones the contract would accept.

```sh
laas -vego -vego.audit ./...
```

```text
vego: specification of Sort has a hole [OBLIVIOUS]: it also accepts an implementation
that fills its slices with 0, 1, 2, ... whatever the input
```

A sort whose contract only says that the output is sorted gets this report, and rightly. A function annotated with `Ensures True` for its safety checks gets one too, which is the reminder that its contract is still to be written.

## Adopting it

### In an existing package

A verified function can call only functions that have contracts, so start where nothing is called and work upwards.

1. **Pick a leaf.** A function that calls nothing, or only functions that `vego` ships contracts for. Pure functions over numbers, slices, and strings are the easiest.
2. **Opt in with `//@ Ensures True`** and run `laas -vego` on the package. What comes back is the safety of the function as it stands: indexes, overflow, nil, termination. Expect to add `Requires` clauses with bounds, loop invariants, and `Variant`s, and expect to find a bug or two.
3. **Write the real contract**, and run `-vego.audit` to see whether it says enough.
4. **Move to the callers.** Each needs the contracts of what it calls. Where a callee is not ready, give it a trusted contract with a reason such as "not verified yet", and delete the entry when it is.
5. **Leave what does not fit.** A function that uses Go outside the subset can often be split: the logic goes into a function over plain data that is verified, and the part with the interface, the closure, or the goroutine stays outside and calls it.

Two things to keep in mind while the package is half verified.

**Nobody checks a `Requires` at run time.** Verified callers prove it; code that is not verified is simply trusted to keep it, and `go build` and `go test` insert no checks. Where data comes in from outside, do the checking in code: a verified function with no `Requires` that tests its input and returns an error, in front of the functions that require it.

```go
func At(A []int, i int) (x int, err error) {
	if i < 0 || i >= len(A) {
		return 0, fmt.Errorf("index %d out of range", i)
	}
	return A[i], nil
}

//@ Ensures err = nil <-> 0 <= i < |A|
//@ Ensures err = nil -> x = A[i]
```

**Package-level variables are not supported**, apart from error sentinels. A function that reads a global has to be handed the value instead.

### For one core component

The steps are the same, with a little design first, because the component has to stay inside the supported Go.

- Keep its data plain: structs, slices, integers, strings, maps with integer or string keys, pointers to structs. Keep interfaces, function values, and arrays out of its types.
- Write the struct invariant first. It is the sentence you would put in the doc comment anyway: "`n` never exceeds the length", "`head` is a valid position".
- Give the constructor `fresh(result)`.
- Give each method the narrowest `Modifies` that works, and, if it may replace a slice, the `fresh ... Or within ...` clause of [A slice that grows inside a struct](#a-slice-that-grows-inside-a-struct).
- State error behaviour with `<->` where you can.

Then run the audit, and write the callers that sit at the boundary so that they establish the preconditions in code.

### In a new module

Put the logic in packages of its own, away from I/O, and write the contract before the body. Gate CI on the verifier from the first commit, so that a change that breaks a proof is never merged. The gate covers annotated functions only: a function without a `//@` line passes silently, whatever it does. If a package is meant to be verified throughout, that every function in it has a contract is a rule for review, or for a check of your own; `vego` does not enforce it. Keep `vego-trusted.yaml` under review like code: every line in it is something the proofs do not cover.

### In CI

```sh
go install github.com/spachava753/laas/cmd/laas@<commit>
laas -vego ./...
```

- **Pin the version.** `laas` has no tagged releases yet, so install a commit, not `@latest`.
- **The exit status is the gate:** 0 when everything annotated is proved, 3 when anything is reported, 1 when the packages could not be loaded.
- **Build `laas` with the Go that the job uses**, as the line above does; see the note on the toolchain in [Running it](#running-it).
- **`-vego.trust` is a report, not a gate.** It exits with 3 when verification had problems, and its use is in review: a change to it is a change to what the proofs assume.
- **Give the job a time limit.** Small functions take well under a second each. Functions with many pointer parameters that may be the same take much longer, and the speed of the tool has not been worked on yet. `-vego.max-steps` bounds the effort on one obligation, not the time of the run.

## When a proof fails

Work through these in order.

1. **Read the message as "not proved".** It names an obligation and a place. Ask first whether the obligation is true there for every input the `Requires` allows. Try the extremes: zero, negative numbers, the largest `int`, an empty slice, `nil`, two arguments that are the same object.
2. **If it is false, you have found a bug**, in the code or in the contract. Fix whichever is wrong. A missing `Requires` is the commonest case.
3. **If it is true and comes after a loop**, the invariant does not say enough. Everything the loop changes is forgotten except what the invariant states, the invariants of struct types included.
4. **If it is true and comes after a call**, the callee's `Ensures` does not say enough. Strengthen it there.
5. **If it is an overflow**, some input needs a bound, or the expression can be rearranged, as with the midpoint.
6. **If it involves two pointers or two slices**, ask whether they may be the same, and say so if they may not.
7. **Otherwise, help the prover.** Put the fact in an `Assert` just before the failure. If the `Assert` is proved and the failure remains, add a smaller step. If the `Assert` is not proved, move it up until it is.

One run often prints several messages for one cause. Fix the first and run again.

A message that starts with `cannot verify` is a different kind. Nothing was attempted, and the text after the function's name says why. There are three sorts:

- **Go that is not supported**, such as `parameter x has unsupported type any`. Rewrite that part, or move it out of the verified function.
- **A missing contract**, as in `it calls helper, which has no contract`. Verify the callee or trust it.
- **A rule about where something may stand**, as in `the call must be a statement of its own`. The message says what to do.

## Messages

The messages you will meet most, with what they mean and what usually fixes them.

| Message | Meaning | Usual fix |
| --- | --- | --- |
| `postcondition may not hold: P` | At this `return`, `P` is not proved. | Steps 1 to 7 above. |
| `precondition of F may not hold: P` | At this call, a `Requires` of `F` is not proved. | Establish it before the call, or require it of your own callers. |
| `index may be out of range` | | A `Requires` or an invariant that bounds the index. |
| `addition may overflow int`, and the like | | Bound the inputs, or rearrange. |
| `loop invariant may not hold on entry` | Not proved before the first iteration; usually false there. | Fix the invariant or what comes before the loop. |
| `loop invariant may not be preserved` | One iteration may break it, or it is too weak to hold itself up. | Add the clause it depends on. |
| `loop variant may not decrease`, `loop variant may be negative` | The `Variant` is not shown to get smaller, or to stay at zero or above. | A different `Variant`, or an invariant that bounds it. |
| `measure may not decrease in recursive call`, `measure may be negative` | The same for a `Measure`. | |
| `x is assigned, which F may not modify; list it in a //@ Modifies clause` | Nothing of that kind is listed. | Add it to `Modifies`. |
| `Modifies lists x, but F never needs to modify it` | The permission is wider than the body. | Remove the entry, or narrow it. |
| `... which F may not modify: nothing its //@ Modifies clauses list is known to cover it` | Something of that kind is listed, but this may be other memory: another element, another struct, or a slice that was replaced since `F` was called. | Say which it is; for a replaced slice, the callee needs `fresh ... Or within ...`. |
| `invariant of T may not hold for what is passed to F as x` | The struct invariant is not proved at the call. | Restore it before the call; in a loop, restate it as a loop invariant. |
| `invariant of T may not hold for x on return` | The same, at the end of the function. | |
| `the contract of F may also be met by a function that always returns an error` | No example input was found on which the contract forces success. | A clause `condition -> err = nil`; see [Errors](#errors). |
| `specification of F has a hole` | From `-vego.audit`: a trivial implementation meets the contract. | Tie the result to the input. |
| `cannot verify F: it calls G, which has no contract` | | Annotate `G`, or add it to the trust file. |
| `cannot verify F: parameter x has unsupported type T` | | Keep `T` out of verified signatures. |
| `cannot verify F: x is not a local variable` | A package-level variable is used. | Pass the value in. |
| `cannot verify F: formatting err would run the methods of an error whose origin is not known` | `fmt.Errorf` is given a foreign error. | Return it as it is, or wrap your own. |
| `nothing can satisfy the Requires clauses of F` | The `Requires` contradict each other or the types, so every proof about `F` would be empty. | Fix the `Requires`. |
| `the slices passed to F as a and b may overlap` | Two slice arguments of one element type are not shown to be different memory. | Pass two slice parameters of your own function, which your callers then have to keep apart, or a slice the function made itself. There is no formula yet for "these two slices share no memory", so a slice held in a struct cannot be shown to be apart from a parameter. |
| `the trusted contract of F cannot be true of this call` | What the entry promises contradicts what is known at the call. | The entry is wrong, or needs a `requires`. |
| `x is passed to F, which is trusted, and is an error whose origin is not known`, or `a value of type T, which can hold an error, an interface, or a function` | `F` could run code that came with `x`. | Pass an error made in verified code, or list the parameter under `runs` in the entry for `F`. |
| `the trusted contract ... cannot be used` | An entry of the trust file is wrong; the text says how. | Fix the entry; check the parameter names. |
| `analysis skipped due to errors in package` | The package does not compile, or the toolchain does not match. | See [Running it](#running-it). |

## What is not supported

A function that uses any of these is reported as `cannot verify`:

- interfaces other than `error`, calls through them, type switches, and type assertions;
- function values, method values, and closures, including `defer func() { ... }()`;
- generic functions and types;
- goroutines, channels, and `select`;
- arrays, and any struct that holds one;
- pointers to anything but a struct;
- package-level variables, other than error sentinels;
- calls to variadic functions other than `fmt.Errorf`, `append(s, t...)`, and `copy`;
- a call that modifies memory inside a condition or a larger expression, as in `if !s.Push(x)`; see [Calls that change memory stand alone](#calls-that-change-memory-stand-alone);
- comparing structs or errors with `==`, `errors.Is` and `errors.As`, and reading another package's error variable such as `io.EOF`;
- a `range` over a map whose body changes a map of that type;
- `goto`, `fallthrough`, labelled `break` and `continue`, and `defer` inside a loop.

Floats are allowed but opaque: they can be passed around and computed with, and nothing can be said or proved about their values.

## What a proof assumes

A proof by `vego` is a proof under these assumptions. They are about things it cannot see.

- **Trusted contracts are true**, the shipped ones and your own, and for a parameter listed under `runs` they are true whatever code arrives in it. The functions behind them return without panicking when their `requires` hold, write nothing a caller can see beyond their `modifies`, do not keep the pointers and slices they are given, and do not call back into the verified function that called them by way of another package.
- **Callers that are not verified keep the contract**: they establish the `Requires`, hand over structs whose invariants hold, and do not pass overlapping slices where two slice parameters have one element type.
- **Code that is not verified keeps Go's types**: no `unsafe`, `reflect`, or cgo that makes one piece of memory two types or changes a string.
- **No other goroutine writes the memory a verified function reads or writes while it runs.** A proof is about one goroutine.
- **Exported error variables are not reassigned** by packages `laas` does not see.
- **The platform is the one `laas` ran for.** A proof for a 64-bit target is not a proof for a 32-bit one.
- **The machine has the memory and the stack.**
- **Annotations mean what you think.** A formula is not checked for an index out of range or a division by zero inside it; see [Formulas](#formulas).

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
| `Invariant P` | doc comment of a struct type | Holds of every parameter, receiver, and result of the type at function boundaries. |
| `Predicate name(x, y) ::= P` | top level | Names a formula over its parameters. |

### Formulas

| Form | Meaning |
| --- | --- |
| `~P`, `P And Q`, `P Or Q` | not, and, or; tightest first |
| `P -> Q`, `P <-> Q` | implies, exactly when; loosest |
| `True`, `False` | |
| `=`, `!=`, `<`, `<=`, `>`, `>=` | comparisons; they chain: `0 <= i < n` |
| `+`, `-`, `*`, `/`, `%` | on mathematical integers; `/` and `%` round as in Go |
| `MaxInt`, `MinInt`, `MaxInt8` ... `MaxUint64` | limits of the Go types |
| `MaxAlloc` | most bytes one allocation can have |
| <code>&#124;A&#124;</code>, `len(A)` | length of a slice or string, number of keys of a map |
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
| `Ensures` | value on entry | `A'`, `c.f'`, `s.items'[0]`: on return |
| `Invariant`, `Assert` in a body | value now | `old(x)`: on entry |
| results | `result`, or `result1`, `result2`, or their own names | |

### Memory

| Form | Meaning |
| --- | --- |
| `Modifies p` | every field of the struct `p` points to |
| `Modifies p.n` | the field `n`, when it holds a number, a boolean, a string, or a struct |
| `Modifies p.f`, `Modifies ps[0]` | when the path ends at a pointer, a slice, or a map: what that refers to, by the three rows around this one, and not the field or element that holds it |
| `Modifies A`, `Modifies s.items` | the elements of a slice, up to its capacity |
| `Modifies ps[0]` | one element of a slice of structs |
| `Modifies m` | a map |
| `Modifies m[k]` | the struct that the pointer under key `k` points to |
| `fresh(x)` | what `x` refers to on return was created by the call; true of a slice with no capacity |
| `within(a, b)` | `a` lies inside the memory of `b`; each is a slice, with its capacity, or a pointer |

### Flags

| Flag | Effect |
| --- | --- |
| `-vego` | run only the verifier |
| `-vego.audit` | also report contracts that degenerate implementations satisfy |
| `-vego.max-steps=n` | effort the prover spends on one obligation |
| `-vego.trusted=path` | the trust file, instead of the one next to `go.mod` |
| `-vego.trust` | print what the proofs take on trust |
| `-test=false` | leave out test files |
| `-exclude-packages=regexp` | skip packages by import path |
