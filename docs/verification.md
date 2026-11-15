# Writing verified Go

## Introduction

`vego` proves things about Go functions. You say what a function must do in comments that start with `//@`, and `vego` either proves that the function does it for every input, or tells you what it could not prove. The comments do not change the program. It compiles and runs exactly as before.

This guide shows how to write Go that `vego` can verify. Read it from top to bottom the first time. After that, two sections work as a reference: [Messages](#messages) explains what the tool prints, and the [Summary](#summary) lists every annotation and formula form. The examples are run by the tests of `vego`. Their source is in `vego/testdata/src/guide`.

`vego` works best on self-contained logic such as index arithmetic, parsers, encoders, data structures, and validation. For each verified function it proves that:

- the function does not panic;
- no integer overflows;
- every loop and every recursion terminates;
- the function meets its contract;
- the function writes only the memory it declares.

`vego` never reports a function as correct when it is not. If it cannot handle a piece of Go, it reports `cannot verify` and names the construct. If it cannot find a proof, it reports `may not hold`. That means "not proved". The code may be wrong, the contract may be wrong, or both may be right and the prover needs a hint. Much of this guide is about working out which.

`vego` is experimental and supports only part of Go. It does not yet support interfaces other than `error`, closures, generics, goroutines, arrays, or package-level variables. [What is not supported](#what-is-not-supported) has the full list. Code that does I/O usually runs into these limits. The usual approach is to verify the logic and leave the code around it unverified. [Adopting it](#adopting-it) describes how.

## Running it

`vego` is one of the analyzers in the `laas` command.

```sh
go install github.com/spachava753/laas/cmd/laas@latest
laas -vego ./...
```

`laas -vego` runs only the verifier. Plain `laas` also runs the other analyzers, which report on things unrelated to verification. The arguments are package patterns, as for `go vet`. Use `./...` for everything or `./internal/core` for one package.

`vego` verifies a function only if it has at least one `//@` annotation. It ignores every other function, so you can start with a single function in a large package. To turn on [the built-in checks](#built-in-checks) without writing a contract, add `//@ Ensures True`.

When every annotated function is proved, `laas` prints nothing and exits with status 0. It does not list what it verified. It exits with status 3 if it has anything to report, and with status 1 if it could not load the packages.

Some details:

- Build `laas` with the same Go you run it with. The `go` command that `laas` finds at run time must not be newer than the Go that built `laas`. If it is, you get errors about the standard library and `analysis skipped`. These are not failed proofs. Rebuild `laas`, or set `GOTOOLCHAIN` to the version that built it.
- A package that does not compile is skipped. The message is `vego: analysis skipped due to errors in package`.
- Test files are included. Pass `-test=false` to leave them out.
- `-exclude-packages` takes a regular expression and skips the import paths that match.
- Run `laas` directly. It refuses to verify under `go vet -vettool`, because the `go vet` cache does not know about the trust file and could return a stale result.

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

An `Ensures` clause states what is true when the function returns. `result` is the returned value. Running `laas -vego` on this file prints nothing, so both clauses are proved for every `a` and `b`.

Now change the function to return `b` on both branches. `vego` reports:

```text
vego: postcondition may not hold: result >= a
```

The message points at the `return` statement and names the part of the contract that fails there. Clauses joined with `And` are checked separately, so the message names only the failing part.

The next function looks correct but is not.

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

The smallest `int` has no positive counterpart. Negating it overflows, and `Abs` returns a negative number. `vego` reports this because it checks every arithmetic operation in a verified function for overflow. Nothing in the contract asked for that check.

The fix is to exclude that input:

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

A `Requires` clause states what must be true when the function is called. The function body may assume it. Every verified caller must prove it.

Together, `Requires` and `Ensures` are the function's contract. Working with `vego` means writing a contract, reading what `vego` could not prove, and then fixing either the code or the contract.

## Annotations

An annotation is a `//` comment that starts with `@` and a keyword. There are eight keywords. Each is allowed only in certain places.

| Keyword | Where it goes |
| --- | --- |
| `Requires`, `Modifies`, `Measure` | the doc comment of a function |
| `Ensures` | the doc comment of a function, or after its closing brace |
| `Invariant`, `Variant` | directly above a loop |
| `Assert` | anywhere in a function body, on its own line |
| `Invariant` | the doc comment of a struct type |
| `Predicate` | the top level of a file |

This guide puts `Requires` above the function and `Ensures` below it.

You can write `//@` or `// @`. `gofmt` rewrites the first form to the second inside doc comments, so formatted code contains both. To continue a long annotation, start the next line with `//@` and no keyword. A `//` inside an annotation starts an ordinary comment.

A misspelt annotation is an error. `//@ Ensure`, `//@ensures`, and an annotation inside `/* */` are all reported, not skipped.

## Formulas

The text after a keyword is a formula. Formulas look like Go conditions, with these differences.

The logical operators are `And`, `Or`, `~` (not), `->` (implies), and `<->` (if and only if). Equality is a single `=`. Comparisons can be chained, so `0 <= i < n` is valid.

```go
//@ Ensures result = -1 Or (0 <= result < |A| And A[result] = x)
```

`~` binds tightest, followed by `And`, `Or`, `->`, and `<->`. `a -> b -> c` means `a -> (b -> c)`. Use parentheses if you are unsure.

Numbers in formulas are mathematical integers. They do not overflow, so `x + 1` is always one more than `x`, whatever the type of `x`. `/` and `%` round as they do in Go. The limits of the Go integer types have names: `MaxInt`, `MinInt`, `MaxInt8` to `MaxInt64`, `MinInt8` to `MinInt64`, and `MaxUint` to `MaxUint64`.

`|A|` is the length of a slice or string, or the number of keys in a map. `len(A)` means the same. `A[i]` is an element. Fields are written with a dot, including through pointers: `c.count`, `s.items[i]`, `|s.items|`.

Formulas can also use strings and `nil`: `role = "admin"`, `p != nil`, `err = nil`.

### Quantifiers

`Forall` and `Exists` range over an interval of integers.

```go
//@ Requires Forall k in [0, |A|) : 0 <= A[k] <= 1000
//@ Ensures Exists k in [0, |A|) : A[k] = result
```

Intervals use mathematical notation. `[0, n)` includes 0 and excludes `n`. `[0, n]` includes both. Several variables can share an interval, as in `Forall i, j in [0, n) : ...`. `in Z` ranges over all integers.

The body of a quantifier extends to the end of the clause. To end it earlier, put the whole quantifier in parentheses.

There is a short form for a condition on a range of elements. `A[lo:hi) <= x` means that every element from index `lo` up to, but not including, `hi` is at most `x`. Any comparison operator can be used.

### Names

A contract can use the function's parameters and results, and the integer and boolean constants of the package. String constants cannot be used by name. Write the string itself.

A single unnamed result is called `result`. Several unnamed results are called `result1`, `result2`, and so on. Named results keep their names.

### Limits

Formulas have no bit operators, no `cap`, and no floating-point facts. They cannot call functions, only predicates. They have no character literals, so write `48` for `'0'`. A slice cannot be compared with `nil`. Use `|A| = 0`. Structs cannot be compared as a whole. Compare their fields.

`vego` does not check that a formula is well defined. `A[i]` in a formula can be out of range, and `x / y` can divide by zero. Such an expression has an unknown value. A clause that uses it usually cannot be proved, but it can also be trivially true and pass, as `A[999] = A[999]` does. Guard such expressions as you would in code: `0 <= i < |A| And A[i] = x`.

## Built-in checks

Every verified function gets the checks in this section. They do not depend on the contract.

### Index bounds

Every index must be proved to be in range.

```go
func First(A []int) int {
	return A[0]
}

//@ Ensures result = A[0]
```

```text
vego: index may be out of range
```

Adding `// @ Requires |A| > 0` fixes it. Every verified caller of `First` must then prove that its slice is not empty.

### Nil pointers and division

A pointer must be proved non-nil wherever it is dereferenced. For a parameter or receiver, this usually means adding `Requires p != nil`.

A divisor must be proved non-zero.

### Overflow

Every `+`, `-`, `*`, `/`, negation, conversion, and left shift must be proved to stay within its type.

```go
// @ Requires 0 <= lo <= hi
func Mid(lo, hi int) int {
	return (lo + hi) / 2
}
```

```text
vego: addition may overflow int
```

`lo + hi` can exceed the largest `int` even though the midpoint cannot. `lo + (hi-lo)/2` verifies.

Overflow is the check you will see most often. Code that adds up values can only be proved if the values are bounded, so contracts often need bounds on their inputs:

```go
// @ Requires |A| <= 1000
// @ Requires Forall k in [0, |A|) : 0 <= A[k] <= 1000
func Sum(A []int) int {
```

These bounds are part of the function's real contract. Without them the function is wrong for some inputs.

Code that overflows on purpose, such as a hash function, cannot be verified. Neither can a conversion that drops bits. `byte(x)` is an error unless `x` is known to fit in a byte. `byte(x & 0xFF)` is accepted.

### Allocation, panics, and termination

`make`, an `append` that grows the slice, and string concatenation must be proved to stay under the largest allocation the platform allows. This usually means bounding sizes.

A reachable call to `panic` is an error.

Every loop and every recursive function must be proved to terminate. The next two sections explain how.

### Checking safety only

To get these checks without stating anything else, use a contract that is always true:

```go
func SafeOnly(A []int, i int) int {
	if 0 <= i && i < len(A) {
		return A[i]
	}
	return 0
}

//@ Ensures True
```

This is a good first step when you add `vego` to existing code.

## Loops

`vego` does not execute a loop. It reasons about a single, arbitrary iteration. To do that it needs a loop invariant: a formula that is true every time the loop is about to test its condition.

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

`vego` checks two things about an invariant. It must be true when the loop is first reached. And if it is true before an iteration, it must be true after it.

After the loop, `vego` knows the invariant and that the loop condition is false. Here that gives `n = d*q + r`, `0 <= r`, and `r < d`, which is the postcondition.

**After a loop, `vego` knows nothing about the variables the loop changed except what the invariant states.** If a proof fails in the code after a loop, the invariant is usually missing a fact.

A `Variant` proves that a `for` loop terminates. It is an integer expression that is never negative while the loop runs and that decreases on every iteration. Every `for` loop needs one.

A `range` loop needs no `Variant`. `vego` also knows the bounds of its index variable.

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

The invariant bounds `total` after `i` elements. That bound lets `total += A[i]` pass the overflow check. When the loop ends, `i` equals `|A|`, and the invariant becomes the postcondition.

This invariant refers to the index, so the loop must name it. With `for _, x := range A` there is no name to use. Write `for i := range A` and read `A[i]`.

When a loop processes a slice one element at a time, the invariant usually states that the part processed so far is correct:

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

A common way to find an invariant is to take the postcondition and replace the upper bound with the loop index. Above, `[0, |A|)` in the postcondition became `[0, i)` in the invariant.

`break`, `continue`, and `return` work inside loops. A `return` inside a loop must establish the postcondition using only the invariant and the conditions on the path to the `return`.

There are two messages about invariants:

- `loop invariant may not hold on entry` means the invariant was not proved before the first iteration. Usually it is false at that point. Sometimes the prover needs help.
- `loop invariant may not be preserved` means `vego` could not prove that an iteration keeps the invariant true. Either an iteration really can break it, or the invariant is too weak. A weak invariant is fixed by adding a second clause that the first one depends on.

## Recursion

A recursive function needs a `Measure` to prove that it terminates. A measure is an integer expression over the parameters. It must never be negative, and it must be smaller at every recursive call. Functions that call each other each need one.

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

At the recursive call, `vego` uses the contract of `Steps` with `n-1` as the argument. It does not look at the body. All calls work this way.

## Calls

`vego` verifies a call using only the contract of the called function. It never looks at the callee's body.

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

At the call, `Percent` must prove the precondition `0 <= 100`. After the call it knows `0 <= result <= 100` and nothing else. It does not know that `Clamp` returns `x` unchanged when `x` is already in range, because the contract of `Clamp` does not say so. If a caller needs a fact about a function, add it to that function's `Ensures`.

Each function is therefore proved once, on its own. The cost is that a function with a weak contract causes proof failures in its callers, not in itself.

A function without a contract cannot be called from verified code:

```text
vego: cannot verify CallsHelper: it calls helper, which has no contract; annotate
helper with //@ so that it is verified, or add a trusted contract for guide.helper
to vego-trusted.yaml
```

Either verify the helper, or give it a trusted contract as described in [Code that is not verified](#code-that-is-not-verified).

The contract of an exported function is available to other packages, so verified code can call verified functions in other packages. If a function failed verification, other packages cannot rely on its contract.

## Predicates

A predicate gives a name to a formula so that you can reuse it.

```go
//@ Predicate sorted(A) ::= Forall i, j in [0, |A|) : i <= j -> A[i] <= A[j]

// @ Requires sorted(A) And |A| > 0
func Smallest(A []int) int {
	return A[0]
}

//@ Ensures Forall k in [0, |A|) : result <= A[k]
```

The parameters of a predicate can be numbers, slices of numbers, or strings.

```go
//@ Predicate digits(s) ::= Forall k in [0, |s|) : 48 <= s[k] <= 57
```

The body of a predicate can refer only to its parameters. It cannot use the constants or variables of the package, so pass them as arguments.

A predicate can be recursive:

```go
//@ Predicate zeros(A, n) ::= n <= 0 Or (zeros(A, n-1) And A[n-1] = 0)
```

In its own definition, a predicate may appear under `And`, `Or`, and quantifiers, and on the right side of `->`. It may not appear under `~`, on the left side of `->`, or inside `<->`.

Use a recursive predicate only for a property that `Forall` cannot express. The prover expands the definition one step at a time and does not do induction, so recursive predicates are hard to prove things with. For example, a sum or count over a slice cannot currently be kept as the invariant of a loop that writes to that slice.

## Helping the prover

The prover is sound but limited. It handles linear arithmetic, reads and writes of slices, and `Forall` facts that apply to a term in the proof. It has some support for products of two variables. When it fails to prove something true, the fix is usually to state an intermediate fact.

`Assert` states such a fact. `vego` must prove the assertion at that point, and can use it in everything that follows.

```go
//@ Assert lo < |A|
```

`Assert` is also the way to find out what `vego` knows at a given point. Assert the fact you believe, and if it fails, move the assertion earlier in the function until it is proved. The fact is lost between the last place where it is proved and the first place where it is not. Often that is a loop whose invariant does not mention it.

This example needs no help, although it multiplies two variables:

```go
// @ Requires 0 <= i < h And 0 <= j < w And h <= 1000 And w <= 1000
func Cell(i, j, w, h int) int {
	return i*w + j
}

//@ Ensures 0 <= result < h*w
```

`-vego.max-steps` raises the limit on how much work the prover does for one proof obligation. Try it last. Most failures are caused by a missing fact, which more effort cannot supply, and a higher limit makes every later run slower.

## Changing memory

The functions so far only computed values. A function can also write memory that its caller can see: the elements of a slice, the fields of a struct behind a pointer, or a map. Such a function must declare what it writes and describe the result.

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

### Modifies

`Modifies` lists the memory a function is allowed to write. Writing anything else is an error:

```text
vego: A[i] is assigned, which FillUnlisted may not modify; list it in a //@ Modifies clause
```

A caller can rely on everything outside the list being unchanged. About the memory in the list, it knows only what the `Ensures` clauses state. So keep the list as small as possible. With `Modifies c.n`, callers keep what they know about the other fields of `c`. With `Modifies c`, they lose it.

`vego` also reports a `Modifies` entry that the function body never needs.

A `Modifies` path is evaluated when the function is called. `Modifies s.items` refers to the slice that `s.items` held at that moment, even if the function later stores a different slice in the field.

### Before and after

In an `Ensures` clause, a name refers to the value at the time of the call. To refer to memory as it is when the function returns, add a prime. In the example, `A'[k]` is element `k` on return and `A[k]` is the element at the time of the call. For a field, write `c.n'`. The prime comes after the name or field and before any index: `s.items'[0]`.

The prime is only needed for memory that the function can change. A parameter that is a plain value, such as `v`, never takes one.

Inside a function body the convention is reversed. In an `Invariant` or `Assert`, a name refers to the current value. `old(x)` refers to the value of a parameter at the time of the call.

## Slices

A slice parameter shares its array with the caller. A function that writes the elements must list the slice in `Modifies`.

Two rules reduce the annotations that slices need.

First, slice parameters with the same element type do not overlap. A function can assume that two `[]int` parameters refer to different memory, and every verified call must prove it. A call such as `Copy(A, A[1:])` is rejected.

Second, `Modifies A` covers the whole capacity of `A`, not just its length. This is necessary because `append` can write past the length.

`append` is supported as the entire right-hand side of an assignment, or as the returned expression.

```go
// @ Requires |A| < 1000
// @ Modifies A
func Push(A []int, x int) []int {
	return append(A, x)
}

//@ Ensures |result| = |A| + 1 And result[|A|] = x
```

`append` does one of two things. If there is spare capacity, it writes into the existing array, and other slices of that array see the write. Otherwise it allocates a new array. `vego` verifies both cases unless it can prove that one cannot happen. `Push` therefore needs `Modifies A` for the first case and a bound on the length for the second.

Slice expressions `A[i:j]` and `A[i:j:k]`, `len`, `cap`, `make`, and slice literals are supported. `copy` and `append(s, t...)` are not supported yet.

## Strings

A string is an immutable sequence of bytes. `vego` supports `|s|`, `s[i]`, `==`, string literals, concatenation, substrings, and conversion to and from `[]byte`.

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

In a formula, a byte of a string is a number. Where the code tests `'0' <= s[i] && s[i] <= '9'`, the contract says `48 <= s[i] <= 57`.

`vego` does not know how strings are ordered by `<`. A `range` over a string produces an unknown rune at each step and advances by one to four bytes.

## Structs and pointers

Struct fields are read and written as in Go. Contracts refer to them with a dot.

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

A `Modifies` path starts at a parameter. `Modifies c` covers every field of the struct that `c` points to. `Modifies c.n` covers one field, so callers know that `c.limit` is unchanged:

```go
// @ Requires c != nil And c.n = 0 And c.limit = 10
// @ Modifies c.n
func Twice(c *Counter) {
	c.Inc()
	c.Inc()
}

//@ Ensures c.n' = 2 And c.limit' = 10
```

What a `Modifies` entry covers depends on the type at the end of its path.

| The path ends at | Example | The entry covers |
| --- | --- | --- |
| a pointer | `Modifies c` | the fields of the struct it points to |
| a number, boolean, string, or struct | `Modifies c.n`, `Modifies ps[0]` | that field or element |
| a slice | `Modifies A`, `Modifies s.items` | the elements, up to the capacity |
| a map | `Modifies m` | the map |

The first, third, and fourth rows apply wherever the path ends. `Modifies s.items` covers the elements of the slice and not the field `items`. In the same way, `Modifies s.next` for a pointer field covers the struct that `next` points to, and `Modifies m[k]` for a map of pointers covers the struct that the pointer stored under `k` points to.

To assign a field that holds a slice, pointer, or map, list the struct that contains it. A method that assigns `s.n` and writes `s.items[i]` needs `Modifies s.n, s.items`. A method that assigns `s.items` needs `Modifies s`.

### Aliasing

Two pointers can point to the same struct. `vego` does not assume that they are different, so a proof must hold in both cases.

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

If `a` and `b` are the same counter, the function returns 2. Decide whether the function should support that case. If it should, the contract is wrong. If it should not, add `And a != b` to the `Requires` clause, and the function verifies.

Pointers can also point into other memory. A `*Point` can point at an element of a `[]Point` or at a field of a larger struct. To rule that out, write `~within(p, ps)`.

### Newly allocated memory

A function can freely write memory that it allocated itself with `&T{...}`, `new`, `make`, or a literal. It can also write its own local variables.

To tell callers that a result is newly allocated, use `fresh`:

```go
func NewCounter(limit int) *Counter {
	return &Counter{limit: limit}
}

//@ Ensures fresh(result) And result.n = 0 And result.limit = limit
```

Without `fresh(result)`, a caller must assume that the result could be a counter it already has.

`fresh(x)` means that the memory `x` refers to on return was allocated during the call. `within(a, b)` means that `a` lies inside the memory of `b`. Each argument is a pointer or a slice, and a slice includes its whole capacity. There are two edge cases. A slice with zero capacity has no memory, so it is `fresh` and is `within` anything. A nil pointer is `within` nothing.

`&x`, `&p.field`, and `&s[i]` are supported when the result points to a struct. Methods with pointer receivers can be called on variables, fields, and elements. Pointers to other types, such as `*int`, are not supported.

### A slice that grows inside a struct

A stack that appends to its own slice needs most of the features above.

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

`Push` assigns the fields `items` and `n`, so it lists `s`. The `append` can write into the capacity of the old slice, so it also lists `s.items`.

The last clause is easy to forget. After `Push` returns, `s.items` can be a different slice from the one the caller listed in its own `Modifies s.items`. Without the clause, a caller that calls `Push` twice gets an error at the second call, because that call may write memory the caller is not allowed to modify. The clause tells the caller where the new slice is. Either it is newly allocated, and anyone may write it, or it lies inside the old slice, which the caller listed.

```go
// @ Requires s != nil And s.n = |s.items| And s.n < 100
// @ Modifies s, s.items
func PushTwo(s *Stack) {
	s.Push(1)
	s.Push(2)
}

//@ Ensures s.n' = s.n + 2
```

Any function that can replace a slice that its callers can reach needs a clause like this. The clause must describe where the new slice actually comes from. For a function that appends, use the clause above. For a function that stores a slice it was given, use `within(s.items', items)`.

Note that the path inside `fresh` is written without a prime, even though it refers to the slice on return.

### Where a modifying call can appear

A call to a function that has a `Modifies` clause is allowed in three places:

- as a statement on its own;
- as the only expression in a `return`;
- as the entire right-hand side of an assignment to variables or their fields.

Consider a method that changes the stack and also returns a value:

```go
// @ Requires s != nil And s.n > 0
// @ Modifies s.n
func (s *Stack) Pop() int {
	s.n--
	return s.items[s.n]
}

//@ Ensures s.n' = s.n - 1 And result = s.items[s.n-1]
```

These calls are accepted:

```go
x := s.Pop()
return s.Pop()
```

A call inside a larger expression, as an argument, or in a condition is rejected:

```go
if s.Pop() > 0 {
```

```text
vego: cannot verify PopInCondition: Pop may modify s.n, so the call must be a statement
of its own or the whole right-hand side of an assignment to variables
```

Assign the result to a variable first.

## Invariants of structs

A struct type can have an invariant: a formula that every value of the type should satisfy.

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

`Top` can index with `s.n-1` because the invariant bounds `n`.

A struct invariant acts as an extra clause in every contract that involves the type:

- On entry, a function can assume it for every parameter and receiver of the type, or of a pointer to the type.
- On return, the function must prove it for those parameters and for every result of the type.
- At a call, the caller must prove it for every argument. After a call to a verified function, the caller can assume it again for the arguments and results.

Between those points, a function can break the invariant temporarily. An invariant cannot be turned off for a single function. If a helper has to run while the invariant is broken, pass it the fields it needs and not the struct.

The invariant applies in fewer places than you might expect. There are three limits.

### It applies only to direct parameters and results

`vego` does not assume or check the invariant for a struct inside a slice, a map, or another struct, or for one behind a pointer field. State it explicitly where you need it. For example, take this type:

```go
// @ Invariant 0 <= balance <= 1000000
type Account struct {
	mu      sync.Mutex
	balance int
}
```

A function that takes a slice of accounts must state the bound for each element:

```go
// @ Requires |as| <= 100
// @ Requires Forall k in [0, |as|) : as[k] != nil And 0 <= as[k].balance <= 1000000
func Total(as []*Account) int {
```

### A loop does not keep it

A loop forgets the struct invariant along with everything else about the memory it changes. If a loop calls a method on a struct, repeat the struct invariant as a loop invariant:

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

Without the `Invariant` line, `vego` reports `invariant of Stack may not hold for what is passed to Pop as s`. The call to `Pop` needs the invariant of `Stack` to hold. After the first iteration, nothing establishes it.

### A trusted function does not restore it

After a call to a trusted function that may modify a struct, `vego` does not assume the invariant of that struct, because nothing proved it.

## Maps

A map is a reference, like a pointer. Two map variables can refer to the same map, and a function that writes a map must list it in `Modifies`.

In a formula, `m[k]` is the value stored under `k`, or the zero value if the key is absent, as in Go. `has(m, k)` is true if the key is present. `|m|` is the number of keys.

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

Keys must be integers or strings. Writing to a map requires a proof that the map is not nil. Reading from a map and calling `delete` do not.

A `range` loop over a map has two limits. The first is that it can check every value but cannot add the values up, because `vego` does not know that each key is visited exactly once. The second is that the loop body must not modify any map of the same type. The common loop that deletes entries is therefore not supported:

```go
for k := range m {
	delete(m, k)
}
```

```text
vego: cannot verify Clear: the loop modifies a map of the type it ranges over, which is not supported
```

Quantifiers range over integers. A formula can therefore describe all the values of a map with integer keys in some range, but not all the values of a map with string keys.

## Errors

`vego` knows only one thing about an error value: whether it is `nil`. It knows that `errors.New` and `fmt.Errorf` return non-nil errors. It also knows that a package-level variable is non-nil if it is initialised with one of them and never assigned again, as in `var ErrEmpty = errors.New("empty")`.

### Saying when a function succeeds

A function that returns an error must state when it succeeds.

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

The second clause alone is not enough:

```text
vego: the contract of HeadWeak may also be met by a function that always returns an
error: no simple input was found for which it forces success; state when it succeeds
with a clause such as "condition -> err = nil", where the condition is about the
inputs and a small input satisfies it
```

A contract that only says "if the function succeeds, then ..." is also satisfied by a function that always fails. `vego` rejects such contracts because they are easy to write by accident and guarantee nothing.

To decide, `vego` searches for one small example input. The input must satisfy the `Requires` clauses, and the `Ensures` clauses must then force every error result to be `nil`. `vego` builds the examples from:

- the numbers and strings in the contract, plus a few small values;
- slices in which every element is the same;
- pointers to structs, followed at most two levels deep;
- maps with a single key, whose value can be a pointer to a struct.

This is enough for most contracts. If your contract does state when the function succeeds and you still get the message, there are two possible causes. Either every succeeding input lies outside what the search builds, for example because success needs a slice with two different elements. Or the search tried a suitable input, and the prover could not show that it satisfies the `Requires` clauses or that the `Ensures` clauses force success. That can happen when the clauses involve non-trivial arithmetic.

In both cases, add a clause that some simple input clearly satisfies, such as `|A| = 0 -> err = nil`. An `Assert` cannot help, because this check does not involve the function body. `-vego.max-steps` does not widen the search. It only affects the proofs about each example.

### Functions that cannot promise success

Some functions cannot say when they succeed, because their success depends on a call whose contract does not say what it returns.

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

The contract of `strconv.Atoi` does not say which strings it accepts. `ParsePort` therefore cannot promise success for any input, and `vego` does not require it to. The same applies to functions that read a file or use the network.

### Wrapping errors

`fmt.Errorf` can format numbers, booleans, and strings. It can also format errors that verified code created with `errors.New` or `fmt.Errorf`.

It cannot format an error that came from a trusted function or from a parameter. Formatting an error calls its methods, and `vego` cannot see what the methods of an unknown error do. For the same reason, such an error cannot be passed to a trusted function unless that function's contract allows it. See [Arguments that carry code](#arguments-that-carry-code).

As a result, this very common line is rejected when `err` came from a trusted function:

```go
return 0, fmt.Errorf("bad quantity %q: %w", line, err)
```

```text
vego: cannot verify QuantityWrapped: formatting err would run the methods of an error
whose origin is not known; only an error made by errors.New or fmt.Errorf, here or in
a verified function, can be formatted
```

Return the error unchanged, or wrap an error of your own:

```go
return 0, fmt.Errorf("bad quantity %q: %w", line, ErrRange)
```

### Other limits

`vego` does not know which error a value is. Two errors cannot be compared with `==`. `errors.Is` and `errors.As` are not supported, so a contract cannot say "returns `ErrEmpty` when the slice is empty". An error variable from another package, such as `io.EOF`, cannot be read.

A package-level error is known to be non-nil only under these conditions. Nothing in its package assigns to it or takes its address. And no code in the package can run before the variable is initialised. A package loses this knowledge if its variable initialisers call function values or pass values of the package to other packages. `vego` then reports an error where the variable is read.

## Defer

`vego` verifies a deferred call at the point where it runs. That is at every `return` of the function, after the results have been set. Deferred calls run in reverse order.

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

`Guarded` returns in two places. At each one, `vego` proves the `Requires` clause of `Release` and then applies its effect. As in Go, the receiver and arguments of a deferred call are evaluated at the `defer` statement.

Only a call to a named function or method can be deferred. `defer` inside a loop and `defer func() { ... }()` are not supported yet.

### Locks

`vego` has no contract for `sync.Mutex`, and you should not write a trusted one. `Lock` blocks forever if the goroutine already holds the mutex. `Unlock` crashes the program if the mutex is not locked. A contract without a condition on the lock's state would claim that both calls always return, and `vego` would then accept a double `Lock` or an `Unlock` without a `Lock`. The condition cannot be stated in a portable way. A formula could only refer to the private fields of the mutex, which would tie the contract to one version of Go.

Keep locking outside the verified code instead. An unverified function takes the lock and calls a verified function to do the work:

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

A struct used by verified code can contain a mutex. Verified code cannot call `Lock` or `Unlock`, and should not touch the field.

The proof of `deposit` shows that it is correct when one goroutine runs it. Keeping other goroutines out is the job of `Deposit`, and that part is not proved.

## Bits

`vego` computes with integers, not bits. It handles shifts and bitwise operators by translating them to arithmetic.

```go
func Pack(hi, lo byte) uint16 {
	return uint16(hi)<<8 | uint16(lo)
}

//@ Ensures result = 256 * hi + lo
```

The translation works as follows.

- `x << k` is `x * 2^k`. It must not lose bits, which is checked like any other overflow.
- `x >> k` is `x / 2^k`, rounded down. This also holds for negative `x`.
- A shift count that may be negative is an error.
- `x & m`, where `m` is a constant mask of low bits, is a remainder. For non-negative `x`, `x & 0xFF` equals `x % 256`. For negative `x` the result is still non-negative, so `-1 & 0xFF` is 255, while `-1 % 256` is -1.
- `x & m`, where `m` is a single bit, is that bit of `x`.
- For any other `x & y`, only bounds are known.
- `x | y`, `x ^ y`, and `x &^ y` are computed from `x & y`. They are known exactly when `x & y` is.
- After `f |= m`, `vego` knows that `f & m` equals `m`.

These are the facts the prover starts from. It cannot always derive every consequence of them.

Formulas have no bit operators. Use `*`, `/`, and `%` in contracts.

## Code that is not verified

Verified code often has to call code that is not verified. This includes the standard library, other modules, and your own functions that use Go `vego` does not support. To make such a function callable, give it a trusted contract. `vego` uses a trusted contract without checking it.

All trusted contracts for a module are in one file, `vego-trusted.yaml`, next to `go.mod`. Trust cannot be declared in source code, so this file contains every unchecked contract your proofs depend on.

```yaml
version: 1

trusted:
  example.com/shop/internal/store.load:
    reason: Reads the stock file; reviewed 2026-11-10.
    modifies: []
    ensures:
      - "err = nil -> count >= 0"
```

Each entry has these fields:

| Field | Required | Content |
| --- | --- | --- |
| key | yes | The full name of the function as Go prints it, such as `sort.Ints`, `example.com/pkg.Func`, or `(*bytes.Buffer).Len`. |
| `reason` | yes | Why you believe the contract. |
| `modifies` | yes | What the function may write, in the form of a `Modifies` clause. `[x]` is the elements of slice `x`, `[b]` is the struct `b` points to, and `[b.count]` is one field. Write `modifies: []` if it writes nothing a caller can see. |
| `requires` | no | A list of formulas. Callers must prove each one. |
| `ensures` | no | A list of formulas. Callers can assume each one. |
| `runs` | no | Parameters that carry code the function may call. See [Arguments that carry code](#arguments-that-carry-code). |

Put the formulas in quotes. Several characters that formulas use have a special meaning in YAML.

The names in an entry are the parameter and result names from the function's source, including the receiver. For the standard library, `go doc -src bytes.Buffer.Len` shows that the receiver is called `b`. Unnamed results are `result`, or `result1`, `result2`, and so on.

### Shipped contracts

`vego` includes contracts for a few standard library functions:

- `sort.Ints`, `sort.IntsAreSorted`, `sort.SearchInts`
- `strings.Contains`, `strings.HasPrefix`, `strings.HasSuffix`, `strings.Index`, `strings.TrimSpace`, `strings.Repeat`, `strings.ToUpper`, `strings.ToLower`
- `unicode/utf8.RuneCountInString`
- `strconv.Itoa`, `strconv.Atoi`
- `math/rand.Intn`, `math/rand.Int`

The contracts are in `vego/trusted/std` in the source of `laas`. An entry in your own file with the same key replaces the shipped contract.

### Arguments that carry code

A trusted contract describes what the function's own code does. Some arguments bring code with them. An `error` has methods. So does any interface value, and a struct can have a field that holds a function. A trusted function could call that code, for example `err.Error()` or `l.sink(text)`, and the code could write memory that your proof depends on.

For this reason `vego` refuses to pass such a value to a trusted function:

```text
vego: cannot verify TellsUnknown: e is passed to tell, which is trusted, and is an error
whose origin is not known; tell could run code through it that nobody has seen. If its
contract holds whatever that code does, list e under runs in the contract
```

There are three ways to deal with this.

The first is to pass an error that verified code created with `errors.New` or `fmt.Errorf`. Such an error has only the standard library's methods and wraps nothing from outside. A package-level error also qualifies if its initialiser used only plain values and other errors of this kind. `var ErrRead = fmt.Errorf("read: %w", io.EOF)` does not qualify, because it wraps an error from another package.

The second is to make the call from unverified code. This is the right choice for logging an error that came from elsewhere. The unverified caller logs the error, and the verified function only returns it.

The third is to list the parameter under `runs` in the trusted contract:

```yaml
  (*example.com/shop/internal/journal.Journal).Append:
    reason: Appends a line through the writer the journal holds. A Journal is
      built only by journal.Open, which gives it an *os.File; reviewed 2026-11-14.
    runs: [j]
    modifies: [j]
```

`runs` does not check anything and does not make the call safe. It extends what the contract claims. With `runs: [j]`, the contract claims to hold for the whole call, whatever value is passed as `j`. In particular, the call writes nothing outside `modifies`, it returns, and it does not panic.

`vego` requires `runs` based on the parameter's type alone. It does not know what the function does with the value. The claim can be true in two situations:

- The function never calls the code it receives. An example is a function that only stores an error, or one that reads a number from a struct that also has a function field. The contract then does not depend on that code.
- The function does call the code, and you know every value that can be passed and have read its code. An example is a struct that is only ever built by one function of your own.

The claim is false for a function that calls the methods of an `error` when unverified callers can pass any error. Do not add `runs` in that case just to remove the message. The contract would be false, and every proof that uses it would be worthless.

The trust report shows `runs`, so that a reviewer of the trust file notices the larger claim.

### Limits of trusted contracts

A trusted contract does not make an unsupported signature callable. If a function has a parameter or result of an unsupported type, such as an interface or a function value, verified code cannot call it even with an entry. The message is `cannot verify Sync: parameter s has unsupported type example.com/shop.Store`. Write a small wrapper whose signature uses only supported types, and trust the wrapper.

A function cannot have both annotations and a trusted contract. When you verify a function that you previously trusted, delete its entry.

`vego` assumes nothing about a trusted function beyond its contract. For example, a returned pointer or slice could be anything unless the contract says `fresh(result)`.

### The trust report

This command prints every trusted contract the proofs use, with its reason and the places that call it:

```sh
laas -vego.trust ./...
```

If a trusted contract is wrong, every proof that uses it is worthless. Keep trusted contracts few, and claim no more than the function's documentation promises.

## Auditing a contract

A function can be verified against a contract that says very little. The `-vego.audit` flag looks for such contracts. For each contract it tries trivial implementations, such as "return zero" or "leave the slice unchanged", and reports each one that the contract would accept.

```sh
laas -vego -vego.audit ./...
```

```text
vego: specification of Sort has a hole [OBLIVIOUS]: it also accepts an implementation
that fills its slices with 0, 1, 2, ... whatever the input
```

A sort function gets this report if its contract only says that the output is sorted. A function annotated with only `Ensures True` gets a report too. Its contract has not been written yet.

## Adopting it

### In an existing package

A verified function can only call functions that have contracts. Start with functions that call nothing and work upwards.

1. Pick a leaf function. It should call nothing, or only functions with shipped contracts. Pure functions over numbers, slices, and strings are the easiest.
2. Add `//@ Ensures True` and run `laas -vego` on the package. This checks the function for index errors, overflow, nil dereferences, and termination. You will usually need to add `Requires` clauses with bounds, loop invariants, and variants. You may also find bugs.
3. Replace `Ensures True` with the real contract. Run `-vego.audit` to check that the contract says enough.
4. Move on to the callers. Each caller needs contracts for everything it calls. If a callee is not ready, give it a trusted contract with a reason such as "not verified yet". Delete the entry once the callee is verified.
5. Split functions that use unsupported Go. Move the logic into a verified function that works on plain data. Leave the part that uses an interface, a closure, or a goroutine unverified, and have it call the verified function.

Keep two things in mind while a package is partly verified.

The first is that nothing checks a `Requires` clause at run time. Verified callers prove it. Unverified callers are simply trusted to satisfy it, and `go build` and `go test` add no checks. Where data enters from outside, check it in code. Write a verified function with no `Requires` clause that tests its input and returns an error, and call it before the functions that need the precondition:

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

The second is that package-level variables are not supported, except for error variables. A function that reads a global variable must receive the value as a parameter instead.

### For one core component

The steps are the same, but design the component first so that it stays within the supported subset of Go.

- Use plain data: structs, slices, integers, strings, maps with integer or string keys, and pointers to structs. Keep interfaces, function values, and arrays out of its types.
- Write the struct invariant first. It is usually a sentence you would put in the doc comment anyway, such as "`n` never exceeds the length".
- Add `fresh(result)` to the contract of the constructor.
- Give each method the smallest `Modifies` list that works. If a method can replace a slice, add the clause described in [A slice that grows inside a struct](#a-slice-that-grows-inside-a-struct).
- Use `<->` to state when a function returns an error, where possible.

Then run the audit. Finally, write the unverified callers at the boundary so that they check the preconditions in code.

### In a new module

Put the logic in its own packages, separate from I/O, and write each contract before its function body.

Run the verifier in CI from the first commit, so that a change that breaks a proof cannot be merged. This only covers annotated functions. A function without a `//@` line always passes, whatever it does. If every function in a package is supposed to be verified, enforce that in code review or with your own check. `vego` does not enforce it.

Review changes to `vego-trusted.yaml` like code. Each line in it is a claim that the proofs do not cover.

### In CI

```sh
go install github.com/spachava753/laas/cmd/laas@<commit>
laas -vego ./...
```

- Pin the version. `laas` has no tagged releases yet, so install a specific commit and not `@latest`.
- Use the exit status. It is 0 when every annotated function is proved, 3 when anything is reported, and 1 when the packages could not be loaded.
- Build `laas` with the same Go that the job uses, as the commands above do. See the toolchain note in [Running it](#running-it).
- Do not use `-vego.trust` as the check. It prints a report for reviewers. It also exits with status 3 if verification reported problems.
- Set a time limit on the job. Small functions take well under a second each. Functions with many pointer parameters that may alias take much longer, and the tool has not been optimised yet. `-vego.max-steps` limits the work per proof obligation, not the total run time.

## When a proof fails

Work through these steps in order.

1. Read the message as "not proved". It names a proof obligation and a location. First decide whether the obligation is actually true at that location for every input the `Requires` clauses allow. Try extreme inputs: zero, negative numbers, the largest `int`, an empty slice, `nil`, and two arguments that are the same object.
2. If the obligation is false, you have found a bug in the code or in the contract. Fix whichever is wrong. The most common cause is a missing `Requires` clause.
3. If it is true and the failure comes after a loop, the loop invariant is too weak. `vego` forgets everything the loop changes except what the invariant states. This includes struct invariants.
4. If it is true and the failure comes after a call, the `Ensures` clauses of the callee are too weak. Strengthen them.
5. If it is an overflow, add a bound on an input, or rearrange the expression as in the midpoint example.
6. If it involves two pointers or two slices, check whether they can alias. If they must not, say so in the `Requires` clause.
7. Otherwise, help the prover. Put the fact in an `Assert` just before the failure. If the `Assert` is proved but the failure remains, assert a smaller intermediate step. If the `Assert` is not proved, move it earlier until it is.

One problem often produces several messages. Fix the first one and run again.

A message that starts with `cannot verify` is different. `vego` did not attempt a proof, and the text after the function name gives the reason. There are three kinds:

- Unsupported Go, such as `parameter x has unsupported type any`. Rewrite that part, or move it out of the verified function.
- A missing contract, such as `it calls helper, which has no contract`. Verify the callee or give it a trusted contract.
- A restriction on where something can appear, such as `the call must be a statement of its own`. The message says what to do.

## Messages

This table lists the most common messages.

| Message | Meaning | Usual fix |
| --- | --- | --- |
| `postcondition may not hold: P` | `P` is not proved at this `return`. | Follow the steps in [When a proof fails](#when-a-proof-fails). |
| `precondition of F may not hold: P` | A `Requires` clause of `F` is not proved at this call. | Establish it before the call, or add it to your own `Requires`. |
| `index may be out of range` | The index is not proved to be in range. | Add a `Requires` clause or an invariant that bounds the index. |
| `addition may overflow int`, and similar | The result is not proved to fit its type. | Bound the inputs, or rearrange the expression. |
| `loop invariant may not hold on entry` | The invariant is not proved before the first iteration. It is usually false there. | Fix the invariant or the code before the loop. |
| `loop invariant may not be preserved` | An iteration may break the invariant, or the invariant is too weak. | Add the clause that the invariant depends on. |
| `loop variant may not decrease`, `loop variant may be negative` | The `Variant` is not proved to decrease, or to stay non-negative. | Use a different `Variant`, or add an invariant that bounds it. |
| `measure may not decrease in recursive call`, `measure may be negative` | The same, for a `Measure`. | Use a different `Measure`, or strengthen the `Requires`. |
| `x is assigned, which F may not modify; list it in a //@ Modifies clause` | No `Modifies` entry covers memory of this kind. | Add it to `Modifies`. |
| `... which F may not modify: nothing its //@ Modifies clauses list is known to cover it` | An entry covers memory of this kind, but `vego` cannot prove it is this memory. It may be another element, another struct, or a slice that was replaced after `F` was called. | Make the entry match. For a replaced slice, the callee needs a `fresh ... Or within ...` clause. |
| `Modifies lists x, but F never needs to modify it` | The `Modifies` list allows more than the body needs. | Remove or narrow the entry. |
| `invariant of T may not hold for what is passed to F as x` | The struct invariant is not proved at the call. | Restore it before the call. In a loop, repeat it as a loop invariant. |
| `invariant of T may not hold for x on return` | The struct invariant is not proved at the end of the function. | Restore it before returning. |
| `the contract of F may also be met by a function that always returns an error` | No example input was found for which the contract forces success. | Add a clause of the form `condition -> err = nil`. See [Errors](#errors). |
| `specification of F has a hole` | Reported by `-vego.audit`. A trivial implementation satisfies the contract. | Relate the result to the input. |
| `nothing can satisfy the Requires clauses of F` | The `Requires` clauses contradict each other or the parameter types, so no call could satisfy them. | Fix the `Requires` clauses. |
| `the slices passed to F as a and b may overlap` | Two slice arguments with the same element type are not proved to be separate memory. | Pass two slice parameters of your own function, or a slice that the function allocated. No formula can yet state that two slices share no memory, so a slice stored in a struct cannot be proved separate from a parameter. |
| `cannot verify F: it calls G, which has no contract` | `G` is neither verified nor trusted. | Annotate `G`, or add it to the trust file. |
| `cannot verify F: parameter x has unsupported type T` | `T` is outside the supported subset. | Keep `T` out of the signatures of verified functions. |
| `cannot verify F: x is not a local variable` | `F` uses a package-level variable. | Pass the value as a parameter. |
| `cannot verify F: formatting err would run the methods of an error whose origin is not known` | `fmt.Errorf` is given an error that verified code did not create. | Return the error unchanged, or wrap your own error. |
| `x is passed to F, which is trusted, and is an error whose origin is not known` (or `a value of type T, which can hold an error, an interface, or a function`) | The trusted function `F` could call code that `x` carries. | See [Arguments that carry code](#arguments-that-carry-code). |
| `the trusted contract of F cannot be true of this call` | The contract contradicts what is known at the call. | The entry is wrong, or it needs a `requires` clause. |
| `the trusted contract ... cannot be used` | The entry in the trust file is invalid. The message says why. | Fix the entry. Check the parameter names. |
| `analysis skipped due to errors in package` | The package does not compile, or the toolchain does not match. | See [Running it](#running-it). |

## What is not supported

A function that uses any of the following is reported as `cannot verify`:

- interfaces other than `error`, calls through interfaces, type switches, and type assertions;
- function values, method values, and closures, including `defer func() { ... }()`;
- generic functions and types;
- goroutines, channels, and `select`;
- arrays, and structs that contain an array;
- pointers to anything other than a struct;
- package-level variables, except error variables;
- calls to variadic functions other than `fmt.Errorf`;
- `append(s, t...)` and `copy`;
- a modifying call inside a condition or a larger expression, as in `if !s.Push(x)` (see [Where a modifying call can appear](#where-a-modifying-call-can-appear));
- comparing structs or errors with `==`;
- `errors.Is` and `errors.As`;
- reading an error variable of another package, such as `io.EOF`;
- a `range` over a map whose body modifies a map of the same type;
- `goto`, `fallthrough`, labelled `break` and `continue`, and `defer` inside a loop.

Floating-point values are supported but opaque. They can be passed around and used in arithmetic, but nothing can be stated or proved about their values.

## What a proof assumes

A proof by `vego` depends on the following assumptions. Each concerns something `vego` cannot see.

- Trusted contracts are true. This applies to the shipped contracts and to your own. A trusted function returns without panicking when its `requires` clauses hold. It writes nothing a caller can see outside its `modifies` list. It does not keep the pointers and slices it receives. It does not call back, through another package, into the verified function that called it. For a parameter listed under `runs`, all of this holds whatever value is passed.
- Unverified callers respect the contract. They satisfy the `Requires` clauses, pass structs whose invariants hold, and do not pass overlapping slices for two slice parameters of the same element type.
- Unverified code respects Go's type system. It does not use `unsafe`, `reflect`, or cgo to give one piece of memory two types or to change a string.
- No other goroutine writes memory that a verified function reads or writes while it runs. A proof covers one goroutine.
- Packages that `laas` does not analyse do not reassign exported error variables.
- The program runs on the platform `laas` was run for. A proof for a 64-bit target does not hold for a 32-bit target.
- The machine has enough memory and stack.
- Formulas are well defined. `vego` does not check formulas for out-of-range indexes or division by zero. See [Formulas](#formulas).

## Summary

### Annotations

| Annotation | Where | Meaning |
| --- | --- | --- |
| `Requires P` | doc comment of a function | `P` must be true when the function is called. |
| `Ensures P` | doc comment, or after the closing brace | `P` is true when the function returns. |
| `Modifies a, b.f` | doc comment of a function | The memory the function may write that a caller can see. |
| `Measure e` | doc comment of a recursive function | `e` is never negative and is smaller at each recursive call. |
| `Invariant P` | directly above a loop | `P` is true each time the loop tests its condition. |
| `Variant e` | directly above a `for` loop | `e` is never negative and decreases on each iteration. |
| `Assert P` | in a function body | `P` must be true at this point and can be used afterwards. |
| `Invariant P` | doc comment of a struct type | `P` is true for every parameter, receiver, and result of the type at function boundaries. |
| `Predicate name(x, y) ::= P` | top level | Names a formula over its parameters. |

### Formulas

| Form | Meaning |
| --- | --- |
| `~P`, `P And Q`, `P Or Q` | not, and, or (in order of precedence, tightest first) |
| `P -> Q`, `P <-> Q` | implies, if and only if (lowest precedence) |
| `True`, `False` | the constants |
| `=`, `!=`, `<`, `<=`, `>`, `>=` | comparisons, which can be chained: `0 <= i < n` |
| `+`, `-`, `*`, `/`, `%` | arithmetic on mathematical integers; `/` and `%` round as in Go |
| `MaxInt`, `MinInt`, `MaxInt8` ... `MaxUint64` | limits of the Go integer types |
| `MaxAlloc` | the largest number of bytes in one allocation |
| <code>&#124;A&#124;</code>, `len(A)` | length of a slice or string, or number of keys in a map |
| `A[i]`, `m[k]`, `p.f` | element, map value, field |
| `A[lo:hi) <= x` | the comparison holds for every element from `lo` up to `hi` |
| `Forall k in [a, b) : P`, `Exists k in [a, b] : P` | quantifiers over an interval |
| `Forall k in Z : P` | quantifier over all integers |
| `"text"`, `nil` | a string; the nil pointer or nil error |
| `has(m, k)` | the map contains the key |
| `name(x, y)` | a predicate |

### Before and after

| Where | A plain name means | Other state |
| --- | --- | --- |
| `Requires` | the value at the call | |
| `Ensures` | the value at the call | `A'`, `c.f'`, `s.items'[0]`: the value on return |
| `Invariant` and `Assert` in a body | the current value | `old(x)`: the value at the call |

Results are named `result`, or `result1`, `result2`, and so on, unless they are named in the signature.

### Memory

| Form | Meaning |
| --- | --- |
| `Modifies p` | every field of the struct that `p` points to |
| `Modifies p.n` | the field `n`, if it holds a number, boolean, string, or struct |
| `Modifies p.f` | if `f` is a pointer, slice, or map: what `f` refers to, not the field itself |
| `Modifies A`, `Modifies s.items` | the elements of a slice, up to its capacity |
| `Modifies ps[0]` | one element of a slice of structs; for a slice of pointers, the struct the element points to |
| `Modifies m` | a map |
| `Modifies m[k]` | for a map of pointers, the struct that the pointer under key `k` points to |
| `fresh(x)` | the memory `x` refers to on return was allocated by the call; true for a slice with zero capacity |
| `within(a, b)` | `a` lies inside the memory of `b`; each is a pointer or a slice, and a slice includes its capacity |

### Flags

| Flag | Effect |
| --- | --- |
| `-vego` | run only the verifier |
| `-vego.audit` | also report contracts that trivial implementations satisfy |
| `-vego.max-steps=n` | limit on the prover's work for one proof obligation |
| `-vego.trusted=path` | use this trust file instead of the one next to `go.mod` |
| `-vego.trust` | print the trust report |
| `-test=false` | leave out test files |
| `-exclude-packages=regexp` | skip packages whose import path matches |
