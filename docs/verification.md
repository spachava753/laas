# Writing verified Go

## Introduction

`vego` proves things about Go functions. You say what a function must do in comments that start with `// @`, and `vego` either proves that the function does it for every input, or tells you what it could not prove. The comments do not change the program. It compiles and runs exactly as before.

This guide shows how to write Go that `vego` can verify. Read it from top to bottom the first time. After that, two sections work as a reference: [Messages](#messages) explains what the tool prints, and the [Summary](#summary) lists every annotation and formula form. The examples are run by the tests of `vego`. Their source is in `vego/testdata/src/guide`.

`vego` works best on self-contained logic such as index arithmetic, parsers, encoders, data structures, and validation. For each verified function it proves that:

- the function does not panic;
- no integer overflows;
- every loop and every recursion terminates;
- the function meets its contract;
- the function writes only the memory it declares.

`vego` never reports a function as correct when it is not. If it cannot handle a piece of Go, it reports `cannot verify` and names the construct. If it cannot find a proof, it reports `may not hold`. That means "not proved". The code may be wrong, the contract may be wrong, or both may be right and the prover needs a hint. Much of this guide is about working out which.

`vego` is experimental and supports only part of Go. It does not yet support interfaces other than `error`, calls of function values whose type has no contract, generics, goroutines, arrays, or package-level variables. [What is not supported](#what-is-not-supported) lists the main gaps. Code that does I/O usually runs into these limits. The usual approach is to verify the logic and leave the code around it unverified. [Adopting it](#adopting-it) describes how.

## Running it

`vego` is one of the analyzers in the `laas` command.

```sh
go install github.com/spachava753/laas/cmd/laas@latest
laas -vego ./...
```

`vego` proves obligations with Z3 5.4.1, which runs as a separate program. Install that release from <https://github.com/Z3Prover/z3/releases/tag/z3-5.4.1> and put its `bin/z3` on `PATH`. To use a binary elsewhere, pass `-vego.z3=path`. `laas` refuses any other version of Z3, because another version may prove different things. A package without annotations does not need Z3. Without Z3, a package with annotations fails with this message:

```text
vego: proving obligations needs Z3 5.4.1, and no z3 was found on PATH; install Z3 5.4.1
from https://github.com/Z3Prover/z3/releases/tag/z3-5.4.1 and put its bin/z3 on PATH, or
name it with -vego.z3
```

`laas -vego` runs only the verifier. Plain `laas` also runs the other analyzers, which report on things unrelated to verification. The arguments are package patterns, as for `go vet`. Use `./...` for everything or `./internal/core` for one package.

`vego` verifies a function only if it has at least one `// @` annotation. It ignores every other function, so you can start with a single function in a large package. To turn on [the built-in checks](#built-in-checks) without writing a contract, add `// @Ensures True`.

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
//
// @Ensures result >= a And result >= b
// @Ensures result = a Or result = b
func Max(a, b int) (result int) {
	if a > b {
		return a
	}
	return b
}
```

An `Ensures` clause states what is true when the function returns. The contract refers to the returned value by the name the function gives it, here `result`. A verified function must name all of its results. Running `laas -vego` on this file prints nothing, so both clauses are proved for every `a` and `b`.

Now change the function to return `b` on both branches. `vego` reports:

```text
vego: postcondition may not hold: result >= a
```

The message points at the `return` statement and names the part of the contract that fails there. Clauses joined with `And` are checked separately, so the message names only the failing part.

The next function looks correct but is not.

```go
// @Ensures result >= 0
func Abs(x int) (result int) {
	if x < 0 {
		return -x
	}
	return x
}
```

```text
vego: negation may overflow int
```

The smallest `int` has no positive counterpart. Negating it overflows, and `Abs` returns a negative number. `vego` reports this because it checks every arithmetic operation in a verified function for overflow. Nothing in the contract asked for that check.

The fix is to exclude that input:

```go
// @Requires x > MinInt
// @Ensures result >= 0 And (result = x Or result = -x)
func Abs(x int) (result int) {
	if x < 0 {
		return -x
	}
	return x
}
```

A `Requires` clause states what must be true when the function is called. The function body may assume it. Every verified caller must prove it.

Together, `Requires` and `Ensures` are the function's contract. Working with `vego` means writing a contract, reading what `vego` could not prove, and then fixing either the code or the contract.

## Annotations

An annotation is a comment line of the form `// @Keyword ...`. There are seven keywords. Each is allowed only in certain places.

| Keyword | Where it goes |
| --- | --- |
| `Requires`, `Ensures`, `Modifies` | the doc comment of a function |
| `Variant` | the doc comment of a recursive function, or directly above a `for` loop |
| `Invariant` | directly above a loop |
| `Assert` | anywhere in a function body, on its own line |
| `Invariant` | the doc comment of a struct type |
| `Predicate` | the top level of a file |

Write one space between `//` and `@`, and no space between `@` and the keyword. `gofmt` leaves this form unchanged. Any other spacing, such as `//@Requires` or `// @ Requires`, is reported as an error.

To continue a long annotation, start the next line with `// @`, a space, and the rest of the formula. A `//` inside an annotation starts an ordinary comment.

```go
// @Ensures result = -1 Or
// @   (0 <= result < |A| And A[result] = x)
```

An ordinary comment directly after an annotation is an error, because it would not be read as part of the annotation. Put an empty `//` line between an annotation and a comment that follows it. A blank line does not work in a doc comment, because it would detach the annotations from the function.

`vego` reports an annotation it cannot read instead of skipping it. These are all errors:

- a misspelt keyword, such as `// @Ensure` or `// @ensures`;
- an annotation inside `/* */`;
- a continuation line `// @ ...` with no annotation above it;
- an `Ensures` clause after the function body;
- an annotation with something in front of the `@`, such as `// post: @ Ensures ...`.

Any other word after `// @` is also an error. `vego` cannot tell a wrong keyword such as `// @Post` from a tag that another tool reads, so it reports both:

```text
vego: unknown annotation "Post"; an annotation starts with one of Requires, Ensures, Modifies,
Invariant, Variant, Assert, Predicate. If another tool reads this comment, declare the word
with -vego.other-tags
```

If your code has comments such as `// @Summary` for another tool, list those words once:

```sh
laas -vego -vego.other-tags=Summary,Param,Router ./...
```

`vego` then treats those lines as ordinary comments. A word that is a keyword, or within two letters of one, cannot be declared.

While a package has an annotation that `vego` could not read or attach to anything, other packages cannot rely on any of its contracts. This covers every error in this section, and also a clause that is dropped, such as a second `Variant` on one function or a `Requires` in the doc comment of a type. The annotation could have been meant for any function of the package.

The same rule applies where an `@` starts a line with only signs in front of it, as in `/// @Post` or a line of a `/* */` comment. An `@` after other words, as in `// note: @Post r > 100`, is reported only if the word is a keyword or within two letters of one, because `vego` cannot tell it from an address or a user name.

One kind of comment is ignored without a declaration. An annotation behind a second `//`, as in `// // @Ensures r > 0`, is treated as commented out or quoted. This is also how an example in a doc comment can show an annotation.

## Formulas

The text after a keyword is a formula. Formulas look like Go conditions, with these differences.

The logical operators are `And`, `Or`, `~` (not), `->` (implies), and `<->` (if and only if). Equality is a single `=`. Comparisons can be chained, so `0 <= i < n` is valid.

```go
// @Ensures result = -1 Or (0 <= result < |A| And A[result] = x)
```

`~` binds tightest, followed by `And`, `Or`, `->`, and `<->`. `a -> b -> c` means `a -> (b -> c)`. Use parentheses if you are unsure.

Numbers in formulas are mathematical integers. They do not overflow, so `x + 1` is always one more than `x`, whatever the type of `x`. `/` and `%` round as they do in Go. The limits of the Go integer types have names: `MaxInt`, `MinInt`, `MaxInt8` to `MaxInt64`, `MinInt8` to `MinInt64`, and `MaxUint` to `MaxUint64`. `MaxAlloc` is the largest number of bytes in one allocation on the platform. No string is longer than `MaxAlloc`.

`|A|` is the length of a slice or string, or the number of keys in a map. `A[i]` is an element. Fields are written with a dot, including through pointers: `c.count`, `s.items[i]`, `|s.items|`.

Formulas can also use strings and `nil`: `role = "admin"`, `p != nil`, `err = nil`. Two pointers can be compared with each other, as in `a != b`. Two errors can be compared too, as in `err = ErrEmpty`, and `is(err, ErrEmpty)` says what `errors.Is` reports. See [Saying which error a function returns](#saying-which-error-a-function-returns).

A boolean can be used as a formula on its own, as in `found` or `~found`. It can also be compared with `True` and `False`, as in `found = True`.

### Quantifiers

`Forall` and `Exists` range over an interval of integers.

```go
// @Requires Forall k in [0, |A|) : 0 <= A[k] <= 1000
// @Ensures Exists k in [0, |A|) : A[k] = result
```

Intervals use mathematical notation. `[0, n)` includes 0 and excludes `n`. `[0, n]` includes both. Several variables can share an interval, as in `Forall i, j in [0, n) : ...`. `in Z` ranges over all integers.

The body of a quantifier extends to the end of the clause. To end it earlier, put the whole quantifier in parentheses.

There is a short form for a condition on a range of elements. `A[lo:hi) <= x` means that every element from index `lo` up to, but not including, `hi` is at most `x`. Any comparison operator can be used.

### Names

A contract can use the function's parameters and results, and the integer and boolean constants of the package. String constants cannot be used by name. Write the string itself. A contract can also name the error variables of the package, as in `ErrEmpty`, and those of an imported package, as in `io.EOF`. A trusted contract names them by the path of their package instead. See [Error variables in a trusted contract](#error-variables-in-a-trusted-contract).

Results are referred to by their names, so every result of a verified function must be named. This guide calls a single result `result`, but you can choose another name. Go does not allow a result to share a name with a parameter, so a name in a contract cannot mean both. Three names are not available for variables that annotations use: `True`, `False`, and `nil`, which are words of the formula language. A predicate cannot be called `is`.

```text
vego: Unnamed has annotations, so each of its results needs a name, as in func Unnamed(...) (n int, err error)
```

### Limits

Formulas have no bit operators, no `len` or `cap`, and no floating-point facts. Write `|A|` for a length. They cannot call functions, only predicates. They have no character literals, so write `48` for `'0'`. A slice cannot be compared with `nil`. Use `|A| = 0`. Structs cannot be compared as a whole. Compare their fields.

`vego` does not check that a formula is well defined. `A[i]` in a formula can be out of range, and `x / y` can divide by zero. Such an expression has an unknown value. A clause that uses it usually cannot be proved, but it can also be trivially true and pass, as `A[999] = A[999]` does. Guard such expressions as you would in code: `0 <= i < |A| And A[i] = x`.

## Built-in checks

Every verified function gets the checks in this section. They do not depend on the contract.

### Index bounds

Every index must be proved to be in range.

```go
// @Ensures result = A[0]
func First(A []int) (result int) {
	return A[0]
}
```

```text
vego: index may be out of range
```

Adding `// @Requires |A| > 0` fixes it. Every verified caller of `First` must then prove that its slice is not empty.

### Nil pointers and division

A pointer must be proved non-nil wherever it is dereferenced. For a parameter or receiver, this usually means adding `Requires p != nil`.

A divisor must be proved non-zero.

### Overflow

Every `+`, `-`, `*`, `/`, negation, conversion, and left shift must be proved to stay within its type.

```go
// @Requires 0 <= lo <= hi
func Mid(lo, hi int) (result int) {
	return (lo + hi) / 2
}
```

```text
vego: addition may overflow int
```

`lo + hi` can exceed the largest `int` even though the midpoint cannot. `lo + (hi-lo)/2` verifies.

Overflow is the check you will see most often. Code that adds up values can only be proved if the values are bounded, so contracts often need bounds on their inputs:

```go
// @Requires |A| <= 1000
// @Requires Forall k in [0, |A|) : 0 <= A[k] <= 1000
func Sum(A []int) (result int) {
```

These bounds are part of the function's real contract. Without them the function is wrong for some inputs.

Code that overflows on purpose, such as a hash function, cannot be verified. Neither can a conversion that drops bits. `byte(x)` is an error unless `x` is known to fit in a byte. `byte(x & 0xFF)` is accepted.

### Allocation, panics, and termination

`make`, an `append` that grows the slice, and string concatenation must be proved to stay under the largest allocation the platform allows. This usually means bounding sizes. The length passed to `make` must also be proved not to be negative. If it is not, `vego` reports `make length may be negative`.

A reachable call to `panic` is an error.

Every loop and every recursive function must be proved to terminate. The next two sections explain how.

### Checking safety only

To get these checks without stating anything else, use a contract that is always true:

```go
// @Ensures True
func SafeOnly(A []int, i int) (result int) {
	if 0 <= i && i < len(A) {
		return A[i]
	}
	return 0
}
```

This is a good first step when you add `vego` to existing code.

## Loops

`vego` does not execute a loop. It reasons about a single, arbitrary iteration. To do that it needs a loop invariant: a formula that is true every time the loop is about to test its condition.

```go
// @Requires n >= 0 And d > 0
// @Ensures n = d*q + r And 0 <= r < d
func Divide(n, d int) (q, r int) {
	q, r = 0, n
	// @Invariant n = d*q + r And 0 <= r
	// @Variant r
	for d <= r {
		q, r = q+1, r-d
	}
	return q, r
}
```

`vego` checks two things about an invariant. It must be true when the loop is first reached. And if it is true before an iteration, it must be true after it.

After the loop, `vego` knows the invariant and that the loop condition is false. Here that gives `n = d*q + r`, `0 <= r`, and `r < d`, which is the postcondition. A condition that modifies memory is different: see [A condition that modifies memory](#a-condition-that-modifies-memory).

**After a loop, `vego` knows nothing about the variables the loop changed except what the invariant states.** If a proof fails in the code after a loop and the fact is true, the invariant is too weak: it is missing something you know about the loop variables. A loop that writes memory can also make `vego` forget memory it did not write. See [What a loop forgets about memory](#what-a-loop-forgets-about-memory).

A `Variant` proves that a `for` loop terminates. It is an integer expression that is never negative while the loop runs and that decreases on every iteration. Every `for` loop needs one.

A `range` loop needs no `Variant`. `vego` also knows the bounds of its index variable.

```go
// @Requires |A| <= 1000
// @Requires Forall k in [0, |A|) : 0 <= A[k] <= 1000
// @Ensures 0 <= result <= 1000 * |A|
func Sum(A []int) (result int) {
	total := 0
	// @Invariant 0 <= total <= 1000 * i
	for i := range A {
		total += A[i]
	}
	return total
}
```

The invariant bounds `total` after `i` elements. That bound lets `total += A[i]` pass the overflow check. When the loop ends, `i` equals `|A|`, and the invariant becomes the postcondition.

This invariant refers to the index, so the loop must name it. With `for _, x := range A` there is no name to use. Write `for i := range A` and read `A[i]`.

When a loop processes a slice one element at a time, the invariant usually states that the part processed so far is correct:

```go
// @Ensures result = -1 Or (0 <= result < |A| And A[result] = x)
// @Ensures result = -1 -> Forall k in [0, |A|) : A[k] != x
func Index(A []int, x int) (result int) {
	// @Invariant Forall k in [0, i) : A[k] != x
	for i := range A {
		if A[i] == x {
			return i
		}
	}
	return -1
}
```

A common way to find an invariant is to take the postcondition and replace the upper bound with the loop index. Above, `[0, |A|)` in the postcondition became `[0, i)` in the invariant.

`break`, `continue`, and `return` work inside loops. A `return` inside a loop must establish the postcondition using only the invariant and the conditions on the path to the `return`.

### A condition that modifies memory

The condition of a `for` loop can call a function that modifies memory, as an iterator does:

```go
type Iter struct {
	i, n int
}

// @Requires it != nil And 0 <= it.i <= it.n
// @Modifies it.i
// @Ensures it.i < it.n -> it.i' = it.i + 1 And result
// @Ensures it.i = it.n -> it.i' = it.i And ~result
func (it *Iter) Next() (result bool) {
	if it.i < it.n {
		it.i++
		return true
	}
	return false
}

// @Requires it != nil And it.i = 0 And 0 <= it.n < 1000
// @Modifies it.i
// @Ensures result = it.n And it.i' = it.n
func Count(it *Iter) (result int) {
	count := 0
	// @Invariant 0 <= it.i <= it.n And count = it.i
	// @Variant it.n - it.i
	for it.Next() {
		count++
	}
	return count
}
```

The invariant must be true each time the loop is about to test its condition, before the condition runs. The condition runs once more than the body. The last time, it returns false and the loop ends. After the loop, `vego` knows that the invariant held of memory as it was before that last test. What the condition wrote then is known only from the `Ensures` clauses of the call. Here `Next` returned false, so `it.i` equals `it.n`.

The `Variant` is also measured before the condition runs, so it must decrease over the condition and the body together. The loop forgets what its condition writes, as it forgets what its body writes, and the function must list that memory in `Modifies`.

### Messages about invariants

There are two messages about invariants:

- `loop invariant may not hold on entry` means the invariant was not proved before the first iteration. Usually it is false at that point. Sometimes the prover needs help.
- `loop invariant may not be preserved` means `vego` could not prove that an iteration keeps the invariant true. Either an iteration really can break it, or the invariant is too weak. A weak invariant is fixed by adding a second clause that the first one depends on.

## Recursion

A recursive function needs a `Variant` in its doc comment to prove that it terminates. Here the variant is an integer expression over the parameters. It must never be negative, and it must be smaller at every recursive call. Functions that call each other each need one.

```go
// @Requires n >= 0
// @Variant n
// @Ensures result = n
func Steps(n int) (result int) {
	if n == 0 {
		return 0
	}
	return 1 + Steps(n-1)
}
```

At the recursive call, `vego` uses the contract of `Steps` with `n-1` as the argument. It does not look at the body. All calls work this way.

## Calls

`vego` verifies a call using only the contract of the called function. It never looks at the callee's body.

```go
// @Requires lo <= hi
// @Ensures lo <= result <= hi
func Clamp(x, lo, hi int) (result int) {
	if x < lo {
		return lo
	}
	if x > hi {
		return hi
	}
	return x
}

// @Ensures 0 <= result <= 100
func Percent(x int) (result int) {
	return Clamp(x, 0, 100)
}
```

At the call, `Percent` must prove the precondition `0 <= 100`. After the call it knows `0 <= result <= 100` and nothing else. It does not know that `Clamp` returns `x` unchanged when `x` is already in range, because the contract of `Clamp` does not say so. If a caller needs a fact about a function, add it to that function's `Ensures`.

Each function is therefore proved once, on its own. The cost is that a function with a weak contract causes proof failures in its callers, not in itself.

A function without a contract cannot be called from verified code:

```text
vego: cannot verify CallsHelper: it calls helper, which has no contract; annotate
helper with // @ annotations so that it is verified, or add a trusted contract for guide.helper
to vego-trusted.yaml
```

Either verify the helper, or give it a trusted contract as described in [Code that is not verified](#code-that-is-not-verified).

The contract of an exported function is available to other packages, so verified code can call verified functions in other packages. If a function failed verification, other packages cannot rely on its contract.

## Function literals

`vego` verifies a function literal when every use of it is in the function that contains it. A literal can stand in three places:

- where it is called, as in `func() { ... }()`;
- where it is deferred, as in `defer func() { ... }()`;
- as the value that declares a new local variable, which the function then only calls.

```go
// @Requires |A| = 3
// @Ensures result <-> A[0] <= A[1] And A[1] <= A[2]
func Sorted3(A []int) (result bool) {
	inOrder := func(i, j int) bool { return A[i] <= A[j] }
	return inOrder(0, 1) && inOrder(1, 2)
}
```

A literal has no contract. `vego` verifies its body at each call, in the state at that call, as part of the function around it. The body is held to everything the function is held to: the built-in checks, the `Modifies` clauses of the function, and the order of evaluation. A `return` inside the body ends the literal. An `Invariant`, `Variant`, or `Assert` inside the body is checked at each call.

A message about the body names the call it comes from:

```go
// @Ensures True
func CheckEach() {
	check := func(n int) {
		// @Assert n >= 0
	}
	check(1)
	check(-1)
}
```

```text
vego: assertion may not hold: n >= 0, in the function literal called at literals.go:23:2
```

The assertion holds at the first call. At the second it is not proved. For a deferred literal, the message ends in one of these ways, depending on whether the literal runs at a `return`, at the end of the function, or at the end of the function literal it is deferred in:

```text
, in the function literal deferred at f.go:19:8 and run at the return at f.go:20:2
, in the function literal deferred at f.go:19:8 and run at the end of the function at f.go:20:1
, in the function literal deferred at f.go:19:8 and run at the end of the function literal at f.go:20:2
```

Inside a literal, `old(x)` is the value that the parameter `x` of the function had when the function was called. If the literal has a parameter of the same name, `old(x)` is an error. Rename the parameter of the literal.

### Variables that a literal assigns

A literal reads and writes the variables of the function around it, as they are when the literal runs.

```go
// @Ensures 0 <= result <= 2
// @Ensures a >= 0 And b >= 0 -> result = 0
func CountNegative(a, b int) (result int) {
	count := 0
	check := func(x int) {
		if x < 0 {
			count++
		}
	}
	check(a)
	check(b)
	return count
}
```

A loop that calls a literal forgets the variables that the literal assigns, in the same way as the variables that the loop body assigns. State what the loop keeps of them in an invariant.

A call of a literal can change a variable that the literal assigns. Go does not fix whether the other operands of a statement are read before or after a call, so `vego` checks a read of such a variable like a read of memory (see [Reads that Go may make before or after a call](#reads-that-go-may-make-before-or-after-a-call)):

```go
// @Requires 0 <= x < 1000
// @Ensures True
func ReadAndBump(x int) (result int) {
	bump := func() int {
		x++
		return 0
	}
	return x + bump()
}
```

```text
vego: x may be read before or after the call to bump, which may change it, and Go does not
fix the order; split the statement so that the order is the one you mean, as in x0 := x before it
```

### Literals that cannot be verified

A literal that is passed to a function, returned, or stored is a function value. It needs a function type with a contract, and is verified as described in [Function literals as values](#function-literals-as-values). A literal given a type without a contract is reported as `cannot verify`:

```go
// @Ensures True
func Printer() (f func(x int)) {
	return func(x int) {}
}
```

```text
vego: cannot verify Printer: the function literal is used as a value of type func(x int), which
has no contract; declare a named function type with a contract and use it here
```

A variable declared with `:=` that holds a literal and is used other than by calling it is reported as `cannot verify` too, with the message `f holds a function literal and is used here other than by calling it`. Declare it with a type that has a contract instead, as in `var f T = func...`. A variadic literal cannot be verified, and neither can a literal that takes or returns a type that `vego` does not support.

## Function values

A function value is a value of a function type: a parameter, a result, a variable, a field, an element of a slice, or a value in a map. `vego` calls a function value only through the contract of its type. You write that contract in the doc comment of a named function type, with the keywords a function uses:

```go
// Mapper maps a number in range to a number in range.
//
// @Requires 0 <= x <= 1000
// @Ensures 0 <= y <= 2000
type Mapper func(x int) (y int)

// @Requires f != nil
// @Requires Forall i in [0, |xs|) : 0 <= xs[i] <= 1000
// @Modifies xs
// @Ensures Forall i in [0, |xs|) : 0 <= xs'[i] <= 2000
func Apply(xs []int, f Mapper) {
	// @Invariant Forall k in [0, i) : 0 <= xs[k] <= 2000
	// @Invariant Forall k in [i, |xs|) : xs[k] = old(xs)[k]
	for i := range xs {
		xs[i] = f(xs[i])
	}
}
```

At the call `f(xs[i])`, `Apply` proves that `f` is not nil and that the `Requires` clause of `Mapper` holds. After the call it knows the `Ensures` clause of `Mapper` and nothing else. The call is checked like any other call: what the `Modifies` clauses of the type list must be memory that `Apply` may modify. A call through a value can be deferred too, as in `defer done(s)`. The value and the arguments are evaluated at the `defer` statement.

A function value that may be nil cannot be called:

```text
vego: the function value f may be nil
```

A function value can be compared with `nil`, in code and in formulas, as in `f != nil` and `Forall i in [0, |opts|) : opts[i] != nil`. Go allows no other comparison of function values, and neither do formulas.

### A function type without a contract

A value of a function type without a contract can be held, passed on, stored, and compared with `nil`, but not called:

```go
// @Ensures True
func TwiceOf(f func(int) int) (y int) {
	return f(1)
}
```

```text
vego: cannot verify TwiceOf: f has type func(int) int, which has no contract; declare a named
function type with a contract and use it here
```

Declare a named type such as `Mapper` and use it for the parameter. A contract can only be written on a named type, so a function type of another package that has no annotations, such as `context.CancelFunc`, cannot be called.

### Writing a contract on a function type

The contract of a function type names the parameters and results of its signature. A function type with a contract must name its results, as a verified function does. Parameters that the contract does not mention may stay unnamed. `Requires`, `Ensures`, and `Modifies` are the only annotations a function type can have.

`vego` checks the contract where the type is declared, whether or not anything uses the type. It reports a contract that cannot be read, `Requires` clauses that nothing satisfies, and an `Ensures` that some call its `Requires` allow could not meet:

```go
// @Requires 0 <= x <= 1000
// @Ensures 2 * y = x
type Half func(x int) (y int)
```

```text
vego: the Ensures clauses of Half are not proved to be satisfiable for every call that its
Requires allow, by results and a change of what Modifies lists; a value of the type is taken to
meet them, so a call of one could prove something false. State in the Requires when some result
exists, or weaken the Ensures
```

No `y` satisfies `2 * y = x` when `x` is odd. `vego` takes a value that comes from code it does not verify to meet the contract of its type, so a call of such a value would let `vego` conclude that `x` is even. To show that a contract can be met, `vego` chooses results and, for each struct or field that `Modifies` lists, new contents. It does not choose new elements for a slice or a map, so an `Ensures` that only a change of their elements can meet is reported too.

### Making a function value

A value of a type with a contract is checked where Go converts something to the type: where it is passed, assigned, returned, stored, or converted with `T(...)`. Three things can become such a value there:

- a function, as in `Apply(xs, double)`;
- a method value, as in `h.Serve`;
- a function literal.

`vego` checks each as a function of its own with the contract of the type. Called with arguments that meet the `Requires` of the type, it must meet its own `Requires`, write only what the type lists in `Modifies`, and leave the `Ensures` of the type true. It is checked against memory it knows nothing about, because the value may run at any later time:

```go
// @Requires 0 <= x <= 10
// @Ensures y = x
func small(x int) (y int) {
	return x
}

// @Ensures f != nil
func Small() (f Mapper) {
	return small
}
```

```text
vego: precondition of small may not hold: 0 <= x <= 10, in small used as a Mapper at funcvalues.go:103:9
```

The receiver of a method value is evaluated where the value is made, as in Go. What `vego` knows of the receiver's value there is known when the value runs, but not what is in memory.

`nil` and a value of the same type can also be assigned. Nothing else can become a value of the type: a value of another function type cannot, even when Go would convert it, because nothing shows that it meets the contract. A method expression, as in `T.M`, cannot be used as a value.

### Function literals as values

A function literal that is passed, returned, or stored is a value of the type it is given. This option sets a field of the configuration it is called with:

```go
type Config struct {
	Timeout int
	Retries int
}

// @Requires c != nil
// @Modifies c
type Option func(c *Config)

// @Requires Forall i in [0, |opts|) : opts[i] != nil
// @Ensures True
func Configure(opts []Option) (cfg Config) {
	for _, opt := range opts {
		opt(&cfg)
	}
	return cfg
}

// @Ensures o != nil
func WithTimeout(d int) (o Option) {
	return func(c *Config) {
		c.Timeout = d
	}
}
```

A literal used as a value may run after the function that made it has returned. So the body of the literal knows this of the variables it captures:

- A variable that nothing assigns after its declaration, and whose address is not taken, has the value it had where the literal was made. What `vego` knew of that value there is known in the literal. `d` above is such a variable.
- Any other variable can have any value of its type. A named result is one, because a `return` assigns it.

From Go 1.22 on, each iteration of a `range` loop has its own variables, so a literal made in an iteration knows the values of that iteration. In a file compiled as an earlier Go, and for the variable of a three-clause `for` loop, the loop assigns the variable, so the literal knows nothing of it.

```go
// @Requires 0 <= k <= 1000
// @Ensures f != nil
func Offset(k int) (f Mapper) {
	return func(x int) int {
		return x + k
	}
}

// @Ensures f != nil
func Later() (f Mapper) {
	k := 1
	f = func(x int) int {
		return x + k
	}
	k = 5000
	return f
}
```

`Offset` is verified. In `Later`, `k` is assigned after the literal is made, so `vego` reports:

```text
vego: addition may overflow int, in the function literal used as a Mapper at funcvalues.go:121:6
vego: postcondition may not hold: 0 <= y <= 2000, in the function literal used as a Mapper at funcvalues.go:121:6
```

A literal used as a value cannot assign a variable it captures:

```text
vego: cannot verify Tally: a function literal used as a value cannot assign calls, a variable of
the function around it: it may run when that function has moved on, and no call of it could tell
that function what it did
```

A literal used as a value cannot call a variable that holds a literal of the function around it. Inside the body of the literal, `old(x)` is the value that its own parameter `x` had when it was called.

### Function values that call function values

The code that a function value made by verified code runs cannot call through a function value. That rules out a literal that calls a value it captures, a literal or function that passes a value to a function that calls it, and a function used as a value that calls through a value itself:

```go
// @Requires f != nil
// @Ensures g != nil
func Logged(f Mapper) (g Mapper) {
	return func(x int) int {
		return f(x)
	}
}
```

```text
vego: cannot verify Logged: the function literal used as a value calls through the function value
f, and code that a function value runs cannot do that yet: no contract of a function type has a
variant, so nothing would prove that such calls end
```

A contract of a function type has no `Variant`. A value could be handed back to code that calls it again, and nothing would show that this ends. With this rule, a call through a value that verified code made runs code that makes no such call.

### Function values from code that is not verified

A function value that verified code receives from code it does not verify is taken to meet the contract of its type. See [What a proof assumes](#what-a-proof-assumes). Such a value could run code that an argument carries. So an argument that can carry code nobody has seen cannot be passed to a function value: an error whose origin is not known, a function value whose type has no contract, or another interface.

```go
// @Requires e != nil
type Report func(e error)

// @Requires r != nil And e != nil
// @Ensures True
func Tell(r Report, e error) {
	r(e)
}
```

```text
vego: cannot verify Tell: e is passed to the function value r and is an error whose origin is
not known; the value may come from code that is not verified, which could run code through it
that nobody has seen
```

An error made with `errors.New` or `fmt.Errorf` can be passed, and so can a function value of a type with a contract.

## Predicates

A predicate gives a name to a formula so that you can reuse it.

```go
// @Predicate sorted(A) ::= Forall i, j in [0, |A|) : i <= j -> A[i] <= A[j]

// @Requires sorted(A) And |A| > 0
// @Ensures Forall k in [0, |A|) : result <= A[k]
func Smallest(A []int) (result int) {
	return A[0]
}
```

The parameters of a predicate can be numbers, slices of numbers, or strings.

```go
// @Predicate digits(s) ::= Forall k in [0, |s|) : 48 <= s[k] <= 57
```

The body of a predicate can refer only to its parameters. It cannot use the constants or variables of the package, so pass them as arguments.

A predicate can be recursive:

```go
// @Predicate zeros(A, n) ::= n <= 0 Or (zeros(A, n-1) And A[n-1] = 0)
```

In its own definition, a predicate may appear under `And`, `Or`, and quantifiers, and on the right side of `->`. It may not appear under `~`, on the left side of `->`, or inside `<->`.

Use a recursive predicate only for a property that `Forall` cannot express. The prover expands the definition where the predicate is applied and does not do induction, so recursive predicates are hard to prove things with. For example, a sum or count over a slice cannot currently be kept as the invariant of a loop that writes to that slice.

## Helping the prover

The prover is Z3. It decides linear integer arithmetic and reads and writes of slices. It uses a `Forall` fact where the proof contains a term that matches it, and it handles products of variables only in part. When it fails to prove something true, the fix is usually to state an intermediate fact.

`Assert` states such a fact. `vego` must prove the assertion at that point, and can use it in everything that follows.

```go
// @Assert lo < |A|
```

`Assert` is also the way to find out what `vego` knows at a given point. Assert the fact you believe, and if it fails, move the assertion earlier in the function until it is proved. The fact is lost between the last place where it is proved and the first place where it is not. Often that is a loop whose invariant does not mention it.

This example needs no help, although it multiplies two variables:

```go
// @Requires 0 <= i < h And 0 <= j < w And h <= 1000 And w <= 1000
// @Ensures 0 <= result < h*w
func Cell(i, j, w, h int) (result int) {
	return i*w + j
}
```

`-vego.rlimit` raises the limit on how much work Z3 does for one proof obligation. The default is 4000000. Z3 counts its work deterministically, so the same binary gives the same answers on every run. Most failures are caused by a missing fact, which more effort cannot supply. A proof that needs the higher limit is also slow every time the tool runs.

When Z3 stopped at a limit, the message ends with a note that says which one:

| Note | What to do |
| --- | --- |
| `(Z3 reached its resource limit; -vego.rlimit raises it)` | Add the missing fact first. If the obligation still fails, try a higher `-vego.rlimit`. |
| `(Z3 ran past its time limit, which depends on the machine)` | Z3 ran for five minutes. Split the function or add facts. This limit depends on the speed of the machine, so the result may differ elsewhere. |
| `(Z3 ran out of memory)` | Z3 used the 1 GB a process may have. `-vego.rlimit` does not help. Split the function or add facts. |

A message without a note means that Z3 gave its answer within the limits.

## Changing memory

The functions so far only computed values. A function can also write memory that its caller can see: the elements of a slice, the fields of a struct behind a pointer, or a map. Such a function must declare what it writes and describe the result.

```go
// @Modifies A
// @Ensures Forall k in [0, |A|) : A'[k] = v
func Fill(A []int, v int) {
	// @Invariant Forall k in [0, i) : A[k] = v
	for i := range A {
		A[i] = v
	}
}
```

### Modifies

`Modifies` lists the memory a function is allowed to write. Writing anything else is an error:

```text
vego: A[i] is assigned, which FillUnlisted may not modify; list it in a // @Modifies clause
```

A caller can rely on everything outside the list being unchanged. About the memory in the list, it knows only what the `Ensures` clauses state. So keep the list as small as possible. With `Modifies c.n`, callers keep what they know about the other fields of `c`. With `Modifies c`, they lose it.

`vego` also reports a `Modifies` entry that the function body never needs.

An entry must name memory that the caller can see. A parameter passed by value is a copy, so `Modifies n` for an `int` parameter is reported as `in Modifies annotation: n is passed by value, so the caller cannot see a change to it`.

A `Modifies` path is evaluated when the function is called. `Modifies s.items` refers to the slice that `s.items` held at that moment, even if the function later stores a different slice in the field.

### Before and after

In an `Ensures` clause, a name refers to the value at the time of the call. To refer to memory as it is when the function returns, add a prime. In the example, `A'[k]` is element `k` on return and `A[k]` is the element at the time of the call. For a field, write `c.n'`. The prime comes after the name or field and before any index: `s.items'[0]`.

The prime is only needed for memory that the function can change. A parameter that is a plain value, such as `v`, never takes one.

Inside a function body the convention is reversed. In an `Invariant` or `Assert`, a name refers to the current value. `old(x)` refers to the value of a parameter at the time of the call. It also works for memory reached from a parameter, as in `old(c.n)`. The name must refer to the parameter at that point, and not to a variable that hides it.

## Slices

A slice parameter shares its array with the caller. A function that writes the elements must list the slice in `Modifies`.

Two rules reduce the annotations that slices need.

First, slice parameters with the same element type do not overlap. A function can assume that two `[]int` parameters refer to different memory, and every verified call must prove it. A call such as `Copy(A, A[1:])` is rejected.

Second, `Modifies A` covers the whole capacity of `A`, not just its length. This is necessary because `append` can write past the length.

The second rule also applies to the slice you pass. `A[:2]` keeps the capacity of `A`, so a function that receives it may write every element of `A`:

```go
// @Modifies A
// @Ensures Forall k in [0, |A|) : A'[k] = 0
func zero(A []int) {
	// @Invariant Forall k in [0, i) : A[k] = 0
	for i := range A {
		A[i] = 0
	}
}

// @Requires |A| = 4
// @Modifies A
// @Ensures A'[3] = A[3]
func ZeroHeadWrong(A []int) {
	zero(A[:2])
}
```

```text
vego: postcondition may not hold: A'[3] = A[3]
```

A full slice expression limits the capacity. With `zero(A[:2:2])` the call cannot reach `A[3]`, and the function verifies.

`append` is supported as the entire right-hand side of an assignment, or as the returned expression.

```go
// @Requires |A| < 1000
// @Modifies A
// @Ensures |result| = |A| + 1 And result[|A|] = x
func Push(A []int, x int) (result []int) {
	return append(A, x)
}
```

`append` does one of two things. If there is spare capacity, it writes into the existing array, and other slices of that array see the write. Otherwise it allocates a new array. `vego` verifies both cases unless it can prove that one cannot happen. `Push` therefore needs `Modifies A` for the first case and a bound on the length for the second.

Slice expressions `A[i:j]` and `A[i:j:k]`, `len`, `cap`, `make`, and slice literals are supported. `copy` and `append(s, t...)` are not supported yet.

## Strings

A string is an immutable sequence of bytes. `vego` supports `|s|`, `s[i]`, `==`, string literals, concatenation, substrings, and conversion to and from `[]byte`.

```go
// @Requires |a| <= 1000 And |b| <= 1000
// @Ensures |result| = |a| + |b|
func Join(a, b string) (result string) {
	return a + b
}

// @Ensures result <-> role = "admin"
func IsAdmin(role string) (result bool) {
	return role == "admin"
}
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

// @Requires c != nil And c.n < c.limit
// @Modifies c.n
// @Ensures c.n' = c.n + 1
func (c *Counter) Inc() {
	c.n++
}
```

A `Modifies` path starts at a parameter. `Modifies c` covers every field of the struct that `c` points to. `Modifies c.n` covers one field, so callers know that `c.limit` is unchanged:

```go
// @Requires c != nil And c.n = 0 And c.limit = 10
// @Modifies c.n
// @Ensures c.n' = 2 And c.limit' = 10
func Twice(c *Counter) {
	c.Inc()
	c.Inc()
}
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

A struct can have a field of a type that `vego` does not support, such as a `sync.Mutex`. Verified code cannot read or assign that field, but it is still part of the struct. Assigning the whole struct writes that field too. For a pointer `h` to such a struct, `*h = H{}` needs `Modifies h`, and entries for the other fields are not enough. A struct with an array field is the exception. It is not supported at all.

### Aliasing

Two pointers can point to the same struct. `vego` does not assume that they are different, so a proof must hold in both cases.

```go
// @Requires a != nil And b != nil
// @Modifies a.n, b.n
// @Ensures result = 1
func SameOrNot(a, b *Counter) (result int) {
	a.n = 1
	b.n = 2
	return a.n
}
```

```text
vego: postcondition may not hold: result = 1
```

If `a` and `b` are the same counter, the function returns 2. Decide whether the function should support that case. If it should, the contract is wrong. If it should not, add `And a != b` to the `Requires` clause, and the function verifies.

Pointers can also point into other memory. A `*Point` can point at an element of a `[]Point` or at a field of a larger struct. To rule that out, write `~within(p, ps)`.

Pointers of two different types can also point to the same struct. Go converts a `*A` to a `*B` when the struct types `A` and `B` have the same fields, so `vego` treats a write through one as a possible write through the other.

### Newly allocated memory

A function can freely write memory that it allocated itself with `&T{...}`, `new`, `make`, a literal, or an `append` that allocated a new array. It can also write its own local variables.

To tell callers that a result is newly allocated, use `fresh`:

```go
// @Ensures fresh(result) And result.n = 0 And result.limit = limit
func NewCounter(limit int) (result *Counter) {
	return &Counter{limit: limit}
}
```

Without `fresh(result)`, a caller must assume that the result could be a counter it already has.

`fresh(x)` means that the memory `x` refers to on return was allocated during the call. `within(a, b)` means that `a` lies inside the memory of `b`. Each argument is a pointer or a slice, and a slice includes its whole capacity. There are two edge cases. A slice with zero capacity has no memory, so it is `fresh` and is `within` anything. A nil pointer is `within` nothing.

`&x`, `&p.field`, and `&s[i]` are supported when the result points to a struct. Methods with pointer receivers can be called on variables, fields, and elements. Pointers to other types, such as `*int`, are not supported.

### A slice that grows inside a struct

A stack that appends to its own slice needs most of the features above.

```go
// @Requires s != nil And s.n = |s.items| And s.n < 1000
// @Modifies s, s.items
// @Ensures s.n' = s.n + 1 And |s.items'| = s.n' And s.items'[s.n] = x
// @Ensures fresh(s.items) Or within(s.items', s.items)
func (s *Stack) Push(x int) {
	s.items = append(s.items, x)
	s.n++
}
```

`Push` assigns the fields `items` and `n`, so it lists `s`. The `append` can write into the capacity of the old slice, so it also lists `s.items`.

The last clause is easy to forget. After `Push` returns, `s.items` can be a different slice from the one the caller listed in its own `Modifies s.items`. Without the clause, a caller that calls `Push` twice gets an error at the second call, because that call may write memory the caller is not allowed to modify. The clause tells the caller where the new slice is. Either it is newly allocated, and anyone may write it, or it lies inside the old slice, which the caller listed.

```go
// @Requires s != nil And s.n = |s.items| And s.n < 100
// @Modifies s, s.items
// @Ensures s.n' = s.n + 2
func PushTwo(s *Stack) {
	s.Push(1)
	s.Push(2)
}
```

Any function that can replace a slice that its callers can reach needs a clause like this. The clause must describe where the new slice actually comes from. For a function that appends, use the clause above. For a function that stores a slice it was given, use `within(s.items', items)`.

Note that the path inside `fresh` is written without a prime, even though it refers to the slice on return.

### What a loop forgets about memory

A loop that writes memory makes `vego` forget what it knew about that memory. How much it forgets depends on how the loop writes.

```go
type Buffer struct {
	items []int
}

// @Requires b != nil
// @Modifies b.items
// @Ensures |result| = 1 And result[0] = |b.items|
func ClearCountedWrong(b *Buffer) (result []int) {
	count := make([]int, 1)
	count[0] = len(b.items)
	for i := range b.items {
		b.items[i] = 0
	}
	return count
}
```

```text
vego: postcondition may not hold: result[0] = |b.items|
```

The loop never writes `count`, but after it `vego` no longer knows `count[0]`. These are the rules:

- If every write in the loop goes through a variable that the loop does not assign, or through a slice that the loop only appends to, `vego` forgets only the memory written that way. It keeps what it knew about all other memory.
- Otherwise `vego` forgets all memory of the same kind that the function may write. For `b.items[i]` that is the elements of every `[]int` the function lists in `Modifies` or allocated itself. Memory of that kind that existed when the function was called and is not in `Modifies` is still known to be unchanged.

`b.items[i]` is not a write through a variable, so the second rule applies. Copy the slice to a local variable first, and only that slice is forgotten:

```go
items := b.items
for i := range items {
	items[i] = 0
}
```

The other way to keep a fact is to state it as a loop invariant, here `// @Invariant count[0] = |b.items|`.

### Where a modifying call can appear

A call to a function that has a `Modifies` clause can stand where any other expression can. Consider a method that changes the stack and also returns a value:

```go
// @Requires s != nil And s.n > 0
// @Modifies s.n
// @Ensures s.n' = s.n - 1 And result = s.items[s.n-1]
func (s *Stack) Pop() (result int) {
	s.n--
	return s.items[s.n]
}
```

It can be an operand, an argument of another call, the condition of an `if` or a `for` loop, the tag of a `switch`, or a `case` expression:

```go
// @Requires s != nil And s.n > 1
// @Requires Forall k in [0, s.n) : 0 <= s.items[k] <= 1000
// @Modifies s.n
// @Ensures result = s.items[s.n-1] + s.items[s.n-2]
func PopSum(s *Stack) (result int) {
	return s.Pop() + s.Pop()
}

// @Requires s != nil And s.n > 0
// @Modifies s.n
// @Ensures result <-> s.items[s.n-1] > 0
func PopInCondition(s *Stack) (result bool) {
	if s.Pop() > 0 {
		return true
	}
	return false
}
```

Go runs the calls in a statement from left to right, so the first `Pop` in `PopSum` takes the top element and the second takes the one below it.

On the right of `&&` and `||`, and in a `case` expression, the call runs only when Go evaluates it there. Where it does not run, `vego` knows that memory is unchanged:

```go
// @Requires s != nil
// @Modifies s.n
// @Ensures s.n = 0 -> s.n' = 0 And ~result
// @Ensures s.n > 0 -> s.n' = s.n - 1
func PopIfAny(s *Stack) (result bool) {
	return s.n > 0 && s.Pop() >= 0
}
```

The precondition of `Pop` only has to hold where `Pop` runs, here when `s.n > 0`.

A call in the condition of a `for` loop is described in [A condition that modifies memory](#a-condition-that-modifies-memory).

### Reads that Go may make before or after a call

Go fixes the order of the calls in a statement, and it runs an operation after its operands. It does not fix when the other operands are read. In `s.n + s.Pop()`, Go may read `s.n` before `Pop` runs or after it:

```go
// @Requires s != nil And 0 < s.n < 1000
// @Requires Forall k in [0, s.n) : 0 <= s.items[k] <= 1000
// @Modifies s.n
func PopAndCount(s *Stack) (result int) {
	return s.n + s.Pop()
}
```

```text
vego: s.n may be read before or after the call to Pop, which may change it, and Go does
not fix the order; split the statement so that the order is the one you mean, as in n := s.n
before it
```

`vego` looks at every read of memory in a statement, and at every read of a variable that a function literal assigns. These are the reads it checks:

- a field, or a whole struct, reached through a pointer, as in `p.n`, `*p`, and the receiver of a method with a value receiver called on a pointer;
- an element of a slice, and the elements that `string(b)` copies;
- an entry of a map, and the number of its keys, `len(m)`;
- a variable whose address is taken;
- a variable that a function literal assigns (see [Variables that a literal assigns](#variables-that-a-literal-assigns)).

For each one that Go may make before or after a call that may change it, `vego` must prove that the read gives the same value either way. It decides this from the `Modifies` and `Ensures` clauses of the call. A local variable whose address is not taken can be changed only by a call of a function literal, and only if some function literal assigns it. Reading any other such variable never conflicts.

Write the order you mean in separate statements:

```go
n := s.n
return n + s.Pop()
```

The message ends with a statement that makes the read first, with a name that is not yet in scope. Put that statement before the one with the read, and use the name in place of the read.

The message has no such statement where moving the read would change when or how often Go makes it. That is the case for a read in these places:

- on the right of `&&` or `||`;
- in a `case` expression;
- in the init statement or the condition of an `else if`;
- in the condition or the post statement of a `for` loop.

It also has none for a read that the message describes in words, such as the receiver of a method. Decide there where the read belongs, and move it yourself.

Some reads do have a fixed order. Go evaluates the arguments of a call before the call, and the left operand of `&&` and `||` before the right one. In `id(s.n) + s.Pop()`, `s.n` is read for `id`, which runs before `Pop`. In `s.Pop() > 0 && s.n > 0`, `s.n` is read after `Pop`.

An assignment evaluates the operands of its targets together with its right-hand side, and assigns only after that. In `c.n = c.Inc()`, the field gets what `Inc` returns. In `a[a[0]] = f(a)`, the index `a[0]` is a read that Go may make before or after `f`.

### An append beside a call

`append` and the other built-in functions are not ordered like calls, because the Go specification does not say that they are. An `append` runs after its operands, and nothing else orders it. So when an `append` writes into the array of its slice, the operands of the targets of the same assignment may be evaluated before or after that write. Reads there are checked like any other read. A call there must not modify anything, and its receiver, parameters, and results must refer to no memory. Integers, floats, booleans, strings, errors, and structs of these refer to no memory. A call that is passed a pointer, a slice, or a map is refused:

```go
// @Requires c != nil
// @Ensures result = c.v
func value(c *Slot) (result int) {
	return c.v
}

// @Requires c != nil And 0 <= c.v < |rows| And |t| = 1
// @Modifies rows, t
func Refill(rows [][]int, t []int, c *Slot) {
	rows[value(c)] = append(t[:0], 5)
}
```

```text
vego: cannot verify Refill: value is called in the target of this assignment, and Go may
call it before or after append writes into the array of t[:0]; assign the result of value to
a variable in a statement of its own first
```

Assign the result first:

```go
i := value(c)
rows[i] = append(t[:0], 5)
```

A call among the operands of the `append`, as in `append(t[:0], five())`, orders the `append` after every call in the targets, and then any call can stand there. An `append` that moves its slice to a new array reads the old elements to copy them, and that read is checked like any other.

## Invariants of structs

A struct type can have an invariant: a formula that every value of the type should satisfy.

```go
// Stack keeps a count that never exceeds what it holds.
//
// @Invariant 0 <= n <= |items|
type Stack struct {
	items []int
	n     int
}

// @Requires s != nil And s.n > 0
// @Ensures result = s.items[s.n-1]
func (s *Stack) Top() (result int) {
	return s.items[s.n-1]
}
```

`Top` can index with `s.n-1` because the invariant bounds `n`.

A struct invariant acts as an extra clause in every contract that involves the type:

- On entry, a function can assume it for every parameter and receiver of the type, or of a pointer to the type.
- On return, the function must prove it for those parameters and for every result of the type.
- At a call, the caller must prove it for every argument. After a call to a verified function, the caller can assume it again for the arguments and results.

This includes a struct passed by value. Its fields are a copy, but a slice in it shares its array with the caller. If the function writes through that slice, it must still prove the invariant on return. A write of `-1` to `b.items[0]` is reported when the invariant of `b`'s type says that `items[0] >= 0`.

Between those points, a function can break the invariant temporarily. An invariant cannot be turned off for a single function. If a helper has to run while the invariant is broken, pass it the fields it needs and not the struct.

The invariant applies in fewer places than you might expect. There are three limits.

### It applies only to direct parameters and results

`vego` does not assume or check the invariant for a struct inside a slice, a map, or another struct, or for one behind a pointer field. State it explicitly where you need it. For example, take this type:

```go
// @Invariant 0 <= balance <= 1000000
type Account struct {
	mu      sync.Mutex
	balance int
}
```

A function that takes a slice of accounts must state the bound for each element:

```go
// @Requires |as| <= 100
// @Requires Forall k in [0, |as|) : as[k] != nil And 0 <= as[k].balance <= 1000000
func Total(as []*Account) (result int) {
```

### A loop does not keep it

A loop forgets the struct invariant along with everything else about the memory it changes. If a loop calls a method on a struct, repeat the struct invariant as a loop invariant:

```go
// @Requires s != nil
// @Modifies s.n
// @Ensures s.n' = 0
func Drain(s *Stack) {
	// @Invariant 0 <= s.n <= |s.items|
	// @Variant s.n
	for s.n > 0 {
		s.Pop()
	}
}
```

Without the `Invariant` line, `vego` reports `invariant of Stack may not hold for what is passed to Pop as s`. The call to `Pop` needs the invariant of `Stack` to hold. After the first iteration, nothing establishes it.

### A trusted function does not restore it

After a call to a trusted function that may modify a struct, `vego` does not assume the invariant of that struct, because nothing proved it.

## Maps

A map is a reference, like a pointer. Two map variables can refer to the same map, and a function that writes a map must list it in `Modifies`.

In a formula, `m[k]` is the value stored under `k`, or the zero value if the key is absent, as in Go. `has(m, k)` is true if the key is present. `|m|` is the number of keys.

```go
// @Ensures ok <-> has(m, k)
// @Ensures v = m[k]
func Get(m map[string]int, k string) (v int, ok bool) {
	v, ok = m[k]
	return v, ok
}

// @Requires m != nil And m[k] < 1000
// @Modifies m
// @Ensures has(m', k) And m'[k] = m[k] + 1
func Bump(m map[string]int, k string) {
	m[k] = m[k] + 1
}
```

Keys must be integers or strings. Writing to a map requires a proof that the map is not nil. Reading from a map and calling `delete` do not.

The keys of a map literal must be different. Go rejects two equal constant keys, and `vego` must prove that any other two keys differ. Go does not fix the order in which a literal puts its entries into the map, so when two keys are equal, either value may be kept:

```go
// @Ensures True
func Pair(a, b int) (result map[int]int) {
	return map[int]int{a: 1, b: 2}
}
```

```text
vego: the keys a and b of this map literal may be equal, and Go does not fix which of their
entries the map keeps; build the map with assignments instead
```

Add `Requires a != b`, or assign the entries one by one, which runs in order.

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

`vego` knows two things about an error value: whether it is `nil`, and which error it is. It knows that `errors.New` and `fmt.Errorf` return non-nil errors. It also knows that such an error differs from every error variable and from the other errors the function makes.

A package-level variable of type `error` that nothing assigns after it is initialised holds the same error for as long as your code runs, as in `var ErrEmpty = errors.New("empty")`. This guide calls such a variable an error variable. The error variables of other packages count too, such as `io.EOF`. What `vego` knows of the error depends on the initialiser of the variable. [What vego knows of an error variable](#what-vego-knows-of-an-error-variable) describes the cases, and [When a package-level error is known](#when-a-package-level-error-is-known) gives the exact conditions.

### Saying when a function succeeds

A function that returns an error must state when it succeeds.

```go
var ErrEmpty = errors.New("empty")

// @Ensures err = nil <-> |A| > 0
// @Ensures err = nil -> first = A[0]
func Head(A []int) (first int, err error) {
	if len(A) == 0 {
		return 0, ErrEmpty
	}
	return A[0], nil
}
```

The second clause alone is not enough:

```text
vego: the contract of HeadWeak may also be met by a function that always returns an
error: no simple input was found for which it forces success; state when it succeeds
with a clause such as "condition -> err = nil", where the condition is about the
inputs and a small input satisfies it
```

A contract that only says "if the function succeeds, then ..." is also satisfied by a function that always fails. `vego` rejects such contracts because they are easy to write by accident and guarantee nothing.

To decide, `vego` searches for one example input. The input must satisfy the `Requires` clauses, and the `Ensures` clauses must then force every error result to be `nil`. The examples have a simple shape:

- slices in which every element is the same, or the slice literals in the contract;
- strings of one repeated byte, or the string literals in the contract;
- pointers to structs, followed at most two levels deep;
- maps with a single key, whose value can be a pointer to a struct.

Z3 picks the numbers in an example: lengths, elements, fields, and keys. It also picks each error. An error in an example is `nil`, an error of its own, the same error as another error of the example, or an error variable that the contract names. `vego` then proves both facts about the example before it accepts it.

When Z3 shows that no input at all can force success, the message says `it requires success for no input` instead. The contract then needs a clause that says when the function succeeds.

The search is enough for most contracts. If your contract does state when the function succeeds and you still get `no simple input was found`, there are two possible causes. Either every succeeding input lies outside the shapes above, for example because success needs a slice with two different elements. Or the prover could not show that a suitable example satisfies the `Requires` clauses or that the `Ensures` clauses force success. That can happen when the clauses involve non-trivial arithmetic.

In both cases, add a clause that some simple input clearly satisfies, such as `|A| = 0 -> err = nil`. An `Assert` cannot help, because this check does not involve the function body.

### Saying which error a function returns

A contract can say which error a function returns.

```go
// @Ensures err = nil <-> |A| > 0
// @Ensures err = ErrEmpty <-> |A| = 0
// @Ensures err = nil -> first = A[0]
func Peek(A []int) (first int, err error) {
	if len(A) == 0 {
		return 0, ErrEmpty
	}
	return A[0], nil
}
```

In a formula, `err = ErrEmpty` means that `err` is the same error as `ErrEmpty`. This is what `err == ErrEmpty` tests in Go. A contract can name the error variables of its own package, and those of an imported package by the package name, as in `io.EOF`.

The second clause alone does not say when `Peek` succeeds. A function that returns `ErrEmpty` for an empty slice and another error otherwise would meet it, so the first clause is still needed. See [Saying when a function succeeds](#saying-when-a-function-succeeds).

A caller can compare the error with the error variable:

```go
// @Ensures v = 0 <-> (|A| = 0 Or A[0] = 0)
func PeekOrZero(A []int) (v int) {
	first, err := Peek(A)
	if err == ErrEmpty {
		return 0
	}
	return first
}
```

The same works with an error variable of another package:

```go
// @Requires 0 <= i
// @Ensures err = nil <-> i < |s|
// @Ensures err = io.EOF <-> i >= |s|
// @Ensures err = nil -> b = s[i]
func Next(s string, i int) (b byte, err error) {
	if i >= len(s) {
		return 0, io.EOF
	}
	return s[i], nil
}

// @Requires 0 <= i
// @Ensures end <-> i >= |s|
func AtEnd(s string, i int) (end bool) {
	_, err := Next(s, i)
	return err == io.EOF
}
```

A `switch` on an error works the same way, as in `switch err { case io.EOF: ... }`.

### Comparing errors

Go's `==` on two error values panics when both hold the same type and that type is not comparable, such as a slice type with an `Error` method. So `vego` accepts `==`, `!=`, and the cases of a `switch` on errors only when one of the two errors is one of these:

- `nil`;
- an error made by `errors.New` or `fmt.Errorf`, here or in a verified function that returns nothing else;
- an error that a trusted contract vouches for, as described in [Errors that a trusted function returns](#errors-that-a-trusted-function-returns);
- an error variable, of this package or another, that holds such an error;
- an error variable whose initialiser has a pointer, integer, string, or boolean type, or an array or struct type made only of these, as described in [What vego knows of an error variable](#what-vego-knows-of-an-error-variable).

A comparison with `nil` cannot panic. The errors that `errors.New` and `fmt.Errorf` make are pointers, so a comparison with them cannot panic either. Comparing two errors of which nothing is known is reported:

```go
// @Ensures True
func SameError(a, b error) (same bool) {
	return a == b
}
```

```text
vego: cannot verify SameError: comparing two errors can panic when both hold the same
uncomparable type; one of them must be nil, an error made by errors.New or fmt.Errorf or
vouched for by a trusted contract, or a package-level error variable that holds such an
error or a pointer, integer, string, or boolean, or an array or struct of these
```

Compare one of them with an error variable instead.

`vego` knows that a new error differs from every error variable and from every other error the function made. It does not know that a new error differs from an error that was passed in, or that a call made before returned, although in Go it always does.

### Asking errors.Is

`errors.Is(err, target)` reports whether `err`, or an error that `err` wraps, is `target` or has an `Is` method that reports true for `target`. In a formula, `is(err, target)` means that `errors.Is(err, target)` reports true.

```go
// @Ensures err = nil <-> |A| > 0
// @Ensures is(err, ErrEmpty) <-> |A| = 0
func PeekLabelled(A []int) (first int, err error) {
	first, err = Peek(A)
	if err != nil {
		return 0, fmt.Errorf("peek: %w", err)
	}
	return first, nil
}

// @Ensures empty <-> |A| = 0
func Empty(A []int) (empty bool) {
	_, err := PeekLabelled(A)
	return errors.Is(err, ErrEmpty)
}
```

`vego` knows what `errors.Is` finds in an error made by `errors.New` or `fmt.Errorf`. It finds the error itself and, when `fmt.Errorf` wraps an error with `%w`, whatever it finds in the wrapped error. `%v` does not wrap, so with `%v` in place of `%w` in `PeekLabelled` the contract is not proved:

```go
return 0, fmt.Errorf("peek: %v", err)
```

```text
vego: postcondition may not hold: is(err, ErrEmpty) <-> |A| = 0
```

To know what an error wraps, `vego` reads the format of `fmt.Errorf`. It does not know what `errors.Is` finds in the error when the call has an error operand and the format has any of these:

- the format is not a constant;
- it has more than one `%w`;
- it has an argument index, as in `%[1]w`, or a width or precision taken from an operand, as in `%*d`;
- it has a width or precision of seven digits or more.

Such an error still has a known origin. It can be returned, compared, and formatted as before. A claim about what `errors.Is` finds in it is not proved, whether the claim says that `errors.Is` finds the target or that it does not.

The same holds for an error variable made by `fmt.Errorf`. `vego` knows what `errors.Is` finds in `var ErrRead = fmt.Errorf("read: %w", io.EOF)`, also in other packages.

For an error that a verified function returns, the caller knows only what the function's contract says. The contract of `PeekLabelled` says nothing about `ErrRange`. When the slice is empty, a caller can therefore prove neither that `errors.Is(err, ErrRange)` is true for its error nor that it is false.

`errors.Is` calls the `Is` and `Unwrap` methods of the error it searches. That error must therefore have a known origin, in the same sense as for formatting. See [Wrapping errors](#wrapping-errors). The target can be any error, because `errors.Is` calls no method of the target.

```go
// @Ensures True
func IsEmpty(err error) (result bool) {
	return errors.Is(err, ErrEmpty)
}
```

```text
vego: cannot verify IsEmpty: errors.Is would run the Is and Unwrap methods of err, an
error whose origin is not known; only an error made by errors.New or fmt.Errorf, here or
in a verified function, or one that a trusted contract vouches for, can be its first
argument
```

An error that a trusted function returns has no known origin unless the contract of the function vouches for it. See [Errors that a trusted function returns](#errors-that-a-trusted-function-returns). Without that, `errors.Is(err, io.EOF)` on it is reported. You can compare it with `==` instead, as in `err == io.EOF`, which runs no method. That comparison is true only when the function returned `io.EOF` itself, and not when it returned an error that wraps `io.EOF`.

The shipped contracts of `strconv.Atoi` and `os.Remove` vouch for their errors. The contract of `strconv.Atoi` also says that a failure is a syntax error or a range error, and which number comes with each:

```go
// @Ensures err = nil Or is(err, strconv.ErrSyntax)
func Nearest(s string) (n int, err error) {
	n, err = strconv.Atoi(s)
	if errors.Is(err, strconv.ErrRange) {
		return n, nil
	}
	return n, err
}
```

The contract of `os.Remove` says nothing about which error it returns. Its error can still be searched:

```go
// @Ensures ~is(err, os.ErrNotExist)
func RemoveIfPresent(name string) (err error) {
	err = os.Remove(name)
	if errors.Is(err, os.ErrNotExist) {
		return nil
	}
	return err
}
```

This is proved because `os.ErrNotExist` is not nil, so `errors.Is` does not find it in `nil`. See [What vego knows of an error variable](#what-vego-knows-of-an-error-variable).

### Functions that cannot promise success

Some functions cannot say when they succeed, because their success depends on a call whose contract does not say what it returns.

```go
// @Ensures err = nil -> 1 <= port <= 65535
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
```

The contract of `strconv.Atoi` does not say which strings it accepts. `ParsePort` therefore cannot promise success for any input, and `vego` does not require it to. The same applies to functions that read a file or use the network.

`vego` excuses a function only when such a call decides between success and failure. At least one `return` of an error and one `return` without an error must each depend on what the call returned. In `ParsePort`, the first `return` passes on the error of `strconv.Atoi`, and `return n, nil` is reached only after a test of `n`. A function that ignores what the call returned is not excused. Neither is a function that returns an error whatever the call returned.

The call can be to a trusted function whose contract does not say when it succeeds, or to a verified function that is excused in the same way.

`vego` follows what the call returned through variables, through loops, through memory that the function reads, and into later calls that it is passed to. It does not follow it through memory that a later call reads or that a loop writes. If the function depends on the call only in that way, `vego` reports the contract, and the function has to be restructured.

This check can miss a weak contract. When the path to the call depends on values `vego` does not know, such as the result of an earlier call, `vego` assumes that the path can be taken. A call that is never reached, or one that always succeeds for reasons `vego` cannot see, can then excuse a contract that says too little.

### Wrapping errors

`fmt.Errorf` can format numbers, booleans, strings, and slices of them, when their types have no methods. It can also format an error of known origin. An error has a known origin in two cases:

- It was made by `errors.New` or `fmt.Errorf`, in verified code or in the initialiser of an error variable of any package, and nothing went into it but such values and other errors of known origin. `io.EOF` is one.
- A trusted contract vouches for it, as described in [Errors that a trusted function returns](#errors-that-a-trusted-function-returns). A verified function that returns such an error passes the known origin on to its callers.

A value whose type has methods, such as a string type with a `String` method, is rejected, because formatting it may call them.

It cannot format an error that came from a parameter, or from a trusted function whose contract does not vouch for it. Formatting an error calls its methods, and `vego` cannot see what the methods of an unknown error do. For the same reason, such an error cannot be passed to a trusted function unless that function's contract allows it. See [Arguments that carry code](#arguments-that-carry-code).

The shipped contract of `strconv.Atoi` vouches for its error, so its error can be wrapped:

```go
var ErrTooMany = errors.New("too many")

// @Ensures err = nil -> 0 <= n <= 1000
// @Ensures err = nil Or err = ErrTooMany Or is(err, strconv.ErrSyntax) Or is(err, strconv.ErrRange)
func ParseQuantity(line string) (n int, err error) {
	n, err = strconv.Atoi(line)
	if err != nil {
		return 0, fmt.Errorf("bad quantity %q: %w", line, err)
	}
	if n < 0 || n > 1000 {
		return 0, ErrTooMany
	}
	return n, nil
}
```

The second clause is proved because `%w` keeps what `errors.Is` finds in `err`, and the contract of `strconv.Atoi` says that its error is a syntax error or a range error.

An error that was passed in is rejected:

```go
// @Ensures err != nil
func Labelled(cause error) (err error) {
	return fmt.Errorf("load: %w", cause)
}
```

```text
vego: cannot verify Labelled: formatting cause would run the methods of an error whose
origin is not known; only an error made by errors.New or fmt.Errorf, here or in a
verified function, or one that a trusted contract vouches for, can be formatted
```

Return the error unchanged, or wrap an error of your own:

```go
return fmt.Errorf("load: %w", ErrMissing)
```

### Other limits

These are not supported, and a function that uses one is reported as `cannot verify`:

- `errors.As`, which needs typed errors;
- `errors.Join` and `errors.Unwrap`;
- `errors.Is` on an error that came from a parameter, or from a trusted function whose contract does not vouch for it;
- an error variable that its package assigns or takes the address of.

A struct invariant cannot name an error variable.

Only an error or `nil` can be converted to `error`. A value of another type is rejected even if it has an `Error` method:

```go
type CodeError struct{ code int }

func (e CodeError) Error() string { return "code " + strconv.Itoa(e.code) }

// @Ensures err != nil
func AsError() (err error) {
	return CodeError{code: 1}
}
```

```text
vego: cannot verify AsError: converting a guide.CodeError to an error is not supported
```

### When a package-level error is known

An error variable of your own package holds the error it was declared with under these conditions. Nothing in the package assigns to it or takes its address. And no code in the package can run before the variable is initialised.

Go initialises the variables of a package in an order it works out from their dependencies. Code of the package can still run earlier if an initialiser hands something to code that Go's ordering does not see. The package then loses what it knew about all its error variables. That happens when the initialiser of any package-level variable does one of these things:

- calls a function value or an interface method;
- ranges over a function;
- starts a goroutine;
- passes something of the package to a function of another package, as an argument or a type argument;
- assigns to anything other than a plain variable;
- sends on a channel;
- passes something of the package to `append`, `copy`, or `panic`.

A value whose type cannot hold code, such as a number or a string, does not count. `vego` reports the error where the variable is read, or named in a contract, and names what ran:

```text
vego: cannot verify Ok: ErrX is not known to have its value yet when this runs: a function
value or an interface method is called at early.go:24 while the variables of the package
are initialised, which may run this function first
```

An error variable that the package assigns, or whose address it takes, is reported where it is read:

```text
vego: cannot verify UnreliableSentinel: ErrReassigned is assigned at values.go:16, so it is
not known to hold the error it was declared with
```

For an error variable of another package, only the first condition matters. Go initialises a package before any code of the packages that import it runs. `vego` reads the source of every package your package is built with, the standard library included. So `io.EOF` holds the error it was declared with in your package because nothing in package `io` assigns to it.

A package can also assign to an error variable of another package. A package that does so cannot rely on that variable:

```text
vego: cannot verify Gone: gonelib.ErrGone is changed at gonemid.go:6 in package gonemid,
which this package is built with, so it is not known to hold the error it was declared with
```

Your package gets this message when it is built with the package that assigns, directly or through another package. It gets it as well when the variable that is assigned went into the error variable that your package reads, as `io.EOF` goes into `fmt.Errorf("read: %w", io.EOF)`.

A variable that holds another error variable is not affected when that variable is changed. It holds the value the other variable had when it was initialised, and `vego` knows only that it is the same error each time it is read.

A proof in another package may rely on the variable all the same. `laas` reports the assignment in every package it runs on that is built with both the assignment and that proof:

```text
vego: gonelib.ErrGone may be changed here, but proofs in package gonelib rely on it being
the error it was declared with
```

```text
vego: gonelib.ErrGone is changed at gonemid.go:6 in package gonemid, which this package is
built with, but proofs in package gonelib rely on it being the error it was declared with
```

The first message is at the assignment, in the package that assigns. The second is at the `package` clause of a package that imports both, directly or not.

An assignment in a package that is not in the build of any package `laas` runs on is not seen. See [What a proof assumes](#what-a-proof-assumes).

### What vego knows of an error variable

`vego` reads the initialiser of each error variable. There are three cases.

The first is a call of `errors.New` or `fmt.Errorf`, as in `var ErrEmpty = errors.New("empty")`. The error is not nil. It differs from the error of every other such variable and from every error made in the body of the function being verified. `vego` knows what `errors.Is` finds in it, and it can be formatted if nothing of unknown origin went into it. See [Wrapping errors](#wrapping-errors).

The second is another error variable, as in `var ErrNotFound = os.ErrNotExist`. The variable is then the same error as that one, and `vego` knows of it what it knows of that one. The same holds for a call of a function of the same package that takes no arguments and whose body is only `return` of an error variable. `fs.ErrNotExist` is set this way to `oserror.ErrNotExist`, which `errors.New` makes, and `os.ErrNotExist` holds `fs.ErrNotExist`. So `vego` knows that the three are one error made by `errors.New`.

The third is anything else, such as `var DeadlineExceeded error = deadlineExceededError{}` in package `context`. `vego` knows only that the variable holds the same error each time it is read. Such a variable can be the target of `errors.Is`, and a contract can name it. It cannot be formatted, and it cannot be the first argument of `errors.Is`, because its methods are not known. Two more facts come from the type of the initialiser:

- If the type is not an interface type, the variable is not nil. This is true even of a nil pointer of a concrete type, which makes a non-nil error.
- If the type is a pointer, integer, string, or boolean type, or an array or struct type made only of these, the variable can be compared with any error. On such a type `==` cannot panic, and it reports true exactly when the two values are the same. Other types are excluded. On an interface, slice, map, or function type `==` can panic, and on a float type it reports false for a NaN compared with itself.

`context.DeadlineExceeded` is not nil and can be compared with any error. An error made in the body of the function being verified differs from it, because a new error is new memory, which no variable held before. `vego` does not know that an error that a call returned differs from it.

These variables are of the third kind too:

- a variable that holds another error variable that its package assigns, or that a package in the build changes;
- a variable set by a call that does more than return an error variable, or that passes arguments, as in `var ErrBad = newError("bad")`.

`vego` does not know whether such a variable is nil, unless the type of its initialiser says so as above. It does not know whether it is the same error as another error variable, or what `errors.Is` finds in it. A proof that needs one of these facts fails with `postcondition may not hold` or a similar message, and nothing says that the variable is the reason. If a proof fails where it uses an error variable of another package, read the initialiser of that variable.

## Defer

`vego` verifies a deferred call at the point where it runs. That is at every `return` of the function, after the results have been set. Deferred calls run in reverse order.

```go
type Lock struct{ held bool }

// @Requires l != nil And ~l.held
// @Modifies l
// @Ensures l.held'
func (l *Lock) Acquire() {
	l.held = true
}

// @Requires l != nil And l.held
// @Modifies l
// @Ensures ~l.held'
func (l *Lock) Release() {
	l.held = false
}

// @Requires l != nil And ~l.held And c != nil And c.n < c.limit
// @Modifies l, c.n
// @Ensures ~l.held'
func Guarded(l *Lock, c *Counter, skip bool) {
	l.Acquire()
	defer l.Release()
	if skip {
		return
	}
	c.Inc()
}
```

`Guarded` returns in two places. At each one, `vego` proves the `Requires` clause of `Release` and then applies its effect. As in Go, the receiver and arguments of a deferred call are evaluated at the `defer` statement.

What a deferred call changes is part of what the `Ensures` clauses describe. A deferred call can also change a result, as Go allows, when it is passed a pointer to a named result of struct type, as in `defer set(&out)`.

A function literal can be deferred too. It runs at each `return`, after the results have been set, so it can change a named result:

```go
// @Requires c != nil And c.n < c.limit
// @Modifies c.n
// @Ensures result = c.n'
func IncAndRead(c *Counter) (result int) {
	defer func() { result = c.n }()
	c.Inc()
	return 0
}
```

The arguments of a deferred literal are evaluated at the `defer` statement. The variables it uses are read when it runs. See [Function literals](#function-literals) for what else applies to its body.

`defer` inside a loop is not supported, because the number of calls it puts off is not known. A `defer` inside a function literal that the loop calls is supported, because it runs when the literal returns:

```go
// @Requires l != nil And ~l.held And 0 <= n <= 10
// @Modifies l
// @Ensures ~l.held'
func Rounds(l *Lock, n int) {
	// @Invariant ~l.held
	for range n {
		func() {
			l.Acquire()
			defer l.Release()
		}()
	}
}
```

A call through a function value of a type with a contract can be deferred too. See [Function values](#function-values). `defer cancel()` after `context.WithCancel` cannot be verified yet, because `context.Context` is an interface and `context.CancelFunc` has no contract.

`recover` is not supported, because it returns an interface. Call it in a function that is not verified.

### Locks

`vego` has no contract for `sync.Mutex`, and you should not write the obvious trusted one, with no conditions. `Lock` blocks forever if the goroutine already holds the mutex. `Unlock` crashes the program if the mutex is not locked. A contract without a condition on the lock's state would claim that both calls always return, and `vego` would then accept a double `Lock` or an `Unlock` without a `Lock`. The condition cannot be stated in a portable way. A formula could only refer to the private fields of the mutex, which would tie the contract to one version of Go.

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

// @Requires a != nil And 0 <= n And a.balance + n <= 1000000
// @Modifies a.balance
// @Ensures a.balance' = a.balance + n
func (a *Account) deposit(n int) {
	a.balance += n
}
```

A struct used by verified code can contain a mutex. Verified code cannot call `Lock` or `Unlock`, and should not touch the field.

The proof of `deposit` shows that it is correct when one goroutine runs it. Keeping other goroutines out is the job of `Deposit`, and that part is not proved.

## Bits

`vego` computes with integers, not bits. It handles shifts and bitwise operators by translating them to arithmetic.

```go
// @Ensures result = 256 * hi + lo
func Pack(hi, lo byte) (result uint16) {
	return uint16(hi)<<8 | uint16(lo)
}
```

The translation works as follows.

- `x << k` is `x * 2^k`. It must not lose bits, which is checked like any other overflow.
- `x >> k` is `x / 2^k`, rounded down. This also holds for negative `x`.
- A shift count that may be negative is an error.
- `x & m`, where `m` is a constant mask of low bits, is a remainder. For non-negative `x`, `x & 0xFF` equals `x % 256`. For negative `x` the result is still non-negative, so `-1 & 0xFF` is 255, while `-1 % 256` is -1.
- `x & m`, where `m` is a single bit, is that bit of `x`.
- For `x & y` in general, only bounds are known. A few simple cases are exact, such as `x & x` and `x & 0`.
- `x | y`, `x ^ y`, and `x &^ y` are computed from `x & y`. They are known exactly when `x & y` is.
- If both operands fit in some number of bits, the result of `&`, `|`, or `^` fits in as many.
- After `f |= m`, `vego` knows that `f & m` equals `m`. After `f &^= m`, it knows that `f & m` is 0.
- `^x` is `-x - 1`. For an unsigned type it is the largest value of the type minus `x`.

These are the facts the prover starts from. It cannot always derive every consequence of them.

Formulas have no bit operators. Use `*`, `/`, and `%` in contracts.

## Code that is not verified

Verified code often has to call code that is not verified. This includes the standard library, other modules, and your own functions that use Go `vego` does not support. To make such a function callable, give it a trusted contract. `vego` uses a trusted contract without checking it.

All trusted contracts for a module are in one file, `vego-trusted.yaml`, next to `go.mod`. Trust cannot be declared in source code, so this file contains every trusted contract that your module adds.

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
| `runs` | no | Parameters that carry code the function may call, at any depth inside the value. See [Arguments that carry code](#arguments-that-carry-code). |
| `vouches` | no | Error results whose errors verified code may format, compare, and pass to `errors.Is`, and results that hold function values verified code may call. See [Errors that a trusted function returns](#errors-that-a-trusted-function-returns) and [Function values that a trusted function returns](#function-values-that-a-trusted-function-returns). |

Put the formulas in quotes. Several characters that formulas use have a special meaning in YAML.

The names in an entry are the parameter and result names from the function's source, including the receiver. For the standard library, `go doc -src bytes.Buffer.Len` shows that the receiver is called `b`. If the function does not name its results, use `result` for a single result, or `result1`, `result2`, and so on for several. This applies only to trusted contracts, because a verified function must name its results.

### Shipped contracts

`vego` includes contracts for a few standard library functions:

- `sort.Ints`, `sort.IntsAreSorted`, `sort.SearchInts`
- `strings.Contains`, `strings.HasPrefix`, `strings.HasSuffix`, `strings.Index`, `strings.TrimSpace`, `strings.Repeat`, `strings.ToUpper`, `strings.ToLower`
- `unicode/utf8.RuneCountInString`
- `strconv.Itoa`, `strconv.Atoi`
- `os.Remove`
- `math/rand.Intn`, `math/rand.Int`

The contracts are in `vego/trusted/std` in the source of `laas`. They state only behaviour that the function's documentation promises, and the tests of `vego` check each one against the real function. The contracts of `strconv.Atoi` and `os.Remove` vouch for their errors. For those, the tests also check that every error in the tree of a returned error has a type whose methods were read against what `vouches` claims. An entry in your own file with the same key replaces the shipped contract.

### What is checked in an entry

`vego` does not check that a trusted contract is true. It checks these things about each entry:

- The function exists.
- Every name in a formula is a parameter or result of the function, of a type that a contract can use, or an error variable. An error variable is named as described in [Error variables in a trusted contract](#error-variables-in-a-trusted-contract). It must exist, its package must be in the build, and the calling package must be able to rely on it as described in [When a package-level error is known](#when-a-package-level-error-is-known).
- Every name under `vouches` is a result of the function of type `error`, listed once.
- `modifies` is present and lists only memory that a caller can see. A parameter passed by value is not such memory.
- A primed path in `ensures`, such as `xs'[0]`, reads memory of a kind that `modifies` lists. The call cannot change any other memory.
- The contract does not contradict itself.

An entry for a function that does not exist is reported in the trust file. An entry that fails one of the other checks cannot be used, and `vego` reports the reason at each call to the function. An entry that no verified code calls is not checked, so the trust report lists it as unused even if it has a defect. If a single entry cannot be read at all, for example because it has no `modifies` list or repeats a field, no entry of the file is used.

At each call, `vego` also checks whether what the contract promises contradicts what is known at that point. A contradiction would make everything after the call provable, so it is reported as `the trusted contract of F cannot be true of this call`. This check is quick and can miss a contradiction that is hard to find.

A trusted function in your own package can call back into the verified function that called it, by name, through a function value, or through an interface method. `vego` reads the body of the trusted function to find this, and reports it:

```text
vego: bounce is trusted and calls back into Bounced, so that this call ends cannot be
proved; verify bounce instead of trusting it
```

A call back by way of another package is not found. See [What a proof assumes](#what-a-proof-assumes).

### Arguments that carry code

A trusted contract describes what the function's own code does. Some arguments bring code with them. An `error` has methods, and their code is chosen by whoever created the error. The same is true of other interface values. A struct can have a field that holds a function, and the value can be nested at any depth inside a struct, slice, or map. A trusted function could call that code, for example `err.Error()` or `l.sink(text)`, and the code could write memory that your proof depends on.

For this reason `vego` refuses to pass such a value to a trusted function:

```text
vego: cannot verify TellsUnknown: e is passed to tell, which is trusted, and is an error
whose origin is not known; tell could run code through it that nobody has seen. If its
contract holds whatever that code does, list e under runs in the contract
```

There are three ways to deal with this.

The first is to pass an error that verified code created with `errors.New` or `fmt.Errorf`, or one that a trusted contract vouches for. An error that verified code created has only the standard library's methods and wraps nothing from outside. An error variable also qualifies if its initialiser used only plain values and other errors of this kind, in its own package or another. `var ErrRead = fmt.Errorf("read: %w", io.EOF)` qualifies. `var ErrLate = fmt.Errorf("late: %w", context.DeadlineExceeded)` does not, because `context.DeadlineExceeded` is not made by `errors.New` or `fmt.Errorf`.

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

`runs` also claims three things about when the function runs the code it receives, whatever kind of code that is:

- It runs the code only before it returns.
- It runs the code only on the goroutine that called it.
- It keeps no value that can hold code once it returns, in memory or anywhere else.

A function that stores a callback and calls it later, such as one that registers a handler, makes these claims false. Do not list its parameter under `runs`. Call it from code that is not verified.

When the parameter can hold a function value of a type with a contract (see [Function values](#function-values)), `runs` claims that the function calls such a value only with arguments that meet the `Requires` clauses of its type. The rest of the claim then has to hold only for values that meet the contract of their type, and every value that verified code passes does. For any other code, the claim has to hold whatever code arrives.

The trust report shows `runs`, so that a reviewer of the trust file notices the larger claim.

### Errors that a trusted function returns

Without a claim in its contract, `vego` knows nothing about the methods of an error that a trusted function returns. Verified code can return such an error and compare it with `nil` or with an error variable of the kinds listed in [Comparing errors](#comparing-errors). It cannot format it, wrap it, or pass it as the first argument of `errors.Is`. To allow these, list the error result under `vouches`:

```yaml
  example.com/shop/internal/scan.next:
    reason: Returns io.EOF at the end of s and no other error; reviewed 2026-11-19.
    requires: ["0 <= i"]
    vouches: [err]
    modifies: []
    ensures:
      - "err = nil <-> i < |s|"
      - "err != nil -> err = io.EOF"
      - "err = nil -> b = s[i]"
```

With `vouches: [err]`, an error that the function returns in `err` has a known origin. Verified code can format it, wrap it with `%w`, ask `errors.Is` about it, compare it with any error, and pass it to another trusted function. A verified function that returns it passes the claim on to its callers. `vego` knows what `errors.Is` finds in the error only from what the contract says, as in `err = io.EOF` above.

`vouches` is a claim about code that `vego` does not read. Before you make it, read the source of the function and of every error type it can return. The claim is about every non-nil error that the function returns in a listed result. It covers every error in the tree of that error, which is what `Unwrap` returns from it, and from that again. It also covers every value that these errors hold. You claim three things:

- Every method of these values returns without panicking and writes nothing that a caller can see, whatever arguments it is passed. This covers `Error`, `Is`, `Unwrap`, and the methods that `fmt` calls when it formats a value. An `Is` method must not call a method of its argument, because the argument can be any error.
- `==` on these errors cannot panic, and it reports true only for two errors that are the same. Every one of them equals itself. `errors.Is` reports the same for two such errors that `==` reports equal, and the same for two targets that `==` reports equal.
- What `errors.Is` reports for one of these errors and a given target does not change after the function returns.

A pointer to a struct meets these conditions when its methods only read its fields and call the same methods of the errors it holds, those errors meet the conditions themselves, and nothing writes the fields after the function returns. The function must not keep the pointer and change the struct later. An integer type whose `Is` method only compares its argument with error variables, such as `syscall.Errno`, also meets them. A type with a float in it does not, because `==` reports false for a NaN compared with itself. An `Is` method that calls `target.Error()` does not either.

If the function returns an error that it was given, the claim covers that error too. With `runs`, the claim must hold whatever value is passed. The trust report shows `vouches`.

### Function values that a trusted function returns

A function value that a trusted function returns is code that the author of the contract may not have read. If a result can hold a function value of a type with a contract, at any depth, the entry must list the result under `vouches`. Otherwise the entry cannot be used, and each call reports:

```text
the trusted contract of F cannot be used: its result m can hold a function value of a type
with a contract; list it under vouches to claim that every such value meets the contract of its type
```

With `vouches: [m]`, you claim that every such function value in `m` meets the contract of its type. The claim also covers the values in memory that `m` reaches and that the function allocated or wrote during the call. An entry whose `modifies` covers memory that can hold such a value, at any depth, cannot be used yet.

### Error variables in a trusted contract

A trusted contract can name error variables, as in `err = io.EOF` and `is(err, io.EOF)`. The contract means the same in every package that calls the function, so its names do not depend on what any file imports:

- A name on its own is an error variable of the package that declares the function, such as `ErrSyntax` in an entry for `strconv.Atoi`.
- A name after the import path of its package is an error variable of that package. Write a path that is a Go identifier as in Go, as in `io.EOF`. Put any other path in quotes, as in `"io/fs".ErrNotExist` or `"example.com".ErrRoot`. YAML then needs the formula in single quotes: `'is(err, "io/fs".ErrNotExist)'`.

The package must be in the build of the package that calls the function. An entry that names a variable that does not exist, or a package that is not in the build, cannot be used. Only a trusted contract can use a path in quotes. The annotations of a verified function name packages as their file imports them.

### Limits of trusted contracts

A trusted contract does not make an unsupported signature callable. If a function has a parameter or result of an unsupported type, such as an interface, verified code cannot call it even with an entry. The message is `cannot verify Sync: parameter s has unsupported type example.com/shop.Store`. Write a small wrapper whose signature uses only supported types, and trust the wrapper.

A function cannot have both annotations and a trusted contract. When you verify a function that you previously trusted, delete its entry.

`vego` knows nothing about the results of a trusted function beyond what the contract states. For example, a returned pointer or slice could refer to any memory unless the contract restricts it, for example with `fresh(result)`.

### The trust report

This command prints every trusted contract the proofs use, with its reason and the places that call it:

```sh
laas -vego.trust ./...
```

The report has three lists:

- the contracts from your trust file that the proofs use;
- the shipped contracts that the proofs use;
- the entries in your trust file that no proof uses.

An entry that lists parameters under `runs` or results under `vouches` shows them in the lines `runs code held by:` and `vouches for the errors and function values in:`. Each is a claim about code that `vego` does not read. See [Arguments that carry code](#arguments-that-carry-code) and [Errors that a trusted function returns](#errors-that-a-trusted-function-returns).

A contract marked `[may fail unpredictably]` does not say when its function succeeds. A verified function that calls it can be excused from saying when it succeeds, as described in [Functions that cannot promise success](#functions-that-cannot-promise-success).

If a trusted contract is wrong, every proof that uses it is worthless. Keep trusted contracts few, and claim no more than the function's documentation promises.

## Auditing a contract

A function can be verified against a contract that says very little. The `-vego.audit` flag looks for such contracts. For each contract it tries trivial implementations and reports each one that the contract would accept. It tries those that fit the function's signature:

- return zero values and change nothing;
- return other constants, chosen from 0, 1, and -1 for integers and `false` and `true` for booleans, and change nothing;
- fill the slices the function writes or returns with zero values;
- fill them with 0, 1, 2, and so on;
- return a parameter unchanged as the result of the same type.

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
2. Add `// @Ensures True` and run `laas -vego` on the package. This checks the function for index errors, overflow, nil dereferences, and termination. You will usually need to add `Requires` clauses with bounds, loop invariants, and variants. You may also find bugs.
3. Replace `Ensures True` with the real contract. Run `-vego.audit` to check that the contract says enough.
4. Move on to the callers. Each caller needs contracts for everything it calls. If a callee is not ready, give it a trusted contract with a reason such as "not verified yet". Delete the entry once the callee is verified.
5. Split functions that use unsupported Go. Move the logic into a verified function that works on plain data. Leave the part that uses an interface, a function value whose type has no contract, or a goroutine unverified, and have it call the verified function.

Keep two things in mind while a package is partly verified.

The first is that nothing checks a `Requires` clause at run time. Verified callers prove it. Unverified callers are simply trusted to satisfy it, and `go build` and `go test` add no checks. Where data enters from outside, check it in code. Write a verified function with no `Requires` clause that tests its input and returns an error, and call it before the functions that need the precondition:

```go
// @Ensures err = nil <-> 0 <= i < |A|
// @Ensures err = nil -> x = A[i]
func At(A []int, i int) (x int, err error) {
	if i < 0 || i >= len(A) {
		return 0, fmt.Errorf("index %d out of range", i)
	}
	return A[i], nil
}
```

The second is that package-level variables are not supported. The only exception is an error variable, a package-level variable of type `error` that is never assigned, as described in [Errors](#errors). A function that reads a global variable must receive the value as a parameter instead.

### For one core component

The steps are the same, but design the component first so that it stays within the supported subset of Go.

- Use plain data: structs, slices, integers, strings, maps with integer or string keys, and pointers to structs. Keep interfaces and arrays out of its types, and give every function type in them a contract.
- Write the struct invariant first. It is usually a sentence you would put in the doc comment anyway, such as "`n` never exceeds the length".
- Add `fresh(result)` to the contract of the constructor.
- Give each method the smallest `Modifies` list that works. If a method can replace a slice, add the clause described in [A slice that grows inside a struct](#a-slice-that-grows-inside-a-struct).
- Use `<->` to state when a function returns an error, where possible.

Then run the audit. Finally, write the callers at the boundary so that they check the preconditions in code.

### In a new module

Put the logic in its own packages, separate from I/O, and write each contract before its function body.

Run the verifier in CI from the first commit, so that a change that breaks a proof cannot be merged. This only covers annotated functions. A function without a `// @` line always passes, whatever it does. If every function in a package is supposed to be verified, enforce that in code review or with your own check. `vego` does not enforce it.

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
- Install Z3 5.4.1 on the machine that runs the job, as in [Running it](#running-it).
- Set a time limit on the job. Small functions take well under a second each. Functions with many pointer parameters that may alias take much longer, and the tool has not been optimised yet. `-vego.rlimit` limits the work per proof obligation, not the total run time.

## When a proof fails

Work through these steps in order.

1. Read the message as "not proved". It names a proof obligation and a location. First decide whether the obligation is actually true at that location for every input the `Requires` clauses allow. Try extreme inputs: zero, negative numbers, the largest `int`, an empty slice, `nil`, and two arguments that are the same object.
2. If the obligation is false, you have found a bug in the code or in the contract. Fix whichever is wrong. The most common cause is a missing `Requires` clause.
3. If it is true and the failure comes after a loop, the loop invariant is too weak. `vego` forgets everything the loop changes except what the invariant states. This includes struct invariants.
4. If it is true and the failure comes after a call, the `Ensures` clauses of the callee are too weak. Strengthen them.
5. If it is an overflow, add a bound on an input, or rearrange the expression as in the midpoint example.
6. If it involves two pointers or two slices, check whether they can alias. If they must not, say so in the `Requires` clause.
7. If it says that a read may be made before or after a call, decide which order you mean and write it as separate statements. See [Reads that Go may make before or after a call](#reads-that-go-may-make-before-or-after-a-call).
8. If it involves an error variable, check what `vego` knows of it. A variable that is not initialised with `errors.New` or `fmt.Errorf` may not be known to be not nil, or to differ from another error. See [What vego knows of an error variable](#what-vego-knows-of-an-error-variable).
9. Otherwise, help the prover. Put the fact in an `Assert` just before the failure. If the `Assert` is proved but the failure remains, assert a smaller intermediate step. If the `Assert` is not proved, move it earlier until it is.

One problem often produces several messages. Fix the first one and run again.

A message that starts with `cannot verify` is different. `vego` did not attempt a proof, and the text after the function name gives the reason. There are three kinds:

- Unsupported Go, such as `parameter x has unsupported type any`. Rewrite that part, or move it out of the verified function.
- A missing contract, such as `it calls helper, which has no contract`. Verify the callee or give it a trusted contract.
- A restriction on where something can appear, such as `append is only supported as the whole right-hand side of an assignment or as the returned value`. The message says what to do.

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
| `variant may not decrease in recursive call`, `variant of the function may be negative` | The same, for the `Variant` of a recursive function. | Use a different `Variant`, or strengthen the `Requires`. |
| `F has annotations, so each of its results needs a name` | A verified function has an unnamed or blank result. | Name every result in the signature. |
| `an annotation is written "// @Keyword ...", with one space before the @ and none after it` (or `with nothing but one space`) | The comment looks like an annotation but has different spacing, or something stands before the `@`. | Write `// @Keyword ...`. |
| `a comment directly after an annotation is not read as part of it` | An ordinary comment follows an annotation in the same comment group. | Start the line with `// @` to continue the annotation, or put an empty `//` line before the comment. |
| `this comment has an @ and a character that ends a line on the screen but not for Go`, or `this file has annotations and a carriage return that does not end a line` | The comment contains a character such as U+2028, or a carriage return without a newline. An editor may show what follows it as a separate line, but `vego` reads it as part of the same line. | Remove the character. |
| `unknown annotation "W"` | The word after `// @` is not a keyword. | Correct the keyword. If another tool reads the comment, declare the word with `-vego.other-tags`. |
| `Ensures annotation is not attached to a function` | The clause is not in the doc comment of a function. | Move it into the doc comment. |
| `x is assigned, which F may not modify; list it in a // @Modifies clause` | No `Modifies` entry covers memory of this kind. | Add it to `Modifies`. |
| `... which F may not modify: nothing its // @Modifies clauses list is known to cover it` | An entry covers memory of this kind, but `vego` cannot prove it is this memory. It may be another element, another struct, or a slice that was replaced after `F` was called. | Make the entry match. For a replaced slice, the callee needs a `fresh ... Or within ...` clause. |
| `x may be read before or after the call to F, which may change it, and Go does not fix the order` | Go may read `x` before or after `F` runs in this statement, and the two are not proved to give the same value. | Read `x` or call `F` in a statement of its own, in the order you mean. The message ends with such a statement, as in `x0 := x before it`, where one fits. See [Reads that Go may make before or after a call](#reads-that-go-may-make-before-or-after-a-call). |
| `cannot verify F: g is called in the target of this assignment, and Go may call it before or after append writes into the array of s` | The call may run on either side of the write, and it may read or write memory. | Assign the result of `g` to a variable in a statement of its own first. See [An append beside a call](#an-append-beside-a-call). |
| `the keys a and b of this map literal may be equal` | Two keys of a map literal are not proved to differ, so it is not known which entry the map keeps. | Prove that they differ, or assign the entries one by one. |
| `Modifies lists x, but F never needs to modify it` | The `Modifies` list allows more than the body needs. | Remove or narrow the entry. |
| `invariant of T may not hold for what is passed to F as x` | The struct invariant is not proved at the call. | Restore it before the call. In a loop, repeat it as a loop invariant. |
| `invariant of T may not hold for x on return` | The struct invariant is not proved at the end of the function. | Restore it before returning. |
| `the contract of F may also be met by a function that always returns an error` | No example input was found for which the contract forces success. | Add a clause of the form `condition -> err = nil`. See [Errors](#errors). |
| `specification of F has a hole` | Reported by `-vego.audit`. A trivial implementation satisfies the contract. | Relate the result to the input. |
| `nothing can satisfy the Requires clauses of F` | The `Requires` clauses contradict each other or the parameter types, so no call could satisfy them. | Fix the `Requires` clauses. |
| `the slices passed to F as a and b may overlap` | Two slice arguments with the same element type are not proved to be separate memory. | Pass two slice parameters of your own function, or a slice that the function allocated. No formula can yet state that two slices share no memory, so a slice stored in a struct cannot be proved separate from a parameter. |
| `cannot verify F: it calls G, which has no contract` | `G` is neither verified nor trusted. | Annotate `G`, or add it to the trust file. |
| `cannot verify F: parameter x has unsupported type T` | `T` is outside the supported subset. | Keep `T` out of the signatures of verified functions. |
| `cannot verify F: x is not a local variable` | `F` uses a package-level variable that is not an error variable. | Pass the value as a parameter. |
| `cannot verify F: formatting err would run the methods of an error whose origin is not known` | `fmt.Errorf` is given an error whose origin is not known, such as one from a parameter or from a trusted function whose contract does not vouch for it. | Return the error unchanged, or wrap your own error. If the error comes from a trusted function, see [Errors that a trusted function returns](#errors-that-a-trusted-function-returns). |
| `cannot verify F: comparing two errors can panic when both hold the same uncomparable type` | Neither error is `nil`, an error made by `errors.New` or `fmt.Errorf`, or an error variable that holds one or holds a pointer, integer, string, or boolean, or an array or struct of these. | Compare one of them with an error variable instead. See [Comparing errors](#comparing-errors). |
| `cannot verify F: errors.Is would run the Is and Unwrap methods of err, an error whose origin is not known` | `errors.Is` is asked about an error from a parameter, or from a trusted function whose contract does not vouch for it. | Compare it with an error variable using `==`. See [Asking errors.Is](#asking-errorsis). |
| `E is assigned at f.go:n, so it is not known to hold the error it was declared with`, or `x.E is assigned at f.go:n in package x` | The package of the error variable assigns it, or takes its address. | Remove the assignment, or pass the error as a parameter. |
| `x.E is changed at f.go:n in package p, which this package is built with` | A package in the build assigns the error variable, or one that went into it. | Remove the assignment. See [When a package-level error is known](#when-a-package-level-error-is-known). |
| `x is passed to F, which is trusted, and is an error whose origin is not known` (or `a value of type T, which can hold an error, an interface, or a function`) | The trusted function `F` could call code that `x` carries. | See [Arguments that carry code](#arguments-that-carry-code). |
| `the trusted contract of F cannot be true of this call` | The contract contradicts what is known at the call. | The entry is wrong, or it needs a `requires` clause. |
| `the trusted contract ... cannot be used` | The entry in the trust file is invalid. The message says why. | Fix the entry. Check the parameter names. |
| `..., in the function literal called at f.go:n:c`, or `..., in the function literal deferred at f.go:n:c and run at the return at f.go:n:c` (or `at the end of the function at`, or `at the end of the function literal at`) | The problem is in the body of a function literal, at the call named at the end. For a deferred literal, the message names the `defer` statement and where the literal runs. | Fix the body, or what holds at that call. See [Function literals](#function-literals). |
| `cannot verify F: the function literal is used as a value of type T, which has no contract` | The literal is passed, returned, or stored as a value of a function type that has no contract. | Declare a named function type with a contract and use it there. |
| `the function value f may be nil` | A call through `f` is not proved to have a value to call. | Add `f != nil` to the `Requires` clauses, or check `f` before the call. |
| `cannot verify F: f has type T, which has no contract` | `f` is called, and its type has no contract. | Declare a named function type with a contract and use it for `f`. See [Function values](#function-values). |
| `cannot verify F: x is used as a value of type T, which has no contract` | A function, method value, or literal is given a function type that has no contract. | Give it a named function type with a contract. |
| `cannot verify F: converting x to T is not supported` | A function value of another type is converted to a function type. | Make the value of the type it is used as, from a function, a method value, or a literal. |
| `..., in g used as a T at f.go:n:c`, or `..., in the function literal used as a T at f.go:n:c` | The function, method value, or literal does not meet the contract of `T` where it is made into a value of `T`. | Fix the function or the literal, or the contract of `T`. See [Making a function value](#making-a-function-value). |
| `the Ensures clauses of T are not proved to be satisfiable for every call that its Requires allow` | Some call that the `Requires` of `T` allow has no result that meets its `Ensures`. | Add the condition to the `Requires` clauses, or weaken the `Ensures`. |
| `cannot verify F: a function literal used as a value cannot assign x` | The literal assigns a variable of the function around it. | Return the value from the literal, or write it into memory that the contract of the type lists. |
| `... calls through the function value f, and code that a function value runs cannot do that yet`, or `g may call through a function value, and code that a function value runs cannot do that yet` | Code that a function value runs would call through a function value. | Leave that code unverified. See [Function values that call function values](#function-values-that-call-function-values). |
| `cannot verify F: x is passed to the function value f and is an error whose origin is not known` | The value may come from code that is not verified, which could run the methods of the error. | Pass an error made by `errors.New` or `fmt.Errorf`, or call from code that is not verified. |
| `cannot verify F: f holds a function literal and is used here other than by calling it` | The variable that holds the literal is passed, compared, or assigned again. | Only call the variable. |
| `cannot verify F: recover is not supported` | `recover` returns an interface. | Call `recover` in a function that is not verified. |
| `cannot verify F: a formula built to verify it has grown beyond 1048576 nodes, which is the limit` | An expression or a run of statements builds a formula that grows faster than the code, as `x = x + x` does when repeated. | Split the function, or the expressions in it, into smaller ones. |
| `analysis skipped due to errors in package` | The package does not compile, or the toolchain does not match. | See [Running it](#running-it). |

## What is not supported

`vego` supports functions and methods over these types: the integer types, `bool`, `string`, `error`, the float types, structs, pointers to structs, slices, and maps with integer or string keys. In the body it supports assignments, `if`, `switch`, `for` and `range` loops with `break` and `continue`, `return`, `defer`, calls to named functions and methods, function literals that are called or deferred where they are written or bound to a variable that is only called, function values of named function types with a contract (see [Function values](#function-values)), and recursion. The built-ins `len`, `cap`, `min`, `max`, `new`, `make`, `append`, and `delete` are supported, and so are composite literals, slicing, and the arithmetic, comparison, shift, and bitwise operators.

A function that uses any of the following is reported as `cannot verify`:

- interfaces other than `error`, calls through interfaces, type switches, and type assertions;
- calls of function values whose type has no contract, and making a function value of such a type from a function, a method, or a literal (see [A function type without a contract](#a-function-type-without-a-contract));
- converting a function value to another function type, and method expressions such as `T.M`;
- a function literal used as a value that assigns a variable it captures (see [Function literals as values](#function-literals-as-values));
- code that a function value made by verified code runs and that calls through a function value (see [Function values that call function values](#function-values-that-call-function-values));
- a contract on a function type whose `Ensures` only a change of the elements of a slice or a map, or memory that the call creates, can meet;
- passing an error of unknown origin, or a value that can hold an interface or a function value of a type without a contract, to a function value;
- `recover`;
- generic functions and types;
- goroutines, channels, and `select`;
- arrays, and structs that contain an array;
- pointers to anything other than a struct;
- package-level variables, except error variables that are never assigned, of this package or another;
- calls to variadic functions other than `fmt.Errorf`;
- `append(s, t...)` and `copy`;
- a call in the target of an assignment whose right-hand side is an `append` that may write into the array of its slice, unless the call modifies nothing and refers to no memory or a call among the operands of the `append` orders it (see [An append beside a call](#an-append-beside-a-call));
- a call with several results as the arguments of another call, as in `g(f())`;
- comparing structs with `==`;
- comparing two errors with `==` when neither is `nil`, an error made by `errors.New` or `fmt.Errorf`, an error that a trusted contract vouches for, or an error variable that holds one or holds a pointer, integer, string, or boolean, or an array or struct of these (see [Comparing errors](#comparing-errors));
- `errors.As`, `errors.Join`, `errors.Unwrap`, and `errors.Is` on an error whose origin is not known (see [Asking errors.Is](#asking-errorsis));
- a `range` over a map whose body modifies a map of the same type;
- `goto`, `fallthrough`, labelled `break` and `continue`, and `defer` inside a loop, except inside a function literal that the loop calls.

Floating-point values are supported but opaque. They can be passed around and used in arithmetic, but nothing can be stated or proved about their values. An integer converted from a float can have any value of its type, so check its range in code before you use it as an index.

## What a proof assumes

A proof by `vego` depends on the following assumptions. Each concerns something `vego` cannot see.

- Trusted contracts are true. This applies to the shipped contracts and to your own. A trusted function returns without panicking when its `requires` clauses hold. It writes nothing a caller can see outside its `modifies` list. It does not keep the pointers and slices it receives. It does not call back, through another package, into the verified function that called it. A call back within the same package is found and reported. For a parameter listed under `runs`, all of this holds whatever value is passed, or for a function value of a type with a contract, whatever value that meets the contract is passed. The function runs the code it receives only before it returns, only on the goroutine that called it, and only with arguments that meet the `Requires` of the type of a function value, and it keeps no value that can hold code. For a result listed under `vouches`, the errors it returns meet the conditions in [Errors that a trusted function returns](#errors-that-a-trusted-function-returns), and the function values it returns meet the contracts of their types.
- Unverified callers respect the contract. They satisfy the `Requires` clauses, pass structs whose invariants hold, and do not pass overlapping slices for two slice parameters of the same element type. They call a function value that verified code made only with arguments that meet the `Requires` of its type.
- A function value that reaches verified code from code that is not verified meets the contract of its type. That includes a value passed as an argument, a value in memory that an argument reaches, and a value made with `reflect.MakeFunc` or by generic code. Called with arguments that meet the `Requires` of its type, such a value returns without panicking, writes only what the `Modifies` of its type lists, and leaves its `Ensures` true.
- Unverified code respects Go's type system. It does not use `unsafe`, `reflect`, or cgo to give one piece of memory two types or to change a string.
- No other goroutine writes memory that a verified function reads or writes while it runs. A proof covers one goroutine.
- No code outside the packages that a verified package is built with assigns an error variable that a proof relies on, and no code changes one through `go:linkname`, assembly, `unsafe`, or `reflect`. When a verified package is built with a package that makes such an assignment, the verified package does not rely on the variable. The assignment is also reported wherever it meets a proof that does rely on it.
- `errors.New`, `fmt.Errorf`, and `errors.Is` behave as they do in the Go releases that `laas` is tested with. Each call of `errors.New` or `fmt.Errorf` returns a new pointer. The errors they return have no `Is` method. `Unwrap` returns the operand of the one `%w`. `errors.Is` finds an error, or an error it wraps, that is the target. The tests of `vego` check this against the running toolchain.
- The compiler evaluates each statement in an order that the Go specification allows. Calls, `&&`, and `||` run from left to right, an operation runs after its operands, and an assignment assigns only after it has evaluated everything. Where the specification leaves the order open, `vego` proves that every order it allows gives the same values.
- The program runs on the platform `laas` was run for. The sizes of `int`, `uint`, and pointers, the layout of structs, and `MaxAlloc` are those of the `GOOS` and `GOARCH` that `laas` runs with. A proof for a 64-bit target does not hold for a 32-bit target.
- The program is built from the files `laas` read. Files left out by a build constraint or a file name such as `_windows.go` are not read, so their annotations are not checked. Run `laas` once for each configuration you ship.
- The machine has enough memory and stack.
- Z3 is correct. Every proof rests on Z3 5.4.1 answering correctly that a problem has no solution.
- Your formulas say what you intend. `vego` does not check a formula for out-of-range indexes or division by zero, so a formula that contains one may mean something other than you expect. See [Formulas](#formulas).

## Summary

### Annotations

| Annotation | Where | Meaning |
| --- | --- | --- |
| `Requires P` | doc comment of a function or of a named function type | `P` must be true when the function, or a value of the type, is called. |
| `Ensures P` | doc comment of a function or of a named function type | `P` is true when the function, or a value of the type, returns. |
| `Modifies a, b.f` | doc comment of a function or of a named function type | The memory the function, or a value of the type, may write that a caller can see. |
| `Variant e` | doc comment of a recursive function | `e` is never negative and is smaller at each recursive call. |
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
| <code>&#124;A&#124;</code> | length of a slice or string, or number of keys in a map |
| `A[i]`, `m[k]`, `p.f` | element, map value, field |
| `A[lo:hi) <= x` | the comparison holds for every element from `lo` up to `hi` |
| `Forall k in [a, b) : P`, `Exists k in [a, b] : P` | quantifiers over an interval |
| `Forall k in Z : P` | quantifier over all integers |
| `"text"`, `nil` | a string; the nil pointer or nil error |
| `ErrEmpty`, `io.EOF` | an error variable of the package, or of an imported package |
| `"io/fs".ErrNotExist` | in a trusted contract, an error variable named by the path of its package |
| `err = ErrEmpty` | the two are the same error |
| `is(err, target)` | `errors.Is(err, target)` reports true |
| `has(m, k)` | the map contains the key |
| `name(x, y)` | a predicate |

### Before and after

| Where | A plain name means | Other state |
| --- | --- | --- |
| `Requires` | the value at the call | |
| `Ensures` | the value at the call | `A'`, `c.f'`, `s.items'[0]`: the value on return |
| `Invariant` and `Assert` in a body | the current value | `old(x)`: the value at the call |

Results are referred to by the names in the function's signature.

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

### Order of evaluation

| In a statement | Order |
| --- | --- |
| calls, `&&`, and <code>&#124;&#124;</code> | from left to right |
| an operation | after its operands |
| the right operand of `&&` and <code>&#124;&#124;</code> | after the left one, and only when the left one does not decide the result |
| an assignment | assigns after every operand is evaluated |
| a call of a function literal | like a call, and it may change the variables that the literal assigns |
| a call through a function value | like a call; the value is evaluated with the arguments, before the call |
| any other read of memory, or of a variable that a function literal assigns | not fixed; `vego` proves that every order gives the same value |
| `append` and other built-in functions | after their operands, and not ordered like calls |
| the entries of a map literal | not fixed; keys that are not both constants must be proved different |

### Flags

| Flag | Effect |
| --- | --- |
| `-vego` | run only the verifier |
| `-vego.audit` | also report contracts that trivial implementations satisfy |
| `-vego.rlimit=n` | Z3's resource limit for one proof obligation, 4000000 by default |
| `-vego.z3=path` | the Z3 5.4.1 binary to use, instead of the `z3` on `PATH` |
| `-vego.trusted=path` | use this trust file instead of the one next to `go.mod` |
| `-vego.other-tags=A,B` | words that another tool reads after `// @`; any other unknown word there is an error |
| `-vego.trust` | print the trust report |
| `-test=false` | leave out test files |
| `-exclude-packages=regexp` | skip packages whose import path matches |
