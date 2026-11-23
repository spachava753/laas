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

`vego` is experimental and supports only part of Go. It does not yet support calls through interfaces whose methods have no contract (which includes the interfaces of the standard library), methods of an interface that write what the interface value holds, calls of function values whose type has no contract, generic code, goroutines, arrays, or package-level variables that are changed. [What is not supported](#what-is-not-supported) lists the main gaps. Code that does I/O usually runs into these limits. The usual approach is to verify the logic and leave the code around it unverified. [Adopting it](#adopting-it) describes how.

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

An annotation is a comment line of the form `// @Keyword ...`. Each keyword is allowed only in certain places.

| Keyword | Where it goes |
| --- | --- |
| `Requires`, `Ensures`, `Modifies` | the doc comment of a function |
| `Variant` | the doc comment of a recursive function, or directly above a `for` loop |
| `Invariant` | directly above a loop |
| `Visited` | directly above a `range` over a map (see [Loops over a map](#loops-over-a-map)) |
| `Assert`, `Snapshot` | anywhere in a function body, on its own line |
| `Invariant` | the doc comment of a struct type |
| `Predicate` | the top level of a file |
| `State`, `Receiver` | the doc comment of an interface type and of its methods (see [States of interface values](#states-of-interface-values)) |
| `Vouches` | the doc comment of a method in an interface type or of a function type, beside its contract (see [Interface values from code that is not verified](#interface-values-from-code-that-is-not-verified)) |

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
Invariant, Variant, Visited, Assert, Snapshot, Predicate, State, Receiver, Vouches. If another tool
reads this comment, declare the word with -vego.other-tags
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

Each operator has one spelling. Go's `&&`, `||`, `!`, and `==` are reported with the spelling to use:

```text
vego: syntax error in Requires annotation: && is not a spelling of the formula language; write And
```

Inequality is written `!=`, as in Go.

```go
// @Ensures result = -1 Or (0 <= result < |A| And A[result] = x)
```

`~` binds tightest, followed by `And`, `Or`, `->`, and `<->`. `a -> b -> c` means `a -> (b -> c)`. Use parentheses if you are unsure.

Numbers in formulas are mathematical integers. They do not overflow, so `x + 1` is always one more than `x`, whatever the type of `x`. `/` and `%` round as they do in Go. The limits of the Go integer types have names: `MaxInt`, `MinInt`, `MaxInt8` to `MaxInt64`, `MinInt8` to `MinInt64`, and `MaxUint` to `MaxUint64`. `MaxAlloc` is the largest number of bytes in one allocation on the platform. No string is longer than `MaxAlloc`.

`|A|` is the length of a slice or string, or the number of keys in a map. `A[i]` is an element. Fields are written with a dot, including through pointers: `c.count`, `s.items[i]`, `|s.items|`.

Formulas can also use strings and `nil`: `role = "admin"`, `p != nil`, `err = nil`. Two pointers can be compared with each other, as in `a != b`. Two errors can be compared too, as in `err = ErrEmpty`, and `is(err, ErrEmpty)` says what `errors.Is` reports. See [Saying which error a function returns](#saying-which-error-a-function-returns).

A boolean can be used as a formula on its own, as in `found` or `~found`. It can also be compared with `True` and `False`, as in `found = True`.

A character in single quotes is the number of that character, as in Go. `s[0] = '/'` means `s[0] = 47`. Escapes are written as in Go, as in `'\n'` and `'\x41'`. A quote directly after a name is a prime, as in `x'`. Any other quote starts a character, so `x' = 'a'` compares the value on return with 97. In a doc comment, `gofmt` turns two quotes in a row into `”`, and two backquotes into `“`. So write the quote character as `'\x27'`, and two quotes in a string as `"\x27\x27"`. A formula that contains `“` or `”` is reported, also inside a string, where the mark is written `"\u201d"`.

`cap(A)` is the capacity of a slice. `A = nil` and `A != nil` say whether a slice is nil, as `A == nil` does in code. See [Capacity and nil in a formula](#capacity-and-nil-in-a-formula).

`elemsize(A)` is the number of bytes that one element of the slice `A` takes on the platform, as `unsafe.Sizeof` gives it. It is 0 for a slice of values of size zero, such as `[]struct{}`. The contracts of generic functions that allocate use it, as described in [Memory and allocation](#memory-and-allocation).

### Quantifiers

`Forall` and `Exists` range over an interval of integers, or over the keys of a map, as described in [Maps](#maps).

```go
// @Requires Forall k in [0, |A|) : 0 <= A[k] <= 1000
// @Ensures Exists k in [0, |A|) : A[k] = result
```

Intervals use mathematical notation. `[0, n)` includes 0 and excludes `n`. `[0, n]` includes both. Several variables can share an interval, as in `Forall i, j in [0, n) : ...`. `in Z` ranges over all integers.

The body of a quantifier extends to the end of the clause. To end it earlier, put the whole quantifier in parentheses.

There is a short form for a condition on a range of elements. `A[lo:hi) <= x` means that every element from index `lo` up to, but not including, `hi` is at most `x`. Any comparison operator can be used.

### Names

A contract can use the function's parameters and results, and the integer and boolean constants of the package. String constants cannot be used by name. Write the string itself. A contract can also name the error variables of the package, as in `ErrEmpty`, and those of an imported package, as in `io.EOF`. A trusted contract names them by the path of their package instead. See [Error variables in a trusted contract](#error-variables-in-a-trusted-contract). The contract of a verified function can name other package-level variables that nothing changes, as described in [Package-level variables](#package-level-variables).

Results are referred to by their names, so every result of a verified function must be named. This guide calls a single result `result`, but you can choose another name. Go does not allow a result to share a name with a parameter, so a name in a contract cannot mean both. Three names are not available for variables that annotations use: `True`, `False`, and `nil`, which are words of the formula language. A predicate cannot be called `len`, `cap`, `elemsize`, `old`, `fresh`, `within`, `apart`, `has`, or `is`.

```text
vego: Unnamed has annotations, so each of its results needs a name, as in func Unnamed(x int) (i int)
```

A contract can name an unexported field only of a struct declared in the package where the contract is written. For an entry in the trust file, that is the package of the function or type that the entry describes. A shipped entry can name no unexported field. A contract of another package that names one is refused:

```go
// @Requires a != nil And a.mu.mu.state = 0
// @Ensures True
func Free(a *Account) {
}
```

```text
vego: in Requires annotation: a.mu.mu: mu is an unexported field of sync.Mutex, declared in package
sync, and a formula in package guide cannot name it; sync.Mutex has the state held, which a formula
names as held(x) for a value or a pointer x
```

A contract can name the unexported fields of structs of its own package, and keeps that meaning where other packages call the function. Such a field can change between versions of the package that declares it, so a contract of another package speaks of the type through its exported fields.

A predicate called `held`, `rheld`, or `running` cannot be used on a mutex or a `sync.Once`, whose states have those names. See [Locks](#locks).

### Limits

Formulas have no bit operators, no `len`, and no floating-point facts. Write `|A|` for a length. They cannot call functions, only predicates. Structs cannot be compared as a whole. Compare their fields.

In a formula, `=` between two interface values says that they are the same value: one was copied from the other. This is how a contract says that a field of an interface type, such as `any`, keeps its value:

```go
// @Requires s != nil
// @Modifies s
// @Ensures s.next' = s And s.Value' = s.Value
func (s *Link) Loop() {
	s.next = s
}
```

`Modifies s` covers the field `Value` too, so without the clause a caller would know nothing of it after the call.

This is not Go's `==`. Two conversions of one concrete value are two values, so after `a, b := any(p), any(p)` the formula `a = b` is false, although `a == b` is true in Go. Code still cannot compare two interface values. See [Comparing interface values](#comparing-interface-values).

`=` between two slices compares their lengths and elements, not whether they share memory. A copy is equal to what it copies:

```go
// Duplicate copies A into new memory.
//
// @Requires |A| <= 1000
// @Ensures r = A
func Duplicate(A []int) (r []int) {
	return append([]int(nil), A...)
}

// Overwrite returns A after changing an element.
//
// @Requires |A| > 0 And A[0] = 1
// @Modifies A
// @Ensures r = A
func Overwrite(A []int) (r []int) {
	A[0] = 2
	return A
}
```

```text
vego: postcondition may not hold: r = A
```

`Overwrite` returns the slice it was given, but `A` in the `Ensures` is its elements at the call, and `A[0]` has changed. To say where a slice lies, use `fresh` and `within`, described in [Newly allocated memory](#newly-allocated-memory).

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

A variable of struct type whose address is not taken counts as changed when the loop assigns any of its fields. This loop assigns `s.Total`, so after it nothing is known of `s.Count` either:

```go
// TallyLoses loses Count: the loop assigns s.Total, so it forgets s.
//
// @Requires |xs| <= 1000
// @Requires Forall k in [0, |xs|) : 0 <= xs[k] <= 1000
// @Ensures s.Count = |xs|
func TallyLoses(xs []int) (s Stats) {
	s.Count = len(xs)
	// @Invariant 0 <= s.Total <= 1000 * i
	for i := range xs {
		s.Total += xs[i]
	}
	return s
}
```

```text
vego: postcondition may not hold: s.Count = |xs|
```

Add the field to the invariant, as in `// @Invariant s.Count = |xs| And 0 <= s.Total <= 1000 * i`.

A struct in memory is different: a loop that writes some of its fields keeps what it knew of the others, as described in [What a loop forgets about memory](#what-a-loop-forgets-about-memory). That includes a struct reached through a pointer and a variable whose address is taken, as by calling a method with a pointer receiver on it:

```go
// reset clears the total.
//
// @Requires s != nil
// @Modifies s.Total
// @Ensures s.Total' = 0
func (s *Stats) reset() {
	s.Total = 0
}

// TallyInMemory keeps Count: s lives in memory, since reset takes its
// address, and the loop writes only s.Total.
//
// @Requires |xs| <= 1000
// @Requires Forall k in [0, |xs|) : 0 <= xs[k] <= 1000
// @Ensures r = |xs|
func TallyInMemory(xs []int) (r int) {
	var s Stats
	s.reset()
	s.Count = len(xs)
	// @Invariant 0 <= s.Total <= 1000 * i
	for i := range xs {
		s.Total += xs[i]
	}
	return s.Count
}
```

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

A message about a missing `Variant` names the cycle, as in `recursive call needs a // @Variant annotation in the doc comment of F to prove termination; the cycle: F calls G at f.go:12:9, G calls F at f.go:20:9`.

### Cycles through function values and interface methods

A call through an interface value or a function value has no callee that `vego` can name, so it cannot check a `Variant` across it. A cycle of calls that goes through such a call is reported at every call of the cycle in a verified function. Here `Pull` calls `s.Next()`, and a `*Retry` held in `s` calls `Pull` again:

```go
// Source reads a number.
type Source interface {
	// @Ensures n >= 0
	Next() (n int)
}

// Retry calls back into Pull through a Source it holds.
type Retry struct{ src Source }

// @Requires r != nil
// @Variant 1
// @Ensures n >= 0
func (r *Retry) Next() (n int) {
	if r.src == nil {
		return 0
	}
	return Pull(r.src)
}

// @Requires s != nil
// @Variant 0
// @Ensures n >= 0
func Pull(s Source) (n int) {
	return s.Next()
}
```

```text
vego: this call may not end: Pull calls s.Next() at cycles.go:28:9, which may run (*Retry).Next,
(*Retry).Next calls Pull at cycles.go:21:9; a cycle that goes through a call with no static callee,
of an interface method or a function value, or through code of another package, cannot be shown to
end, since no Variant can be checked across such a call. Break the cycle
```

The variants do not help, because nothing compares them across `s.Next()`. A `*Retry` whose `src` is itself loops for ever. Break the cycle: call the method on the concrete type, or keep the call back out of the method.

`vego` finds such a cycle from the types alone, whoever makes the value, also code that is not verified or code of another package:

- A call of an interface method `M` may run every method named `M` in the package whose signature, receiver aside, is the same.
- A call through a function value may run every function, method value, method expression, and function literal of the package that is used as a value of a type with the same signature. Every exported function, and every method with an exported name on any type, counts as such a value, since another package can make one of it.
- A call of a function of another package may run what its arguments and its receiver can hold, at any depth. So may a call through an interface value or a function value, whose implementation may be code of another package, for its arguments:
  - A function value counts as a call through it.
  - An interface value counts as a call of each of its methods. It may also run every method with an exported name of every type of the package, and every function value the package lets out, of any signature, since that code can find them by a type assertion or reflection.
  - An `unsafe.Pointer` may run the same, since that code can convert it back to the type of what it points to and call that. The two types described in [Arguments that carry code](#arguments-that-carry-code), `sync/atomic.Pointer[T]` and `runtime.Pinner`, count as what their package lets them hold instead.
  - A value of another type converted to an interface there may run the exported methods of its type and of the types it holds.
  - A function or a literal written as the argument may run only itself.
  - A value that `fmt` formats may run the methods named `String`, `Error`, `Format`, and `GoString` of what it holds through exported fields, and of every type of the package through an interface value.
  - An error of known origin made at the call, `nil`, and a sentinel of the package run nothing of the package.
  - An entry of the trust file may claim what the function finds on what a parameter holds, under `asserts`, and the call then runs only what the claim allows. See [What a function finds on what it is handed](#what-a-function-finds-on-what-it-is-handed).

A method of another name or another signature is not reached. A method `Next(step int) (n int)` beside `Source` above is no part of the cycle.

When the cycle goes through code of another package because of what a value can hold, the message says why that code may reach the package and what removes it, as in `r is an interface value, which may hold a value of any type of the package or any function it lets out, and code of another package may call that, or an exported method of it, by a type assertion or reflection, so a cycle goes through code of another package, and no Variant can be checked across it. Hand that code a value whose type holds no interface value and no function value, or keep what it may reach from calling back`. The entries that `vego` ships for `bufio`, `io`, `log`, and the `fmt` functions that write to a writer claim what they find on what they are handed, so a reader or a writer handed to them reaches only its `Read` or `Write`.

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

A contract that cannot be read is reported at each call, so the caller fails there. The rest of the caller is still checked, so that its own mistakes are reported at the same time:

```go
// Box holds a value of any type.
type Box struct{ Value any }

// @Requires b != nil
// @Ensures b.Value' = b
func (b *Box) touch() (result *Box) {
	return b
}

// @Requires b != nil
// @Ensures True
func Touches(b *Box) {
	b.touch()
}
```

```text
vego: in Ensures annotation: an interface value can only be compared with nil or with another
interface value
vego: the contract of touch cannot be used: its Ensures annotation at unreadable.go:7:1 cannot be
read (an interface value can only be compared with nil or with another interface value), so this
call is verified without it
```

The first message is at the clause, and the second at the call in `Touches`.

What the rest of the caller relies on depends on what can be read:

- For a function of the package, when every `Requires` and `Modifies` clause can be read, the call checks the `Requires` and assumes the `Ensures` clauses that can be read.
- For a function of the package whose `Modifies` clauses can be read but a `Requires` clause cannot, the call assumes nothing about what it returns, and what `Modifies` lists is forgotten.
- For the contract of a function type or of an interface method declared in the package, when its `Modifies` clauses can be read, a call checks the `Requires` clauses that can be read and assumes no `Ensures`. What `Modifies` lists is forgotten.
- Otherwise, nothing after the use is checked on that path. This happens, for example, when a `Modifies` clause cannot be read, when a trusted contract has a defect, or when a value is converted to a function type or an interface whose contract cannot be read.

The contract of an exported function is available to other packages, so verified code can call verified functions in other packages. If a function failed verification, other packages cannot rely on its contract.

### Variadic functions

Inside a variadic function, and in its contract, the last parameter is a slice:

```go
// @Ensures m >= first
// @Ensures Forall i in [0, |rest|) : m >= rest[i]
func Largest(first int, rest ...int) (m int) {
	m = first
	// @Invariant 0 <= i <= |rest|
	// @Invariant m >= first
	// @Invariant Forall j in [0, i) : m >= rest[j]
	// @Variant |rest| - i
	for i := 0; i < len(rest); i++ {
		if rest[i] > m {
			m = rest[i]
		}
	}
	return m
}

// @Ensures m >= 7
func AtLeastSeven(x int) (m int) {
	return Largest(7, x, 3)
}
```

A call that lists the arguments, as in `Largest(7, x, 3)`, passes a new slice that holds them. Its length and capacity are the number of arguments. A call with no arguments for the parameter, as in `Largest(7)`, passes `nil`. The new slice shares no memory with anything that existed before the call, so the callee may write its elements without the caller listing anything in `Modifies`. The values in it are the caller's, though. If the elements are pointers, a callee that writes what they point to writes the caller's memory, and the caller needs a `Modifies` clause for it as for any other call.

Each argument is converted to the element type of the slice. When that type is an interface, the conversion is checked as described in [Making an interface value](#making-an-interface-value).

A call that passes a slice with `...` passes that slice itself, and not a copy. A callee that writes it writes the caller's array:

```go
// @Requires |xs| > 0
// @Modifies xs
// @Ensures xs'[0] = 0
func ClearFirst(xs ...int) {
	xs[0] = 0
}

// @Requires |xs| > 0
func ClearAll(xs []int) {
	ClearFirst(xs...)
}
```

```text
vego: ClearFirst may modify xs, which ClearAll may not modify; list it in a
// @Modifies clause
```

Everything described in [Slices](#slices) about slices that share memory applies to such a slice. Two slice parameters of one element type must not overlap, so `Pair(xs, xs...)` for a `func Pair(a []int, rest ...int)` is reported as `the slices passed to Pair as a and rest may overlap`.

A function type with a contract and a method of an interface can be variadic too, and so can a function literal. Calls through such values, and values made of variadic functions, work as for any other type. A value of an `...any` parameter carries code, so a call through a function value or an interface value that passes one is refused, as described in [Function values from code that is not verified](#function-values-from-code-that-is-not-verified).

## Function literals

`vego` verifies a function literal when every use of it is in the function that contains it. A literal can stand in three places:

- where it is called, as in `func() { ... }()`;
- where it is deferred, as in `defer func() { ... }()`;
- as the value that declares a new local variable, which the function then only calls.

A literal written where it is handed to a trusted function that calls it while it runs, such as `sort.Search`, is verified there too. See [Functions that a trusted function calls](#functions-that-a-trusted-function-calls).

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

A literal that is passed to a function, returned, or stored is a function value, unless it is passed to a parameter of a trusted function that has a contract under `calls`. It needs a function type with a contract, and is verified as described in [Function literals as values](#function-literals-as-values). A literal given a type without a contract is reported as `cannot verify`:

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

A variable declared with `:=` that holds a literal and is used other than by calling it is reported as `cannot verify` too, with the message `f holds a function literal and is used here other than by calling it`. Declare it with a type that has a contract instead, as in `var f T = func...`. To hand it to a trusted function that calls it, write the literal where it is handed over. A literal that takes or returns a type that `vego` does not support cannot be verified either.

## Function values

A function value is a value of a function type. It can be held anywhere a value can, such as in a parameter, a field, or a slice. `vego` calls a function value only through the contract of its type. You write that contract in the doc comment of a named function type, with the keywords a function uses:

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

Declare a named type such as `Mapper` and use it for the parameter. A contract can only be written on a named type. A function type of another module gets its contract from an entry in the trust file, as `context.CancelFunc` does from a shipped one. See [Interfaces and function types of other packages](#interfaces-and-function-types-of-other-packages).

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
vego: precondition of small may not hold: 0 <= x <= 10, in small used as a value of type Mapper at funcvalues.go:103:9
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
vego: addition may overflow int, in the function literal used as a value of type Mapper at funcvalues.go:121:6
vego: postcondition may not hold: 0 <= y <= 2000, in the function literal used as a value of type Mapper at funcvalues.go:121:6
```

A literal used as a value cannot assign a variable it captures:

```text
vego: cannot verify Tally: a function literal used as a value cannot assign calls, a variable of
the function around it: it may run when that function has moved on, and no call of it could tell
that function what it did
```

A literal used as a value cannot call a variable that holds a literal of the function around it. Inside the body of the literal, `old(x)` is the value that its own parameter `x` had when it was called.

### Function values that call function values

The code that a function value made by verified code runs cannot call through a function value. These are refused:

- a literal that calls a value it captures;
- a literal or a function that passes a value to a function that calls it;
- a function used as a value that calls through a value itself.

`Logged` returns a literal of the first kind:

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
variant, so nothing would prove that such calls end. Make the value in code that is not verified,
or keep that call out of the literal
```

A contract of a function type has no `Variant`. A value could be handed back to code that calls it again, and nothing would show that this ends. With this rule, a call through a value that verified code made runs code that makes no such call.

### Function values from code that is not verified

A function value that verified code receives from code it does not verify is taken to meet the contract of its type. See [What a proof assumes](#what-a-proof-assumes). Such a value could run code that an argument carries. So these arguments cannot be passed to a function value:

- an error whose origin is not known;
- a function value whose type has no contract;
- an interface value with a method that has no contract, and an `any`.

`Tell` passes an error that came from a parameter:

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

An error made with `errors.New` or `fmt.Errorf` can be passed, and so can a function value of a type with a contract and an interface value whose methods all have contracts.

## Interfaces

An interface value is a value of an interface type other than `error`. It can be held anywhere a value can. `vego` calls a method through an interface value only through the contract of that method. You write the contract in the doc comment of the method, in the declaration of the interface:

```go
// Pricer prices an order line.
type Pricer interface {
	// Price returns the price in cents of qty units of sku, and whether
	// sku is known.
	//
	// @Requires 0 <= qty <= 1000
	// @Ensures ok -> 0 <= cents <= 1000000
	Price(sku string, qty int) (cents int, ok bool)
}

// LinesTotal adds the prices of two lines.
//
// @Requires p != nil
// @Requires 0 <= a <= 1000 And 0 <= b <= 1000
// @Ensures ok -> 0 <= total <= 2000000
func LinesTotal(p Pricer, a, b int) (total int, ok bool) {
	x, okA := p.Price("apple", a)
	y, okB := p.Price("pear", b)
	if !okA || !okB {
		return 0, false
	}
	return x + y, true
}
```

At each call `p.Price(...)`, `LinesTotal` proves that `p` is not nil and that the `Requires` clause of `Price` holds. After the call it knows the `Ensures` clause and nothing else. The call is checked like any other call, so what the method lists in `Modifies` must be memory that `LinesTotal` may modify. A call through an interface value can be deferred, as in `defer p.Price("apple", 1)`. The interface value and the arguments are evaluated at the `defer` statement, and a nil interface value is reported there.

An interface value that may be nil cannot be called:

```text
vego: the interface value p may be nil
```

An interface value can be compared with `nil`, in code and in formulas, as in `p != nil`. A formula can also compare two interface values by `=`, which says that they are the same value (see [Comparing interface values](#comparing-interface-values)).

### Writing a contract on a method of an interface

A contract on a method of an interface has `Requires`, `Ensures`, and `Modifies` clauses over the parameters and results of the method. The method must name its results. The receiver has no name, so a contract cannot refer to what the interface value holds. A `Receiver` annotation names the receiver. The contract can then use the name in two places: as the argument of a state, described in [States of interface values](#states-of-interface-values), and in `Modifies`, to say that the method writes memory behind its receiver, described in [Methods that write behind their receiver](#methods-that-write-behind-their-receiver).

`vego` checks the contract where the interface is declared, in the same way as the contract of a function type. See [Writing a contract on a function type](#writing-a-contract-on-a-function-type). An `Ensures` that some call its `Requires` allow could not meet is reported there.

A contract can be written only on a method of an interface type declared at package level, with a name and without type parameters. An interface type that embeds another interface has the methods of the embedded one, with their contracts. When two embedded interfaces declare a method of the same name, Go keeps one of them, and `vego` reports the contract that is left out:

```go
// Sized has a method of its own.
type Sized interface {
	// @Ensures n >= 0
	Size() (n int)
}

// Bounded declares a Size of its own.
type Bounded interface {
	// @Ensures n <= 100
	Size() (n int)
}

// Measured gets Size from both.
type Measured interface {
	Sized
	Bounded
}
```

```text
vego: the contract of Bounded.Size is not part of this interface: it has Size from Sized.Size,
and Go keeps one declaration of a method; declare the method once, with its contract
```

A method without a contract cannot be called through an interface value. A method of an interface of another module has no doc comment you can annotate. It gets a contract from an entry in the trust file instead, and `vego` ships entries for a few methods of the standard library, such as `(io.Writer).Write`. `fmt.Stringer` has none:

```go
// @Requires s != nil
// @Ensures True
func Show(s fmt.Stringer) (text string) {
	return s.String()
}
```

```text
vego: cannot verify Show: s.String calls Stringer.String, which has no contract; a method of an
interface gets one in its doc comment where the interface is declared, with // @ annotations;
for a type of another module, give it an entry (fmt.Stringer).String in vego-trusted.yaml
```

`io.Closer` has a shipped entry whose contract speaks of whether the value has been closed. See [States of interface values](#states-of-interface-values).

### Making an interface value

Go converts a value to an interface type where the value is passed, assigned, returned, or stored as the interface type, or converted with `I(x)`. Where verified code converts a value of a type that is not an interface, `vego` checks each method of the interface. It checks the method of the value's type as a function of its own, with the contract of the interface method. Called with arguments that meet the `Requires` of the interface method, the method of the type must meet its own `Requires`, write nothing that the interface method does not list in `Modifies`, and leave the `Ensures` of the interface method true.

```go
// Table prices every item at the same rate.
type Table struct {
	Rate int
}

// Price uses the rate of the table.
//
// @Requires t != nil And 0 <= qty <= 1000
// @Ensures ok -> 0 <= cents <= 1000000
func (t *Table) Price(sku string, qty int) (cents int, ok bool) {
	if t.Rate < 0 || t.Rate > 1000 {
		return 0, false
	}
	return t.Rate * qty, true
}

// @Requires t != nil
// @Ensures ok -> 0 <= total <= 2000000
func TotalAtRate(t *Table) (total int, ok bool) {
	return LinesTotal(t, 1, 2)
}
```

`TotalAtRate` passes `t` as a `Pricer`, so `vego` checks `(*Table).Price` against the contract of `Pricer.Price` there. A method that does not meet the contract is reported where the value is converted:

```go
// Flat prices every item at 2000 cents.
type Flat struct{}

// @Requires 0 <= qty <= 1000
// @Ensures ok
func (Flat) Price(sku string, qty int) (cents int, ok bool) {
	return 2000 * qty, true
}

// @Ensures p != nil
func FlatPricer() (p Pricer) {
	return Flat{}
}
```

```text
vego: postcondition may not hold: ok -> 0 <= cents <= 1000000, in Flat.Price used as a method of
Pricer at interfaces.go:69:9
```

Converting a nil pointer to an interface type gives an interface value that is not nil. Its methods are then called with a nil receiver. `vego` knows at the conversion whether the pointer may be nil, and the method is checked with that knowledge.

### What a conversion checks

An interface value can be called at any later time, so the method is checked against memory that `vego` knows nothing about. What `vego` knows of the value where it is converted is known in the check: the struct for a value receiver, and the pointer for a pointer receiver. What the pointer points to is not known. This has three consequences.

A method that writes what its receiver points to cannot be used as a method of an interface, because the contract of an interface method can list only parameters:

```go
// LineCounter counts the lines it prices.
type LineCounter struct {
	lines int
}

// @Requires c != nil And 0 <= qty <= 1000
// @Modifies c
// @Ensures ok -> 0 <= cents <= 1000000
func (c *LineCounter) Price(sku string, qty int) (cents int, ok bool) {
	if c.lines < 1000 {
		c.lines++
	}
	return 0, true
}

// @Requires c != nil
// @Ensures p != nil
func CountingPricer(c *LineCounter) (p Pricer) {
	return c
}
```

```text
vego: Price may modify c, which Pricer.Price may not modify; Pricer.Price can list only what its
parameters refer to, so a method that writes what its receiver refers to cannot be used as a
method of Pricer yet, in (*LineCounter).Price used as a method of Pricer at interfaces.go:90:9
```

A method that writes what its receiver refers to needs an interface whose method lists its receiver, as described in [Methods that write behind their receiver](#methods-that-write-behind-their-receiver). A `*bytes.Buffer` and a `*strings.Builder` cannot be converted to `io.Writer` even so, as described in [Converting a value of your own type](#converting-a-value-of-your-own-type), and no type can be converted to `sort.Interface` yet. A state of an interface value, described in [States of interface values](#states-of-interface-values), is not part of the value's memory.

A method with a pointer receiver cannot rely on what the receiver points to. A `Requires` clause that reads it, or a struct invariant of the receiver's type, cannot be proved in the check, and is reported there. A method with a value receiver gets the struct that was converted, so its invariant is proved from what is known where the value is converted. Give the method a value receiver and convert the struct, or make the conversion in code that is not verified. Through a pointer, a value receiver gets the struct as it is when the method runs, so its invariant cannot be proved there either.

A method with a value receiver called through a pointer reads the struct each time it is called, and panics if the pointer is nil:

```go
// Rated has a value receiver.
type Rated struct {
	Rate int
}

// @Requires 0 <= qty <= 1000
// @Ensures ok -> 0 <= cents <= 1000000
func (r Rated) Price(sku string, qty int) (cents int, ok bool) {
	if r.Rate < 0 || r.Rate > 1000 {
		return 0, false
	}
	return r.Rate * qty, true
}

// @Ensures p != nil
func RatedPricer(r *Rated) (p Pricer) {
	return r
}
```

```text
vego: Rated.Price has a value receiver, and the pointer that the interface value holds may be
nil, in Rated.Price used as a method of Pricer at interfaces.go:109:9
```

### Methods that write behind their receiver

A method of an interface can write memory that the value it is called on holds, as a buffer writes its contents. Say so with a `Receiver` annotation and the receiver in `Modifies`:

```go
// Recorder keeps the lines it is given in memory of its own.
type Recorder interface {
	// Record adds a line.
	//
	// @Receiver r
	// @Requires |line| <= 100
	// @Modifies r
	// @Ensures True
	Record(line string)
}
```

The memory that the methods of a value may write in this way is the value's footprint. `vego` does not know what the footprint holds. A function that calls `Record` lists the value in `Modifies`, as it lists a pointer whose struct it writes:

```go
// Lines counts the lines that were logged.
type Lines struct {
	Total int
}

// @Requires r != nil And t != nil And 0 <= t.Total < 1000 And |line| <= 100
// @Modifies r, t
// @Ensures t.Total' = t.Total + 1
func Log(r Recorder, t *Lines, line string) {
	r.Record(line)
	t.Total++
}
```

Without `r` in `Modifies`, the call is reported:

```go
// @Requires r != nil
// @Ensures True
func Forgot(r Recorder) {
	r.Record("start")
}
```

```text
vego: r.Record may modify the footprint of r, which Forgot may not modify; list it in a // @Modifies clause
```

After the call, `vego` forgets everything that may lie in the footprint of `r`. It keeps what the other parameters reach without going through an interface value, such as the struct that `t` points to and what its fields point to, and memory that the function made itself. A function may assume that the footprint of a parameter it lists in `Modifies` holds none of what its other parameters reach, and every verified caller must show it. A caller shows it by where its arguments come from. An argument that it got from its own parameters, by reading fields, elements, and map entries, or that it made itself, is fine, as `t` is here:

```go
// @Requires r != nil And t != nil And 0 <= t.Total < 1000
// @Modifies r, t
// @Ensures True
func Start(r Recorder, t *Lines) {
	Log(r, t, "start")
}
```

The value passed for the footprint must be a parameter that the caller's own `Modifies` lists. A function can return memory that it got from somewhere other than its arguments, such as its own package or a call it made. So an argument that a call returned is refused, unless one of these holds:

- the contract of that call says that the result is new, with `fresh`;
- the contract says that the result lies within one of its arguments that is fine itself, with `within`;
- the call is of a verified function whose body returns only what its arguments reach or memory it made, and its arguments are fine. A getter such as `return u.cfg` is such a function.

A call through an interface value, as here, is none of these:

```go
// @Requires r != nil
// @Modifies r
// @Ensures True
func Note(r Recorder, t *Lines) {
	r.Record("note")
}

// LineCounts hands out a count it holds.
type LineCounts interface {
	// @Ensures t != nil
	Current() (t *Lines)
}

// @Requires r != nil And s != nil
// @Modifies r
// @Ensures True
func NoteFrom(r Recorder, s LineCounts) {
	Note(r, s.Current())
}
```

```text
vego: the footprint of what is passed to Note as r may hold memory that what is passed as s.Current() reaches, and
Note relies on it not doing so: it comes from the call of s.Current at footprints.go:59:10, whose contract does not
say that it is new or lies within an argument
```

The same refusal names a store when a value of unknown origin was stored into memory that the function reaches before the call, since the callee could then reach it. A call whose `Modifies` covers memory that can hold a pointer, a slice, or a map counts as such a store, since it may put there memory it got from anywhere. A verified function whose body stores only what its arguments reach or memory it made does not, as long as its arguments are fine.

The states of another interface value may lie in the footprint, so a write forgets them too. Close a value before you write through another, or require what you need again afterwards:

```go
// @Requires r != nil And c != nil And ~closed(c)
// @Modifies r, c
// @Ensures True
func RecordThenClose(r Recorder, c io.Closer) {
	r.Record("done")
	c.Close()
}
```

```text
vego: precondition of c.Close may not hold: ~closed(c)
```

A method writes behind its receiver only when the interface that declares it has no states. A method of an interface with states whose contract lists its receiver changes the states of the value and nothing else, as described in [Declaring a state on an interface of your own](#declaring-a-state-on-an-interface-of-your-own). An interface with states can still have a method that writes behind its receiver, from an interface without states that it embeds. Such a method keeps the states of the value it is called on. Converting a value of your own type to an interface with such a method is not supported yet, as [What a conversion checks](#what-a-conversion-checks) describes.

#### New values and values made over a writer

`fresh(r)` of an interface value whose methods write behind it means that the call created the value and all of its footprint. Writing through such a value writes only memory that the call made, so it needs no `Modifies`, and it keeps everything that existed before:

```go
// Recorders makes recorders whose footprints are new.
type Recorders interface {
	// @Ensures r != nil And fresh(r)
	New() (r Recorder)
}

// @Requires f != nil And t != nil
// @Ensures t.Total' = t.Total
func LogToNew(f Recorders, t *Lines) {
	r := f.New()
	r.Record("start")
}
```

A value made over a writer writes what that writer writes. `fresh(s, r)` says that everything `s` refers to was made by the call or lies in the footprint of `r`, which must be an interface value whose methods write behind it. A trusted function that wraps a recorder says so:

```yaml
trusted:
  guide.teeRecorder:
    reason: Makes a recorder that records into r and into memory it makes.
    requires:
      - "r != nil"
    ensures:
      - "s != nil And fresh(s, r)"
    keeps:
      r: [s]
    vouches: [s]
    modifies: []
```

A write through what it returns is then covered by `Modifies r`:

```go
// @Requires r != nil
// @Modifies r
// @Ensures True
func LogThroughTee(r Recorder) {
	s := teeRecorder(r)
	s.Record("tee")
}
```

Without `r` in `Modifies`, the write is reported:

```text
vego: s.Record may modify the footprint of s, which LogThroughTeeUnlisted may not modify; it may lie in the footprint
of r, as the contract of teeRecorder at footprints.go:97:7 says; list r in a // @Modifies clause
```

The second argument of `fresh` may also be a variadic parameter whose elements are such values, as in `fresh(result, readers)` of `io.MultiReader`. `vego` reads that clause only where a call writes each element out as its own argument. There it says that what the result refers to is new or lies in the footprint of one of those arguments. Where a call hands a slice whole, the clause says only that the value the result holds is new. The checks of the entry itself also read it that way, so a contradiction in such a clause is reported at a call that writes the elements out (see [Wrappers in package io](#wrappers-in-package-io)).

`within(m, r)` says that a pointer, a slice, or a map lies in the footprint of `r`, as a header lies in the response writer that hands it out. `within(p, bw)` for a `*bufio.Writer` or another value that owns memory (see [Writing through a buffer](#writing-through-a-buffer)) says that `p` lies in its struct or in what it owns. A value that a contract places within an interface value or an owner may be memory that a writer writes, so it cannot be passed to a function beside that writer, as described in [Methods that write behind their receiver](#methods-that-write-behind-their-receiver).

#### Converting a value of your own type

You can convert a pointer to a struct of your own to an interface whose methods write behind their receiver. The footprint of the interface value is the struct the pointer points to. Each method is checked against the interface's contract, and its `Modifies` must stay within that struct:

```go
// LineCount counts the lines it is given.
type LineCount struct{ N int }

// @Requires t != nil And |line| <= 100
// @Modifies t
// @Ensures True
func (t *LineCount) Record(line string) {
	if t.N < 1000000 {
		t.N++
	}
}

// @Requires t != nil
// @Modifies t
// @Ensures True
func Track(t *LineCount) {
	var r Recorder = t
	r.Record("start")
}
```

A call through `r` writes the struct that `t` points to, so `Track` lists `t`. Without it, the call is reported:

```text
vego: r.Record may modify the footprint of r, which TrackUnlisted may not modify; it is the memory that t points to,
converted at conversions.go:33:19; list t in a // @Modifies clause
```

A struct that your function makes needs nothing listed. After a call through the interface value, the struct is not known any more, so a read of it proves nothing about what it held before:

```go
// @Ensures n = 0
func TrackBack() (n int) {
	t := &LineCount{}
	var r Recorder = t
	r.Record("start")
	return t.N
}
```

```text
vego: postcondition may not hold: n = 0
```

A method that writes outside its own struct cannot be used this way. Here `Forward` writes the `LineCount` that its field points to:

```go
// Forward passes each line on to the tally it points to.
type Forward struct{ To *LineCount }

// @Requires f != nil And |line| <= 100
// @Modifies f.To
// @Ensures True
func (f *Forward) Record(line string) {
	if f.To != nil {
		f.To.Record(line)
	}
}
```

```text
vego: Record may modify what it calls f.To, which Recorder.Record may not modify; it is not part of the footprint of
*Forward, which is the struct f points to, in (*Forward).Record used as a method of Recorder at conversions.go:61:19
```

A nil pointer converts too, and its footprint is empty.

The footprint is fixed when the value is converted. A value converted in a loop and called after the loop has a footprint about which nothing is known there, so the call needs everything it may write listed, and is usually refused. Convert the value before the loop.

A `*bytes.Buffer` and a `*strings.Builder` cannot be converted to an `io.Writer`. Their `Write` panics when the buffer is too large to grow, and the contract of `(io.Writer).Write` has no bound for it:

```go
// @Ensures True
func BufferAsWriter() {
	var b bytes.Buffer
	var w io.Writer = &b
	fmt.Fprintf(w, "%d items", 3)
}
```

```text
vego: cannot verify BufferAsWriter: converting a value of type *bytes.Buffer to io.Writer is not supported: its Write
may panic when the buffer is too large to grow, and the contract of (io.Writer).Write has no bound for it; pass the
Buffer itself to fmt.Fprintf, Fprint, or Fprintln, which then calls its own Write, or write what you format with its
own WriteString, as in b.WriteString(fmt.Sprintf(...))
```

Pass the buffer itself to `fmt.Fprintf`, `fmt.Fprint`, or `fmt.Fprintln`. `vego` then checks the call as `fmt.Sprintf` followed by the buffer's own `Write` (see [Formatting into a buffer](#formatting-into-a-buffer)):

```go
// @Ensures True
func FormatToBuffer() {
	var b bytes.Buffer
	fmt.Fprintf(&b, "%d items", 3)
}
```

A `*bufio.Writer` cannot be converted to an `io.Writer` either, because its `Write` calls through the writer it keeps (see [Interface values that call interface values](#interface-values-that-call-interface-values)). Pass it as a `*bufio.Writer`, or pass it to `fmt.Fprintf` itself.

### Interface values that call interface values

Code that an interface value made by verified code runs cannot call through an interface value or a function value. The reason is the same as for function values: no contract has a `Variant`, so nothing would prove that such calls end. See [Function values that call function values](#function-values-that-call-function-values). A type that wraps another interface value cannot be converted, and its method is itself reported, since the value it wraps may be one of its own type:

```go
// Logging wraps a pricer.
type Logging struct {
	Inner Pricer
}

// @Requires l.Inner != nil And 0 <= qty <= 1000
// @Ensures ok -> 0 <= cents <= 1000000
func (l Logging) Price(sku string, qty int) (cents int, ok bool) {
	return l.Inner.Price(sku, qty)
}

// @Requires inner != nil
// @Ensures p != nil
func LoggedPricer(inner Pricer) (p Pricer) {
	return Logging{Inner: inner}
}
```

```text
vego: this call may not end: Logging.Price calls l.Inner.Price(sku, qty) at interfaces.go:147:9,
which may run Logging.Price; a cycle that goes through a call with no static callee, of an interface
method or a function value, or through code of another package, cannot be shown to end, since no
Variant can be checked across such a call. Break the cycle
vego: cannot verify LoggedPricer: Price may call through a function value or an interface value,
and code that an interface value runs cannot do that yet: no contract of a function type or of a
method of an interface has a variant, so nothing would prove that such calls end; Price calls
through the interface value l.Inner. Make the value in code that is not verified, or keep that
call out of what Price runs
```

A struct that embeds an interface value gets the methods of that value, which call through it. Such a struct cannot be converted either.

A decorator can be verified today when it wraps a concrete type, whose method it calls with a static call:

```go
// RatedLogging wraps a Rated, a concrete type, and so calls its method
// statically.
type RatedLogging struct {
	Inner Rated
}

// @Requires 0 <= qty <= 1000
// @Ensures ok -> 0 <= cents <= 1000000
func (l RatedLogging) Price(sku string, qty int) (cents int, ok bool) {
	return l.Inner.Price(sku, qty)
}

// @Ensures p != nil
func LoggedRated(inner Rated) (p Pricer) {
	return RatedLogging{Inner: inner}
}
```

Both functions verify. A decorator that wraps any `Pricer`, as `Logging` does, cannot be verified yet.

### Converting between interfaces

An interface value can be converted to an interface whose methods it has from the same declarations, as through embedding:

```go
// Catalog is a pricer that also reports a size.
type Catalog interface {
	Pricer
	Sized
}

// @Ensures (p = nil) <-> (c = nil)
func AsPricer(c Catalog) (p Pricer) {
	return c
}
```

The converted value is nil exactly when the original is. Converting to an interface that declares a method of the same name itself is refused, because its contract may differ. An interface type written in place, such as `interface{ Pricer }` as the type of a parameter, is not supported if it embeds a declared interface. Go treats two such types as the same type whenever their methods have the same names and signatures, so a value could pass from one contract to another without a conversion. Declare a named type instead, as in `type PricerOnly interface{ Pricer }`.

A value of any type that `vego` supports can be converted to `any`. An `any` can be held, passed, and compared with nil, and nothing else can be done with it. An error converted to `any` is nil exactly when the error is nil.

### Comparing interface values

An interface value can be compared only with `nil`. `==` on two interface values compares the types and values they hold, which `vego` does not know, and panics when both hold the same type and that type is not comparable:

```go
// @Ensures same
func SamePricer(p, q Pricer) (same bool) {
	return p == q
}
```

```text
vego: cannot verify SamePricer: comparing interface values is not supported yet: == compares the
types and values they hold, which are not known, and panics when both hold the same type and it
is not comparable; compare with nil instead
```

Type assertions and type switches are not supported either.

A formula can compare two interface values. `a = b` says that they are the same value: one was copied from the other, by an assignment, a conversion to another interface type, or a call that hands it on. It is not Go's `==`. Two conversions of one concrete value are two values, so a function that returns `any(p), any(p)` proves `a != b`, although `a == b` is true in Go. A contract that says a function hands back what it was given, or that a field keeps its value, uses this form:

```go
// @Requires a != nil And b != nil And a != b
// @Modifies a, b
// @Ensures a.Value' = b.Value And b.Value' = a.Value
func Swap(a, b *Link) {
	a.Value, b.Value = b.Value, a.Value
}
```

An interface value and an error cannot be compared in a formula. An error is modelled apart from other interface values (see [Errors](#errors)).

### States of interface values

Some interfaces have a protocol. A value of `io.Closer` must not be closed twice, and a transaction is committed only after it began. A contract speaks of such a protocol through a state of the interface value. A state is a boolean that no Go code reads or writes. Only contracts speak of it.

`vego` ships one state for an interface. `closed(c)` is true once `Close` has been called on the value that `c` holds. The shipped contract of `(io.Closer).Close` requires `~closed(c)` and ensures `closed(c')`, where `c` is the value that `Close` is called on:

```go
// ReadOnce reads once into buf and closes rc.
//
// @Requires rc != nil And ~closed(rc) And |buf| > 0
// @Modifies rc, buf
// @Ensures closed(rc') And 0 <= n <= |buf|
func ReadOnce(rc io.ReadCloser, buf []byte) (n int, err error) {
	defer rc.Close()
	return rc.Read(buf)
}
```

`io.ReadCloser` has `Close` from `io.Closer`, so its values have the state `closed` too. The documentation of `io.Closer` says that the behaviour of a second `Close` is undefined. `vego` reports a `Close` of a value that may be closed:

```go
// @Requires c != nil And ~closed(c)
// @Modifies c
// @Ensures True
func CloseTwice(c io.Closer) {
	c.Close()
	c.Close()
}
```

```text
vego: precondition of c.Close may not hold: ~closed(c)
```

The message shows the clause as the contract of `Close` writes it. A function that calls `Close` on a value it is given requires `~closed` of it, as `ReadOnce` does.

`Close` changes the state of the value it is called on. So a function that closes a value lists it in `Modifies`, as `ReadOnce` lists `rc`. `Modifies rc` for an interface value covers the states of what `rc` holds, and nothing else. After `rc.Close()`, a caller knows `closed(rc')`. `Read` keeps the state. A method whose contract does not list its receiver in `Modifies` changes none of the states of the receiver, and the contract of `Read` does not list it.

For a field, `Modifies resp.Body` covers the states of the body:

```go
// @Requires resp != nil And resp.Body != nil And ~closed(resp.Body)
// @Modifies resp.Body
// @Ensures closed(resp.Body')
func Status(resp *http.Response) (code int) {
	defer resp.Body.Close()
	return resp.StatusCode
}
```

`Modifies resp.Body` does not cover the field `Body` itself. To assign the field, list the struct that holds it, as in `Modifies resp`:

```go
// @Requires resp != nil
// @Modifies resp.Body
// @Ensures True
func Replace(resp *http.Response, body io.ReadCloser) {
	resp.Body = body
}
```

```text
vego: resp.Body is assigned, which Replace may not modify: // @Modifies resp.Body covers the
states of what the interface value resp.Body holds, not the place that holds it; to assign it,
list the struct that holds it
```

#### Which values share a state

A state belongs to what an interface value holds, not to the variable. A copy of an interface value has the same state. So does the value converted to an interface that it embeds, as `rc` converted to `io.Closer`, and the value stored in an `any`. Closing one of them closes the others.

Two interface values that `vego` cannot tell apart may hold the same value, or one may wrap the other. Two parameters are told apart when the contract lists one of them in `Modifies` and both have states. The function then assumes that, unless one of them is nil, they share no state, and every verified caller must show this:

```go
// @Requires a != nil And b != nil And ~closed(a) And ~closed(b)
// @Modifies a, b
// @Ensures closed(a') And closed(b')
func ShutBoth(a, b io.Closer) {
	a.Close()
	b.Close()
}

// @Requires resp != nil And resp.Body != nil And c != nil
// @Requires ~closed(resp.Body) And ~closed(c)
// @Modifies resp.Body, c
// @Ensures True
func ShutWithBody(resp *http.Response, c io.Closer) {
	ShutBoth(resp.Body, c)
}
```

```text
vego: the interface values passed to ShutBoth as a and b may share their states: they may be
one value, hold one value, or hold a value and one that wraps it, and ShutBoth may rely on them
not doing so
```

`ShutWithBody` cannot show it. Its caller may pass `resp.Body` as `c`. Passing one value as both `a` and `b` is refused too, since `ShutBoth` would close it twice. Interface values in memory, such as the bodies of two responses or the elements of a slice, and the values that calls return, are not assumed to share no state. Closing one of them makes the state of the others unknown.

#### Values that a trusted function returns

A trusted function can say that the interface value it returns is new and not closed. `fresh(rc)` for an interface value means that the call created what `rc` holds, so that it shares no state with anything that existed before the call:

```yaml
  example.com/files.open:
    reason: >-
      open returns what os.Open returns, as an io.ReadCloser. When err is
      nil, rc holds a new *os.File that nobody has closed. Its Read and
      Close meet the shipped entries.
    vouches: [rc]
    modifies: []
    ensures:
      - "err = nil -> rc != nil And ~closed(rc) And fresh(rc)"
```

```go
// @Ensures True
func FirstByte(name string) (b byte, err error) {
	rc, err := open(name)
	if err != nil {
		return 0, err
	}
	defer rc.Close()
	buf := make([]byte, 1)
	if _, err := rc.Read(buf); err != nil {
		return 0, err
	}
	return buf[0], nil
}
```

`FirstByte` needs no `Modifies` for `rc`, because a value that the call created is not memory that a caller can see. Without `fresh(rc)`, `rc` may hold a value that the caller holds, and closing it is reported as a change that `FirstByte` may not make. The result is listed under `vouches`, which claims that its methods meet their contracts. See [Function values and interface values that a trusted function returns](#function-values-and-interface-values-that-a-trusted-function-returns).

#### Declaring a state on an interface of your own

Declare a state with a `State` annotation in the doc comment of the interface type. To speak of the state in the contract of a method, name the receiver with a `Receiver` annotation in the doc comment of the method:

```go
// Tx is a transaction whose state open its methods change.
//
// @State open
type Tx interface {
	// Begin starts the transaction.
	//
	// @Receiver t
	// @Requires ~open(t)
	// @Modifies t
	// @Ensures (err = nil) <-> open(t')
	Begin() (err error)

	// Commit ends it.
	//
	// @Receiver t
	// @Requires open(t)
	// @Modifies t
	// @Ensures ~open(t')
	Commit() (err error)
}

// @Requires t != nil And ~open(t)
// @Modifies t
// @Ensures ~open(t')
func Transact(t Tx) (err error) {
	if err := t.Begin(); err != nil {
		return err
	}
	return t.Commit()
}
```

A `Commit` that may not follow a `Begin` is reported, as `CloseTwice` was:

```go
// @Requires t != nil And open(t)
// @Modifies t
// @Ensures True
func CommitTwice(t Tx) {
	t.Commit()
	t.Commit()
}
```

```text
vego: precondition of t.Commit may not hold: open(t)
```

A state can be declared only on a named interface type at package level, without type parameters, that declares at least one method itself. `type B io.Closer` declares no method of its own and cannot have a state. The name of the receiver must differ from the names of the parameters and results. A contract can use the receiver only as the argument of a state, as in `open(t)`, and in `Modifies`. `Modifies t` lets the method change every state of the value, also one that another interface declares, such as `closed` of a value whose interface also embeds `io.Closer`.

A method of an interface with states whose contract lists its receiver in `Modifies` changes the states of the value, and writes nothing else behind its receiver. To have a method that writes memory behind its receiver, declare it on an interface without states, and embed that interface. See [Methods that write behind their receiver](#methods-that-write-behind-their-receiver).

A declaration makes a claim about every value of the interface. Each method whose contract does not list the receiver in `Modifies` leaves every state of the value unchanged. This includes the methods that the interface has from interfaces it embeds, whose contracts were written without the state. If `Tx` embedded `io.Reader`, its `State` annotation would claim that `Read` never changes `open`. You must check this claim yourself against every implementation that reaches your verified code.

An interface of another module gets its states in the trust file, in a `state` section beside `trusted`. Its entries name the receiver with a `receiver` field:

```yaml
state:
  example.com/lib.Conn:
    started:
      reason: True between a Start that returned nil and the next Finish.

trusted:
  (example.com/lib.Conn).Start:
    reason: ...
    receiver: c
    requires: ["~started(c)"]
    modifies: [c]
    ensures: ["(result = nil) <-> started(c')"]
```

The same conditions apply as for a declaration in source, and the interface must be of another module. A trust file cannot declare states of an interface that has shipped states, such as `io.Closer`, or of a struct type. Modules built together must declare the same states for an interface, as they must give a method the same entry. See [One entry for each type in a build](#one-entry-for-each-type-in-a-build).

#### Making a value of an interface with a state

Verified code cannot yet convert a value of its own type to an interface whose contracts speak of a state:

```go
// @Ensures err = nil
func (quiet) Close() (err error) {
	return nil
}

// @Ensures c != nil
func Quiet() (c io.Closer) {
	return quiet{}
}
```

```text
vego: cannot verify Quiet: converting a value of type quiet to io.Closer is not supported yet:
io.Closer has the state closed, and the contract of Closer.Close speaks of it; nothing ties a
state to what the methods of quiet do until the memory a value owns is modelled, the next part
of interfaces. Make the conversion in code that is not verified
```

So a closer of your own cannot be passed as an `io.Closer`, an `io.ReadCloser`, or another interface with `Close` from `io.Closer`. Make the conversion in code that is not verified.

An entry of your own for `(io.Closer).Close` replaces the shipped one, and the state `closed` stays. An entry with `modifies: []` and no `receiver` claims that every closer from code that is not verified returns without panicking and writes nothing verified code can see, each time it is closed. Nothing then stops verified code from calling `Close` twice, so the claim covers a second call. You can make it for the closers you know: a `*os.File` returns an error from a second `Close` and does not panic. A type whose `Close` closes a channel panics the second time. Write the entry only if every closer that your callers pass meets the claim. Under such an entry, verified code can convert a closer of its own to `io.Closer`, since no contract in use speaks of the state.

### Interface values from code that is not verified

An interface value that verified code receives from code it does not verify is taken to meet the contracts of its methods. See [What a proof assumes](#what-a-proof-assumes). As for function values, an argument that can carry code nobody has seen cannot be passed to a method of an interface value. An interface value whose methods all have contracts can be passed.

An error that a method returns through an interface value has an unknown origin, unless the contract of the method vouches for it. Without that, the error can be returned, and compared with `nil` or with an error variable (see [Comparing errors](#comparing-errors)), but not formatted, wrapped, or searched with `errors.Is` (see [Asking errors.Is](#asking-errorsis)), and it cannot be passed to a trusted function that does not list it under `runs` (see [Arguments that carry code](#arguments-that-carry-code)):

```go
// Loader loads a number.
type Loader interface {
	// @Ensures True
	Load() (n int, err error)
}

// @Requires l != nil
// @Ensures True
func LoadWrapped(l Loader) (n int, err error) {
	n, err = l.Load()
	if err != nil {
		return 0, fmt.Errorf("load: %w", err)
	}
	return n, nil
}
```

```text
vego: cannot verify LoadWrapped: formatting err would run the methods of an error whose origin is not known; only an error made by errors.New or fmt.Errorf, here or in a verified function, or one that a contract vouches for, can be formatted; err is assigned l.Load() at trial.go:127:11, a call whose errors nothing vouches for
```

Return the error unchanged, or vouch for the errors of the method in its contract with `Vouches`:

```go
// VouchedLoader loads a number, and vouches for the errors it returns.
type VouchedLoader interface {
	// @Ensures True
	// @Vouches err
	Load() (n int, err error)
}

// @Requires l != nil
// @Ensures True
func LoadVouched(l VouchedLoader) (n int, err error) {
	n, err = l.Load()
	if err != nil {
		return 0, fmt.Errorf("load: %w", err)
	}
	return n, nil
}
```

`Vouches` lists error results of the method. It makes the claim that `vouches` makes in the trust file, described in [Errors that a trusted function returns](#errors-that-a-trusted-function-returns), about every error that a value of the interface returns there. `vego` checks the claim of every value that verified code makes of the interface: its method must return only errors of known origin there, made by `errors.New` or `fmt.Errorf` or vouched for. A value that returns an error it was given is reported:

```text
vego: Load may return an error whose origin is not known in err, and the contract of
VouchedLoader.Load vouches for the errors there; return only errors made by errors.New or
fmt.Errorf, or vouched for, in stale.Load used as a method of VouchedLoader at trial.go:161:9
```

Of every value that comes from code that is not verified, the claim is assumed, as the rest of the contract is (see [What a proof assumes](#what-a-proof-assumes)). Read the code that makes such values before you write the annotation. The contract of a function type can vouch for its errors in the same way.

A `Vouches` annotation adds to a contract, so a method with no other clause is reported. It belongs only in these two places. In the doc comment of a function it is reported, because the errors of a verified function are judged from its body, and those of a trusted function are vouched for in the trust file. For an interface of another module, an entry in the trust file can vouch for the errors of a method, as described in [Wrapping the errors of Read and Write](#wrapping-the-errors-of-read-and-write).

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
// @Predicate digits(s) ::= Forall k in [0, |s|) : '0' <= s[k] <= '9'
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

`Assert` states such a fact. `vego` must prove the assertion at that point, and can use it in everything that follows. It stands between two statements, or after the last statement of a block or of a `case` clause, where it is checked at the end of that block or clause.

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

At the default limit, `vego` does not prove all the postconditions of a function that writes one field through twenty-four or more different pointers, such as `p0.x = 1` through `p23.x = 1` with `@Ensures p0.x' = 1 And ... And p23.x' = 1`. The messages carry the note about the resource limit. With thirty pointers, `-vego.rlimit=40000000` proves them all. With twenty-three pointers such a function verifies at the default limit, and so do thirty writes through one pointer.

### A value that only an annotation reads

`Snapshot` names the value that a formula has at the point where the annotation stands. This is how an inner loop states that it moved past where the iteration began, so that the outer loop's `Variant` decreases:

```go
// Runs counts the runs of equal elements.
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
```

`start` is the value `i` had when the outer iteration began. Without the inner invariant `start < i`, `vego` knows nothing after the inner loop that shows that `i` grew, and reports `loop variant may not decrease: |A| - i`.

A snapshot is written `// @Snapshot name = value`, where the value is an integer expression or a formula. It is read in the state where the annotation stands, so it may use `old`, lengths, fields, and `fresh`, as an `Assert` there may. From there to the end of the innermost block, or of the `case` clause, that holds it, `name` in an annotation of the body is that value. No statement can change it, and it cannot be primed or put in `old`. A snapshot holds an integer or a boolean. A snapshot of a slice or a string is reported.

These rules keep one meaning for each name, and each break is reported:

- The name must not name anything visible where the snapshot stands, such as a variable, a constant, or a function such as `max`, and must not be a word of the annotation language.
- Nothing in its scope may declare the name again, in Go or in another snapshot, and no quantifier there may bind it.
- An annotation must use it. A snapshot that nothing names is an error, as an unused variable is in Go.
- An annotation inside a function literal cannot name a snapshot taken outside the literal. Take it inside the literal.
- A snapshot must stand above the `Invariant` and `Variant` lines of a loop. One between or below them is reported.

### Finding out where the time goes

`-vego.cost` prints, on standard error, what verifying each function asked of Z3. It changes no message and no exit status.

```sh
laas -vego -vego.cost ./...
```

For `Load` from [Wrapping the errors of Read and Write](#wrapping-the-errors-of-read-and-write), under the entries shown there, in a file `foreign.go` that declares it at line 54, it prints:

```text
foreign.go:54:6: vego cost of Load: 44 problems, 2094455 resource units, 162773 bytes, 1.60 s
	foreign.go:54:6: 2 questions of the always-fails check stopped at a limit
```

The first line counts the problems that `vego` handed to Z3, the work Z3 counted for them, and the size of their text. These three numbers are the same on every run with the same `laas`, Go, and Z3, unless a question ran past the time limit or out of memory, which depend on the machine (see the notes in [Helping the prover](#helping-the-prover)). The seconds are the time spent on the function. They include time spent waiting for a free Z3 process while other packages are verified at the same time, so they change with the machine and its load. They do not include the time spent on other functions, such as checking a trusted contract that the function calls, which get a line of their own.

Each indented line gives a place in the function and a kind of question that stopped at a limit there. A question that stops at its limit has used all the work it is allowed, so these lines usually show where the time goes. The kinds are:

- a proof obligation;
- a question of the always-fails check, which looks for an input on which the contract makes the function succeed (see [Saying when a function succeeds](#saying-when-a-function-succeeds));
- a contradiction check, which asks whether what is known at a place, such as after a call of a trusted function, contradicts itself;
- a check whether a `Modifies` entry is needed;
- a quick check, such as whether an `append` writes in place.

The work each is allowed:

| Kind | Limit |
| --- | --- |
| proof obligation | `-vego.rlimit` |
| question of the always-fails check | `-vego.rlimit`, 200000 units for whether an outcome depends on a call, and a quarter of `-vego.rlimit` for a proposal of an input |
| contradiction check | 200000 units, and `-vego.rlimit` for the check of a trusted contract, of a contract of a type, and of the invariants of a type; each is first asked with a tenth of that, at most 200000 units |
| check whether a `Modifies` entry is needed | 200000 units |
| quick check | 200000 units |

With `-vego.cache`, a function whose answers came from the cache has a clause at the end of its first line, such as `, 13 answered from the answer cache on disk`. See [Keeping answers between runs](#keeping-answers-between-runs).

A contradiction check is first asked of Z3 with a different search, at a tenth of the check's limit. That search settles some checks that the usual one leaves open, and leaves open some that the usual one settles. When that search does not settle the question, the check is asked again in full, so a function can count two problems for one check.

A proof obligation that stops at a limit draws a message with the note. So does the always-fails check when it reports a contract and a question of its search stopped at a limit. Other questions draw no message of their own. When one of them stops at a limit, `vego` goes on as when a proof fails: a path counts as possible, a `Modifies` entry counts as needed, an outcome counts as one that may depend on a call, a contradiction counts as not found, and an input that the search did not find counts as not found, which can make `vego` report the contract.

### Using the idle Z3 processes

`vego` verifies the functions of a package one after another, and `laas` runs up to four Z3 processes. When a package is verified while the other processes are idle, as when you run `laas` on one package, up to three more verifiers in the run verify the package's later functions on those processes. They report nothing. When the verification reaches such a function, the answers it needs are ready. A package of several slow functions is verified up to three times faster that way. In one package of 24 functions, a run went from 91 s to 33 s. The messages, the exit status, and what `-vego.cost` counts are the same as without it. If a run fails with `internal error of vego`, run it again with `-vego.speculate=false` and report the message.

The extra verifiers use memory: in the runs measured, up to 13% more than without them. On a machine that is short of memory, turn them off:

```sh
laas -vego -vego.speculate=false ./...
```

### Keeping answers between runs

`-vego.cache` names a directory where `vego` keeps the answers of Z3 from one run to the next:

```sh
laas -vego -vego.cache="$HOME/.cache/vego" ./...
```

On the next run, a question that is the same as one asked before is answered from the directory, and Z3 is not asked again. After a small edit, most of the questions of a package are the same as before. In one package of 24 functions that took 90 s, changing one `Requires` clause left 502 of 597 questions the same.

The answers are the same with the cache and without it. Each run that uses the cache solves again a random sample of the answers it reads, about one in 256, and fails the package if Z3 now answers otherwise. A wrong entry is therefore found in some runs and not in others.

A package that used an answer from the directory says so on standard error, with a line such as:

```text
vego: 157 of the 157 answers of Z3 for example.com/ring came from the answer cache in /home/you/.cache/vego
```

These counts depend on what the directory held when the run asked. A run on a warm directory counts answers that a run on an empty one does not. Two runs that use one directory at the same time can count differently, depending on which run solved a question first and wrote its answer. The other messages and the other figures of `-vego.cost` are the same in every run.

The trust report names the directory too, because the proofs then rest on what it holds. See [The trust report](#the-trust-report) and [What a proof assumes](#what-a-proof-assumes).

Give a directory that does not exist yet, or an empty one. `laas` marks it as an answer cache with a file `CACHEDIR.TAG`, and refuses a directory that holds anything else and has no such mark. The directory must also be outside every module and repository: `laas` refuses one inside a directory that holds `go.mod`, `.git`, or the files of another version control system. A cache committed to a repository would carry its answers into other people's runs. On a machine where `/tmp` itself holds a repository, every directory under `/tmp` is refused for that reason. Use a directory under your home directory, such as `$HOME/.cache/vego`. The flag works on Linux only, because `vego` reads `/proc` to identify the files that Z3 runs.

The answers are kept for the Z3 binary that gave them, together with the libraries it loads and the processor. Another Z3, or the same one after a system update that changes its libraries, starts with an empty directory of its own. `-vego.z3` must name the Z3 binary itself, not a script that starts it.

When `vego` cannot trust what it finds in the directory, the package fails with a message such as the one below, and so does every package verified after it in the run. `laas` exits with status 1. Packages verified before it keep their messages.

```text
vego: the answer cache entry /home/you/.cache/vego/z3-0f5c.../c5/a4db... is damaged: it does not end in its hash; to empty the cache, remove /home/you/.cache/vego
```

To empty the cache, remove the directory. Once a day, answers not used for five days are removed, and then the oldest until the directory holds at most 1 GB. `vego` removes only files that it wrote there.

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
vego: A[i] is assigned, which FillUnlisted may not modify; list it in a // @Modifies clause, as A
```

A caller can rely on everything outside the list being unchanged. About the memory in the list, it knows only what the `Ensures` clauses state. So keep the list as small as possible. With `Modifies c.n`, callers keep what they know about the other fields of `c`. With `Modifies c`, they lose it.

`vego` also reports a `Modifies` entry that the function body never needs.

An entry must name memory that the caller can see. A parameter passed by value is a copy, so `Modifies n` for an `int` parameter is reported as `in Modifies annotation: n is passed by value, so the caller cannot see a change to it`.

A `Modifies` path is evaluated when the function is called. `Modifies s.items` refers to the slice that `s.items` held at that moment, even if the function later stores a different slice in the field.

### Before and after

In an `Ensures` clause, a name refers to the value at the time of the call. To refer to memory as it is when the function returns, add a prime. In the example, `A'[k]` is element `k` on return and `A[k]` is the element at the time of the call. For a field, write `c.n'`. The prime comes after the name or field and before any index: `s.items'[0]`.

The prime is only needed for memory that the function can change. A parameter that is a plain value, such as `v`, never takes one.

A clause of an `Ensures` that names no result and nothing primed speaks only of the state at the call. `vego` reports such a clause when it reads memory that the function may modify, because the prime is then most likely missing:

```go
// @Requires l != nil And l.Max = 7
// @Modifies l.Max
// @Ensures l.Max = 7
func SetMax(l *Limits) {
	l.Max = 7
}
```

```text
vego: the Ensures clause "l.Max = 7" names no result and nothing on return, so it speaks of the
state when SetMax is called, and it reads memory that SetMax may modify; write a prime for the
value on return, as in l.Max', or move the clause to a Requires
```

A clause joined with `And` is checked one part at a time. A clause that relates a result to the state at the call, such as `r = c.n`, or that reads only memory that the function cannot modify, is not reported. The same check applies to the contracts of function types, methods of interfaces, and trusted functions.

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

`append(A, B...)` adds every element of `B`, and `append(b, s...)` adds the bytes of the string `s` to a `[]byte`. The elements are copied as if through a temporary copy, so what is added is what `B` held before the write, also when `B` shares the array of `A`. The usual way to delete an element verifies:

```go
// @Requires 0 <= i < |A|
// @Modifies A
// @Ensures |result| = |A| - 1
// @Ensures Forall k in [0, i) : result[k] = A[k]
// @Ensures Forall k in [i, |A| - 1) : result[k] = A[k + 1]
func Remove(A []int, i int) (result []int) {
	return append(A[:i], A[i+1:]...)
}
```

Slice expressions `A[i:j]` and `A[i:j:k]`, `len`, `cap`, `make`, and slice literals are supported. A nil slice has length and capacity 0, so after `if a == nil` the function knows that `len(a)` is 0. `copy` is not supported yet: write the copy as a loop that assigns each element, or, when the two slices have the same length, as `dst = append(dst[:0], src...)`.

### Capacity and nil in a formula

`cap(A)` is the capacity of `A`, and `A = nil` says that `A` is nil. A nil slice has length 0, but a slice of length 0 need not be nil. So `|A| = 0` and `A = nil` are different conditions:

```go
// Reserve returns an empty slice with room for n elements.
//
// @Requires 0 <= n <= 1000
// @Ensures |r| = 0 And cap(r) = n And r != nil
func Reserve(n int) (r []int) {
	return make([]int, 0, n)
}

// @Ensures r != nil
func EmptyOf(A []int) (r []int) {
	return A[:0]
}
```

```text
vego: postcondition may not hold: r != nil
```

`A[:0]` of a nil slice is nil, so `EmptyOf` does not meet its contract.

Both forms can be primed and put in `old`, as in `cap(s.items')` and `old(A) = nil`. `cap` applies only to a slice. A string is never nil, and `s = nil` for a string `s` is reported.

### Slices that share no memory

Slice parameters of one element type are assumed not to overlap. Slices that a function reaches through memory are not: two fields of one struct may share an array. `apart(a, b)` says that two slices share no memory, up to their capacities:

```go
// Halves holds two slices that the type does not keep apart.
type Halves struct {
	front, back []int
}

// @Requires h != nil And |h.front| > 0 And |h.back| > 0 And apart(h.front, h.back)
// @Modifies h.front
// @Ensures h.front'[0] = 0 And h.back'[0] = h.back[0]
func ClearFront(h *Halves) {
	h.front[0] = 0
}
```

Without `apart(h.front, h.back)` in the `Requires`, `vego` reports `postcondition may not hold: h.back'[0] = h.back[0]`, because `h.back[0]` may be the element that the function writes.

A slice with no capacity shares no memory with anything. `apart` takes two slices of one element type. Slices of two element types never share memory, and `apart` of them is reported.

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

In a formula, a byte of a string is a number. Where the code tests `'0' <= s[i] && s[i] <= '9'`, the contract says `'0' <= s[i] <= '9'`, which means `48 <= s[i] <= 57`.

`vego` does not know how strings are ordered by `<`. A `range` over a string produces an unknown rune at each step and advances by one to four bytes.

`string(r)` of a rune, or of any other integer, is the UTF-8 encoding of the character, as in Go. `vego` knows its length and its bytes. A value that is not a character, such as a negative number or a surrogate, gives the three bytes of U+FFFD:

```go
// @Requires 0 <= r < 128
// @Ensures |s| = 1 And s[0] = r
func RuneString(r rune) (s string) {
	return string(r)
}
```

### Building text in a buffer

Verified code can write a `strings.Builder` and a `bytes.Buffer`. In a formula, `|b|` is the length of the buffer `b`, the number that `b.Len()` returns:

```go
// @Requires |parts| <= 1000 And (Forall i in [0, |parts|) : |parts[i]| <= 1000)
// @Ensures |r| <= 1001 * |parts|
func JoinWithCommas(parts []string) (r string) {
	var b strings.Builder
	// @Invariant 0 <= i And i <= |parts| And |b| <= 1001 * i
	// @Variant |parts| - i
	for i := 0; i < len(parts); i++ {
		b.WriteString(parts[i])
		b.WriteByte(',')
	}
	return b.String()
}
```

For a `bytes.Buffer`, `|b|` counts the bytes that have not been read yet. It is not what was ever written, and it is not the capacity. A formula cannot name the capacity of a buffer: `cap(b)` is reported as `cap(b): b is a strings.Builder, whose capacity no contract speaks of; its length |b| is what bounds what it can grow to`.

A method that writes panics when the buffer cannot grow to hold what it writes. So it requires a bound on the length of the buffer and on what it writes, as an `append` does (see [Allocation, panics, and termination](#allocation-panics-and-termination)). These methods have shipped contracts. Each also requires that `b` is not nil:

| Method | Requires | Ensures |
| --- | --- | --- |
| `Write(p)`, `WriteString(s)` of a `Builder` | <code>2 * (&#124;b&#124; + &#124;p&#124;) + 65536</code> at most `MaxAlloc` and `MaxInt` | <code>&#124;b'&#124; = &#124;b&#124; + &#124;p&#124;</code>, with the count written and a nil error |
| `WriteByte`, `WriteRune` of a `Builder` | the same with 1 or 4 bytes | the length grows by 1, or by the 1 to 4 bytes of the rune |
| `Grow(n)` of a `Builder` | `0 <= n`, and <code>3 * (&#124;b&#124; + n) + 65536</code> at most `MaxAlloc` and `MaxInt` | the length is kept |
| `Write`, `WriteString`, `WriteByte`, `WriteRune`, `Grow` of a `Buffer` | `0 <= n` for `Grow`, and for `k` the bytes written, or `n` of `Grow`, <code>3 * (&#124;b&#124; + k) + 65536 <= MaxAlloc</code> and <code>5 * (&#124;b&#124; + k) <= MaxInt</code> | as for a `Builder` |
| `Len`, `String` | nothing more | <code>result = &#124;b&#124;</code>, <code>&#124;result&#124; = &#124;b&#124;</code> |
| `Bytes` of a `Buffer` | nothing more | <code>&#124;result&#124; = &#124;b&#124;</code>, and the result lies within `b` |
| `Reset` | nothing more | <code>&#124;b'&#124; = 0</code> |
| `Truncate(n)` of a `Buffer` | <code>0 <= n <= &#124;b&#124;</code> | <code>&#124;b'&#124; = n</code> |

A bound such as `|b| <= 1000000` on the buffer and one on what is written is enough. When the bound is missing, the message says what is enough on the platform:

```go
// @Ensures True
func JoinUnbounded(parts []string) (r string) {
	var b strings.Builder
	for _, s := range parts {
		b.WriteString(s)
	}
	return b.String()
}
```

```text
vego: precondition of WriteString may not hold: 2 * (|b| + |s|) + 65536 <= MaxAlloc; it holds when |b| <=
10000000000000 and |s| <= 10000000000000
```

A function that writes a buffer it is given lists it in `Modifies`. `Modifies b` covers the struct and the array of the buffer:

```go
// @Requires b != nil And |b| <= 1000000 And |line| <= 1000
// @Modifies b
// @Ensures |b'| = |b| + |line| + 1
func AddLine(b *strings.Builder, line string) {
	b.WriteString(line)
	b.WriteByte('\n')
}

// @Ensures |r| = 6
func TwoLines() (r string) {
	var b strings.Builder
	AddLine(&b, "ab")
	AddLine(&b, "cd")
	return b.String()
}
```

A struct that holds a buffer by value owns its array too. `Modifies r` of a pointer to it covers that array, and `|r.text|` is the length of the buffer:

```go
// LineBook collects lines in a Builder it holds.
type LineBook struct {
	lines int
	text  strings.Builder
}

// @Requires r != nil And |r.text| <= 1000000 And |line| <= 1000 And r.lines < 1000000
// @Modifies r
// @Ensures |r.text'| = |r.text| + |line| + 1 And r.lines' = r.lines + 1
func (r *LineBook) Add(line string) {
	r.text.WriteString(line)
	r.text.WriteByte('\n')
	r.lines++
}
```

An element of a slice of buffers is listed as the element, as in `Modifies bs[0]`. `Modifies bs` covers the elements but not the arrays they own.

What `Bytes` returns lies in the array of the buffer. A later write may overwrite it, also after `Reset`, which keeps the array:

```go
// @Ensures r
func Overwritten() (r bool) {
	var b bytes.Buffer
	b.WriteString("abc")
	p := b.Bytes()
	first := p[0]
	b.Reset()
	b.WriteByte('z')
	return p[0] == first
}
```

```text
vego: postcondition may not hold: r
```

A buffer is not copied, as described in [Writing through a buffer](#writing-through-a-buffer). To format into a buffer, pass it to `fmt.Fprintf`, as described in [Formatting into a buffer](#formatting-into-a-buffer). A buffer cannot be converted to an `io.Writer`, and a struct that holds one by value cannot be converted to an interface whose methods write behind their receiver.

These methods have no shipped contract, and a call of one is reported:

- the methods that read, such as `Read`, `ReadByte`, `ReadString`, and `Next`;
- `ReadFrom` and `WriteTo`, which call through the reader or writer they are given;
- `Cap`, `Available`, and `AvailableBuffer`, which speak of the capacity;
- `bytes.NewBuffer` and `bytes.NewBufferString`, which take over memory they are given.

The contracts say how long a buffer is. They say nothing of what it holds.

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
| an interface value | `Modifies rc`, `Modifies resp.Body` | the states of what the value holds; see [States of interface values](#states-of-interface-values) |

The first, third, fourth, and fifth rows apply wherever the path ends. A path that ends in a function value covers the field that holds it, as for a number. `Modifies s.items` covers the elements of the slice and not the field `items`. In the same way, `Modifies s.next` for a pointer field covers the struct that `next` points to, and `Modifies m[k]` for a map of pointers covers the struct that the pointer stored under `k` points to.

To assign a field that holds a slice, pointer, map, or interface value, list the struct that contains it. A method that assigns `s.n` and writes `s.items[i]` needs `Modifies s.n, s.items`. A method that assigns `s.items` needs `Modifies s`.

A struct can have a field of a type that `vego` does not support, such as a channel. Verified code cannot read or assign that field, but it is still part of the struct. Assigning the whole struct writes that field too. For a pointer `h` to such a struct, `*h = H{}` needs `Modifies h`, and entries for the other fields are not enough. A struct with an array field is the exception. It is not supported at all.

### Types declared inside a function

A type can be declared inside a function body, as Go allows. It is a type of its own, and a local struct with the same fields as a type of the package converts to it, as in Go. A type declared inside a function cannot have annotations. An invariant on a local struct, or a contract on a method of a local interface or on a local function type, is reported as `Invariant annotation stands on a type declared inside F; a type declared inside a function cannot have annotations, so declare it at package level to give it an invariant or a contract`. Declare the type at package level to give it one. An `Assert` or a `Snapshot` directly above a local type is read in the body, as anywhere between statements.

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

In an `Ensures`, `fresh(x)` means that the memory `x` refers to on return was allocated during the call. In an `Invariant` or an `Assert` inside a body, `fresh(x)` means that the memory `x` refers to there was allocated since the function was entered. That is the memory a function may write without listing it in `Modifies`, so a loop can use it to keep that knowledge (see [What a loop forgets about memory](#what-a-loop-forgets-about-memory)). `fresh` cannot stand in a `Requires` or in the invariant of a type, where no call has allocated anything yet, and both are reported.

`fresh` says only when the memory was allocated. It does not say that nothing else refers to the memory: two fresh slices may share one array, and a fresh pointer may have been stored where the caller can reach it. A proof that needs such a fact needs a clause that states it, such as `apart(a, b)` or `p != q`.

`within(a, b)` means that `a` lies inside the memory of `b`. Each argument of `fresh` and `within` is a pointer or a slice, and `fresh` also takes a map or an interface value. With interface values whose methods write behind them, `fresh` takes more than one argument and `within` takes such a value second, as described in [New values and values made over a writer](#new-values-and-values-made-over-a-writer). A slice includes its whole capacity. These edge cases apply:

- A slice with zero capacity has no memory, so it is `fresh` and is `within` anything.
- A nil interface value holds nothing, so it is `fresh`.
- A nil pointer and a nil map are not `fresh`, so `fresh(p)` also says that `p` is not nil.
- A nil pointer is `within` nothing.

For two pointers to structs, `within(p, l)` means that `p` points to `l`'s struct itself or to a field of it. That struct or field has `p`'s struct type, or a type with the same fields, tags ignored. The field may be held directly or in a struct that `l`'s struct holds, but not behind a pointer. So `@Modifies l` covers a write through `p` when the `Requires` says `within(p, l)`. When `p` points to a struct whose size is not zero and `l`'s struct has no such place, `within(p, l)` is an error.

`&x`, `&p.field`, and `&s[i]` are supported when the result points to a struct. Methods with pointer receivers can be called on variables, fields, and elements. Pointers to other types, such as `*int`, are not supported.

### The address of a field in a formula

A formula can name the address of a struct that it reaches through a pointer or an element of a slice, as in `&e.ring.root` and `&s[i]`. It is the pointer that the same expression gives in code, and it compares like any pointer:

```go
// Item is an element of a Ring, whose root marks where it starts.
type Item struct {
	next *Item
	ring *Ring
}

// Ring is a list that ends at its own root.
type Ring struct {
	root Item
	size int
}

// Next returns the item after e, or nil at the end of the ring.
//
// @Requires e != nil
// @Ensures result = nil <-> (e.ring = nil Or e.next = nil Or e.next = &e.ring.root)
// @Ensures result != nil -> result = e.next
func (e *Item) Next() (result *Item) {
	if p := e.next; e.ring != nil && p != &e.ring.root {
		return p
	}
	return nil
}
```

These rules apply:

- The path must go through a pointer or an element of a slice, and must end in a struct. `&x` of a variable, `&p.n` for a field `n` of type `int`, and `&h.f` for a struct `h` passed by value are reported.
- When the last pointer that the path goes through is nil, Go panics on `&e.ring.root`. In a formula the address is then nil. So `e.next = &e.ring.root` holds when `e.next` and `e.ring` are both nil. When an earlier pointer is nil, as `e` is here, nothing is known of the address.
- A primed path is read on return, wherever the prime stands. `&e.ring'.root` and `&e'.ring.root` both take the address in `e.ring` as it is on return.
- A pointer to a struct of size zero can be compared only with nil, as in code.

### A slice that grows inside a struct

A stack that appends to its own slice is simplest when the struct declares that it owns the slice:

```go
// @Owns items
type Pile struct {
	items []int
}

// @Requires p != nil And |p.items| < 1000000
// @Modifies p
// @Ensures |p.items'| = |p.items| + 1 And p.items'[|p.items|] = x
func (p *Pile) Push(x int) {
	p.items = append(p.items, x)
}
```

`Modifies p` covers the slice's array, and a caller may push again after a push. [Structs that own memory](#structs-that-own-memory) describes this in full.

A struct that does not own its slice needs most of the features above.

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

- If every write in the loop goes through a variable that the loop does not assign, or through a slice that the loop only appends to, `vego` forgets only the memory written that way. It keeps what it knew about all other memory. A call counts as such a write when it is passed the variable, or a pointer to a field of the struct the variable points to, as `h.mu.Lock()` passes `&h.mu`. For a write to one struct, or to some of its fields, `vego` forgets those fields of that struct. It keeps the other fields of that struct, and every struct that cannot lie where the written fields are. Two different pointers to one struct type point to structs that do not overlap, so for a struct with two fields of one struct type, a write of `p.b` keeps `q.a` when `p != q`.
- Otherwise `vego` forgets all memory of the same kind that the function may write. For `b.items[i]` that is the elements of every `[]int` the function lists in `Modifies` or allocated itself. Memory of that kind that existed when the function was called and is not in `Modifies` is still known to be unchanged.

`b.items[i]` is not a write through a variable, so the second rule applies. Copy the slice to a local variable first, and only that slice is forgotten:

```go
items := b.items
for i := range items {
	items[i] = 0
}
```

The other way to keep a fact is to state it as a loop invariant, here `// @Invariant count[0] = |b.items|`.

A loop also forgets that a slice belongs to the function, when the loop assigns the slice the result of a call. Here `out` starts as `nil`, which has no memory, and `grow` returns either a new slice or one inside its argument:

```go
// grow appends x.
//
// @Requires |s| < 1000000
// @Modifies s
// @Ensures |result| = |s| + 1
// @Ensures fresh(result) Or within(result, s)
func grow(s []int, x int) (result []int) {
	return append(s, x)
}

// CopyThrough appends through grow in a loop.
//
// @Requires |A| <= 1000
// @Ensures True
func CopyThrough(A []int) (out []int) {
	// @Invariant |out| <= i
	for i := range A {
		out = grow(out, A[i])
	}
	return out
}
```

```text
vego: grow may modify out, which CopyThrough may not modify; out is a result, and a // @Modifies
clause names memory only by a path from a parameter: if what out refers to may be memory of the
caller, list it by the parameter it comes from; if it is memory that CopyThrough made, nothing here
shows that, since a loop that assigns out forgets where its memory came from: say so with
// @Invariant fresh(out) on the loop
```

At the head of the loop `out` is a slice of which nothing is known, so it may be memory that the caller holds. A result cannot be listed in `Modifies`: `// @Modifies out` is reported as `in Modifies annotation: out is not a parameter`. Say in the invariant that the slice is the function's own:

```go
// CopyFresh says that out is its own.
//
// @Requires |A| <= 1000
// @Ensures |out| = |A|
func CopyFresh(A []int) (out []int) {
	// @Invariant |out| = i And fresh(out)
	for i := range A {
		out = grow(out, A[i])
	}
	return out
}
```

In a body, `fresh(out)` means that the memory `out` refers to was allocated since the function was entered. The invariant holds on entry to the loop, because a nil slice has no memory. `grow` keeps it, because it returns new memory or memory inside `out`. When `out` may really be memory of the caller, as after `out = A`, the invariant is reported as `loop invariant may not hold on entry: fresh(out)`, and the slice has to be listed by the parameter it comes from.

A slice that the loop only appends to with `append` keeps what is known of it, and needs no such clause:

```go
// CopyAppend appends in the loop itself.
//
// @Requires |A| <= 1000
// @Ensures |out| = |A|
func CopyAppend(A []int) (out []int) {
	// @Invariant |out| = i
	for i := range A {
		out = append(out, A[i])
	}
	return out
}
```

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

`append` and the other built-in functions are not ordered like calls, because the Go specification does not say that they are. An `append` runs after its operands, and nothing else orders it. So when an `append` writes into the array of its slice, the operands of the targets of the same assignment may be evaluated before or after that write. Reads there are checked like any other read. A call there must not modify anything, its receiver, parameters, and results must refer to no memory, and its contract must name no package-level variable that refers to memory. Integers, floats, booleans, strings, errors, and structs of these refer to no memory. A call that is passed a pointer, a slice, or a map is refused:

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

`vego` does not assume or check the invariant for a struct inside a slice, a map, or another struct, or for one behind a pointer field, unless the struct that holds it owns that field (see [The invariant of what a struct owns](#the-invariant-of-what-a-struct-owns)). State it explicitly where you need it. For example, take this type:

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

A function of another package cannot state such a clause when the invariant names unexported fields, because a contract can name an unexported field only in the package that declares the struct (see [Names](#names)). It then cannot call a method that needs the invariant of a struct it reaches through a field, such as `s.store.Delete(id)` for a `store` whose invariant is `tasks != nil`, unless the struct owns that field. The invariant of a struct includes the invariants of the structs its owned pointer fields point to, and of the owners it holds by value; see [The invariant of what a struct owns](#the-invariant-of-what-a-struct-owns).

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

When the invariant names fields that the function cannot name, as for a struct of another package, write `valid(s)` in place of its clauses: `// @Invariant valid(s)`. `valid(x)` is true when the invariants of the struct `x` is or points to hold, with those of what it owns.

### A trusted function does not restore it

After a call to a trusted function that may modify a struct, `vego` does not assume the invariant of that struct, because nothing proved it.

## Structs that own memory

A struct can own the memory that some of its fields refer to. Write `// @Owns` with the names of those fields in the doc comment of the struct type:

```go
// Pile owns the array of its slice.
//
// @Owns items
type Pile struct {
	items []int
}

// @Requires p != nil And |p.items| < 1000000
// @Modifies p
// @Ensures |p.items'| = |p.items| + 1 And p.items'[|p.items|] = x
func (p *Pile) Push(x int) {
	p.items = append(p.items, x)
}

// @Requires p != nil And |p.items| < 1000
// @Modifies p
// @Ensures |p.items'| = |p.items| + 2
func PushTwice(p *Pile) {
	p.Push(1)
	p.Push(2)
}
```

`Push` lists only `p`. `Modifies p` covers the struct and everything `p` owns: the array of `items` up to its capacity. `PushTwice` can call `Push` twice, because after each call the array that `p` owns is either the one it owned before or new memory. Compare [A slice that grows inside a struct](#a-slice-that-grows-inside-a-struct), where a struct that does not own its slice needs a `fresh` clause for this.

A function that makes a pile needs no `Modifies` at all to push onto it:

```go
// @Ensures r != nil And |r.items| = 2
func NewPile() (r *Pile) {
	r = &Pile{}
	r.Push(1)
	r.Push(2)
	return r
}
```

An owned field can hold:

- a slice, whose array up to its capacity is owned;
- a map, which is owned;
- a pointer to a struct, whose struct is owned, with what that struct owns in turn;
- an interface value, whose footprint is owned, with the states of what it holds (see [Methods that write behind their receiver](#methods-that-write-behind-their-receiver)).

The field must be unexported, so that only its package can change what it refers to. The struct must be declared at package level, without type parameters. A struct cannot own itself, so a list node with `@Owns next` is refused. A struct type with the same fields as an owner owns what the owner owns, because Go converts between the two. The elements of an owned slice and the values of an owned map are not owned: a `[]*Node` owns the array of pointers, not the nodes.

An owner cannot be copied or overwritten as a whole, since the copy would share what the original owns. Pass a pointer to it.

### What an owned field may refer to

An owned field may come to refer only to memory made since the function was called, or to part of what it referred to just before. `vego` checks this at every store into an owned field:

```go
// @Requires p != nil
// @Modifies p
// @Ensures True
func Take(p *Pile, xs []int) {
	p.items = xs
}
```

```text
vego: p.items may come to refer to memory that existed when Take was called and that it did not own; an owned field may refer only to memory made since, or to part of what it referred to then; copy it into new memory, as slices.Clone does, or do not declare the field owned
```

`p.items = slices.Clone(xs)` verifies. So do `append` to the field itself, a slice of it, `make`, a composite literal, and a variable that holds new memory nothing else refers to, as in `m := make(map[string]int); fill(m); c.m = m`.

### Keeping what a struct owns in one place

What a struct owns may be read and written through local variables, and handed to a function that keeps nothing of it, such as `sort.Ints(p.items)`. It may not be kept anywhere else:

```go
// Shelf holds a slice it does not own.
type Shelf struct {
	kept []int
}

// @Requires p != nil And s != nil
// @Modifies s
// @Ensures True
func Lend(p *Pile, s *Shelf) {
	s.kept = p.items
}
```

```text
vego: p.items is memory that p owns, stored into memory at owns.go:66:2; it may be read and written here, but not kept elsewhere: copy it, or do not declare the field owned
```

The same applies to a function literal that may run after the call and captures it, and to a callee that may keep what it is handed. A verified function keeps a parameter when it stores it, or memory it refers to, into memory. A trusted function keeps only what its entry lists under `keeps`.

A method may return what its struct owns when its contract says so with `within`:

```go
// @Requires p != nil
// @Ensures within(r, p) And |r| = |p.items|
func (p *Pile) Items() (r []int) {
	return p.items
}
```

Without the `within` clause, the return is reported as `Items returns memory that p owns; say so with within(r, p) in an Ensures, or return a copy`.

### What a function may assume of what it is handed

A function that lists an owner in `Modifies` may assume that nothing else it is handed refers to what the owner owns. `Append` reads `xs` after each `append` to `p.items`, and the values it read stay as they were:

```go
// @Requires p != nil And |p.items| + |xs| < 1000000
// @Modifies p
// @Ensures |p.items'| = |p.items| + |xs|
func (p *Pile) Append(xs []int) {
	// @Invariant 0 <= i <= |xs| And |p.items| = |old(p.items)| + i
	for i := range xs {
		p.items = append(p.items, xs[i])
	}
}
```

Every call of a verified function proves it. Handing an owner what it owns is refused:

```go
// @Requires p != nil And |p.items| < 1000
// @Modifies p
// @Ensures True
func AppendOwn(p *Pile) {
	p.Append(p.items)
}
```

```text
vego: p.items is memory that p owns, and Append is handed what reaches a Pile, which can own it; Append assumes that nothing it is handed is what an owner it is handed owns: copy it, or pass it alone
```

### A struct that owns its writer

A struct that owns an interface value keeps its other fields across a call through that value:

```go
// @Owns out
type Journal struct {
	out   io.Writer
	lines int
}

// @Ensures r != nil And r.lines = 0
func NewJournal() (r *Journal) {
	return &Journal{out: os.Stderr}
}

// @Requires l != nil And l.out != nil And l.lines < 1000000
// @Modifies l
// @Ensures err = nil -> l.lines' = l.lines + 1
func (l *Journal) Line(p []byte) (err error) {
	_, err = l.out.Write(p)
	if err == nil {
		l.lines++
	}
	return err
}
```

`l.lines` is known after `l.out.Write(p)`. A caller of `Line` keeps what its other arguments refer to, too.

A struct can own only a writer made for it, as `os.Stderr` converted where it is stored, or a value made in the function. A writer it is handed is memory that existed when the function was called, and storing it is refused.

### Converting an owner to an interface

A pointer to an owner can be converted to an interface whose methods write behind their receiver. What a method may write is the struct and everything it owns:

```go
// @Owns m
type Registry struct {
	m map[string]int
}

// @Requires x != nil
// @Modifies x
// @Ensures True
func (x *Registry) Put(k string, v int) {
	if x.m == nil {
		x.m = make(map[string]int)
	}
	x.m[k] = v
}

// @Ensures True
func PutTwice() {
	x := &Registry{}
	var p Putter = x
	p.Put("a", 1)
	p.Put("b", 2)
}
```

Here `Putter` is an interface whose `Put` lists its receiver. The memory a converted value may write grows with what the owner owns. A map stored into `x.m` after the conversion is written by `p.Put`, so nothing is known of it after the call:

```go
// @Ensures r
func StaleRegistry() (r bool) {
	x := &Registry{m: map[string]int{}}
	var p Putter = x
	x.m = make(map[string]int)
	m := x.m
	m["a"] = 1
	p.Put("a", 2)
	return m["a"] == 1
}
```

```text
vego: postcondition may not hold: r
```

### The invariant of what a struct owns

The invariant of a struct includes the invariants of the structs that its owned pointer fields point to. A function of another package can then call a method that needs them, as in [It applies only to direct parameters and results](#it-applies-only-to-direct-parameters-and-results). To say in a formula that the invariants of a value hold, write `valid(x)`: it is what a function assumes of `x` on entry, and it names no field of `x`. A loop that calls a method of a store that a server owns can keep the store's invariant with `// @Invariant valid(s)`.

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

Keys must be integers, strings, or booleans. Writing to a map requires a proof that the map is not nil. Reading from a map and calling `delete` do not.

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

### Saying something of every key

`Forall k in m : P` says that `P` holds of every key that `m` has. `Exists k in m : P` says that `P` holds of some key it has. The variable `k` has the type of the keys, so it can be a string:

```go
// @Requires Forall k in m : 0 <= m[k] <= 100
// @Ensures 0 <= total <= 100 * |m|
func SumScores(m map[string]int) (total int) {
	// @Visited done
	// @Invariant 0 <= total <= 100 * |done|
	for _, n := range m {
		total += n
	}
	return total
}
```

A key that `m` does not have is outside the quantifier, so `Forall k in m : m[k] = 1` says nothing of `m[0]` when `m` lacks the key 0. `m` can be primed, put in `old`, or reached through fields, as in `Forall k in s.index'`.

The body can compare a string key with another string, as in `k = node`. That comparison tells `vego` which key it is: a write to the key `node` is a write to the key `k` exactly when `k = node`. A comparison made through a predicate, `has`, `|...|`, or an index does not tell `vego` which key it is, and neither does a comparison of two keys bound by nested quantifiers. A formula that depends on such a comparison may not be proved.

`Z` in a quantifier always means the integers. A variable, parameter, snapshot, or quantifier variable named `Z` makes `Forall k in Z` an error, so rename it.

### How many keys a map can have

`vego` knows two bounds on `|m|`:

- A map has no more keys than its key type has values: at most 2 for `bool` and 256 for `uint8`.
- Every key and value takes memory of its own, so `|m|` times the size of a key and a value is at most `MaxAlloc`.

The second bound lets a function make a slice with `len(m)` elements of the key type or the value type without a `Requires`. It does not bound a slice that grows by `append` one key at a time, because an `append` that moves needs twice the length. Such a loop needs a `Requires` on `|m|`, or a slice made with room for every key, as in `make([]T, 0, len(m))`.

Outside a range over the map, `vego` does not tie the number of keys to the keys it knows of. This true contract is not proved:

```go
// @Requires has(m, "a") And has(m, "b")
// @Ensures |m| >= 2
func TwoKeys(m map[string]int) {}
```

```text
vego: postcondition may not hold: |m| >= 2
```

### Loops over a map

Go visits each key a map has when the loop starts exactly once, in an order that it does not fix. To count the iterations, name the keys the loop has visited with a `Visited` annotation above the loop:

```go
// @Ensures |result| = |m|
func KeysOf(m map[string]int) (result []string) {
	result = make([]string, len(m))
	i := 0
	// @Visited done
	// @Invariant i = |done|
	for k := range m {
		result[i] = k
		i++
	}
	return result
}
```

In the annotations of the loop and in its body, `|done|` is the number of places in the order that the loop has passed before the current iteration. That is the number of iterations, unless the loop deletes keys it has not reached (see [Changing the map a loop ranges over](#changing-the-map-a-loop-ranges-over)). `has(done, k)` says that the loop passed the key `k` before the current iteration. `Forall k in done : P` says something of every key the loop has passed. A formula reads `done` only in these three ways. It cannot be primed, put in `old`, indexed, or compared as a whole.

When the loop ends, `done` is every key the map had when the loop started. So an invariant `Forall k in done : P` gives `P` of each of those keys after the loop. `done` itself cannot be named after the loop.

Without the annotation, nothing ties `i` to the number of iterations, and the write to `result[i]` is not proved to be in range:

```go
// @Ensures True
func KeysOfUncounted(m map[string]int) (result []string) {
	result = make([]string, len(m))
	i := 0
	// @Invariant 0 <= i
	for k := range m {
		result[i] = k
		i++
	}
	return result
}
```

```text
vego: index may be out of range
```

The keys of different iterations differ. So a loop can copy a map and say how many keys the copy has:

```go
// @Ensures |c| = |m| And (Forall k in m : has(c, k) And c[k] = m[k])
func Widen(m map[string]int32) (c map[string]int64) {
	c = make(map[string]int64)
	// @Visited done
	// @Invariant |c| = |done| And (Forall k in done : has(c, k) And c[k] = m[k])
	// @Invariant Forall k in c : has(done, k)
	for k, v := range m {
		c[k] = int64(v)
	}
	return c
}
```

Two loops over one map need not visit it in the same order, and `vego` does not assume that they do.

A `Visited` annotation must stand directly above a `range` over a map, with at most one on a loop, and an annotation of the loop must name it. Its name must name nothing else where it stands.

### Changing the map a loop ranges over

A `range` loop over a map can change the map it ranges over when the change has one meaning in Go. The loop can write a key that the map has, and a later iteration reads the value written. It can delete the key of the current iteration:

```go
// @Requires m != nil
// @Modifies m
// @Ensures Forall k in m' : m'[k] >= 0
func DropNegative(m map[string]int) {
	// @Visited done
	// @Invariant Forall k in m : has(old(m), k) And m[k] = old(m[k])
	// @Invariant Forall k in done : has(m, k) -> m[k] >= 0
	for k, v := range m {
		if v < 0 {
			delete(m, k)
		}
	}
}
```

It can also delete a key that the loop has not reached yet. Go then does not visit that key. The loop passes its place in the order without running the body, and `done` counts that place too. An invariant must hold when a place is passed this way, so `n = |done|` is not preserved here:

```go
// @Requires m != nil And has(m, "a") And has(m, "b")
// @Modifies m
// @Ensures n = |m|
func CountDeleting(m map[string]int) (n int) {
	// @Visited done
	// @Invariant n = |done|
	for k := range m {
		if k == "a" {
			delete(m, "b")
		}
		n++
	}
	return n
}
```

```text
vego: loop invariant may not be preserved: n = |done|
```

`n <= |done|` holds, and with it `n <= |m|`. A loop whose only deletes of maps of the type delete the key of the current iteration, through the loop's own key variable, needs no such care: every key it reaches is still there.

The loop cannot add a key, because Go may or may not visit a key added while the loop runs:

```go
// @Requires m != nil And (Forall k in m : 0 <= k < 100)
// @Modifies m
func Shift(m map[int]int) {
	for k := range m {
		m[k+100] = m[k]
	}
}
```

```text
vego: this may add a key to m, the map that the loop at guide.go:1026:2 ranges over, and Go may
or may not visit a key added during the loop; collect the new entries in another map and add
them after the loop
```

Writing a key that the map lacks, after deleting it, is adding it. A call that may change the map the loop ranges over is reported too, since it may add a key:

```go
// @Requires m != nil
// @Modifies m
func MergeEach(m, src map[string]int) {
	for range m {
		maps.Copy(m, src)
	}
}
```

```text
vego: Copy may modify m while the loop at maps.go:169:2 ranges over it, and may add a key, which
Go may or may not visit during the loop; change the map in the loop's body, or after the loop
```

A map of the same type that is not the ranged one can be changed freely. `vego` must prove that it is another map, for example from `Requires dst != src`, or because the function made it.

### Writing one entry

`Modifies m[k]` lists one entry of a map: whether `m` has the key `k`, its value, and the number of keys. A caller keeps everything it knew of the other keys, and knows the new number of keys:

```go
// @Requires counts != nil And counts[page] < 1000000
// @Modifies counts[page]
// @Ensures has(counts', page) And counts'[page] = counts[page] + 1
func Hit(counts map[string]int, page string) {
	counts[page]++
}

// @Requires counts != nil And counts["a"] < 1000 And counts["home"] = 7
// @Modifies counts
// @Ensures counts'["a"] = counts["a"] + 2 And counts'["home"] = 7
func HitTwice(counts map[string]int) {
	Hit(counts, "a")
	Hit(counts, "a")
}
```

For a map held in another map, `Modifies g[from][to]` lists the entry `to` of the map `g[from]`. A path that goes past the key into a field of the value, as in `m[k].qty`, is an error: list the whole entry.

When the values of a map are pointers, slices, maps, or interface values, `m[k]` in a `Modifies` clause names what the value refers to, as `p.next` does for a pointer field. The entry itself is covered only by `Modifies m`:

```go
// @Requires tags != nil And |tags[k]| < 1000
// @Modifies tags[k]
// @Ensures True
func AddTag(tags map[string][]string, k, tag string) {
	tags[k] = append(tags[k], tag)
}
```

```text
vego: tags[k] is assigned, which AddTag may not modify; list the whole map in a // @Modifies
clause: an entry of a map whose values are pointers, slices, maps, or interface values is covered
only by the map, since a path such as m[k] in a Modifies clause names what the value refers to
```

A contract with `Modifies m` says what it keeps with a quantifier:

```go
// @Requires g != nil
// @Modifies g
// @Ensures set != nil And has(g', k) And g'[k] = set
// @Ensures Forall j in g : has(g', j) And (j = k Or g'[j] = g[j])
func Group(g map[string]map[string]bool, k string) (set map[string]bool) {
	set = g[k]
	if set == nil {
		set = make(map[string]bool)
		g[k] = set
	}
	return set
}
```

A loop that calls a function with `Modifies m[k]` forgets the whole map, as for any write to a map in a loop. State in an invariant what the loop keeps.

## Package-level variables

A function can read a package-level variable that nothing changes after it is initialised. A contract can name it as the code does:

```go
var digits = "0123456789abcdef"

var limits = map[string]int{"free": 10, "pro": 1000}

// Hex returns the digit for d.
//
// @Requires 0 <= d < 16
// @Ensures r = digits[d]
func Hex(d int) (r byte) {
	return digits[d]
}

// Limit returns the limit of a plan.
//
// @Ensures ok <-> (plan = "free" Or plan = "pro")
// @Ensures plan = "pro" -> n = 1000
func Limit(plan string) (n int, ok bool) {
	n, ok = limits[plan]
	return n, ok
}
```

Both functions verify. `vego` knows the string that `digits` holds and the keys and values of `limits`. It knows these values from the initialisers, and nothing in the program can change them. A variable of an imported package is named as in Go, as in `lib.Limit`.

Error variables follow rules of their own, described in [Errors](#errors).

### Which variables a function can read

`vego` reads every file of your package and of every package it is built with. That includes code that is not verified and the standard library. A function can read a variable when none of that code changes it in one of these ways:

- assigns it, or a field of it, as in `x = 1`, `x.n = 1`, `x++`, or `for x = range s`;
- takes its address, as in `&x` or `&x.n`, or selects a method with a pointer receiver on it, as in `x.Reset()` or the method value `x.Reset`;
- names it in a `//go:linkname` directive, or refers to it in an assembly file.

Reading a variable that is changed is reported:

```go
var served int

// Serve counts requests, and is not verified.
func Serve() {
	served++
}

// Served reads the count.
//
// @Ensures True
func Served() (r int) {
	return served
}
```

```text
vego: cannot verify Served: served is assigned at globals.go:35; package-level variables that are changed
are not supported yet
```

Pass the value as a parameter instead. For a variable of another package, the message names the package that changes it. An `init` function that assigns a variable changes it too.

The type of the variable must be one that cannot hold code. A function value, an interface value, an error, a channel, or an `unsafe.Pointer` may not appear in the type at any depth, also behind a pointer, and also in a field that the type does not export. Verified code cannot read such a field, but it can hand the variable to a trusted function that runs the code the field holds. So `*http.Client` cannot be read, and neither can `*log.Logger`:

```go
// Client reads a variable whose type can hold code.
//
// @Ensures True
func Client() (r bool) {
	return http.DefaultClient != nil
}
```

```text
vego: cannot verify Client: http.DefaultClient has type *net/http.Client, which can hold a function value,
an interface value, an error, a channel, or an unsafe.Pointer; package-level variables of such types are not
supported yet
```

Two types of the standard library are counted by what their package lets them hold, as described in [Arguments that carry code](#arguments-that-carry-code). So `*os.File` holds no code, and `os.Stdin`, `os.Stdout`, and `os.Stderr` can be read where nothing in the build assigns them.

### What vego knows of the value

`vego` reads the initialiser of the variable. The value is known in these cases:

- There is no initialiser and no `//go:embed` directive. The variable holds the zero value of its type, unless the build sets it with `-ldflags -X`, as described at the end of this section.
- The initialiser is a constant, as in `var defaultTimeout = 30`. The variable holds that constant. A float constant is one value, but nothing is known of it, as for every float.
- The initialiser is a struct literal, as in `var defaults = Config{Timeout: 30}`. Each field holds what the literal gives it, by these same rules.
- The initialiser is a slice or map literal, `make`, `new`, `&T{...}`, or `[]byte` or `[]rune` of a constant string. The variable is not nil. A slice has the length that the literal, the constant arguments of `make`, or the string gives, and the capacity of a literal or of `make` with constant arguments.
- The initialiser is another package-level variable that a function can read. The variable holds the same value.

Anything else gives a value of the type of which nothing more is known. That includes a call, as in `var pageSize = os.Getpagesize()`, arithmetic on other variables, and a variable that a `//go:embed` directive fills.

`vego` does not know that such a value is what your code expects. A `Requires` clause cannot state it either, since no caller chooses the value of a package-level variable, and a caller in another package may not be able to name it. So a clause that reads package-level variables and nothing else must follow from what their declarations give:

```go
var pageSize = os.Getpagesize()

// Pages counts the pages that n bytes take.
//
// @Requires pageSize > 0
// @Requires n >= 0
// @Ensures True
func Pages(n int) (r int) {
	return n / pageSize
}
```

```text
vego: the Requires clause pageSize > 0 reads only package-level variables, and their declarations do not
show that it holds; test the value in the body instead
```

Test the value in the body:

```go
// PagesChecked tests the value in the body.
//
// @Requires n >= 0
// @Ensures True
func PagesChecked(n int) (r int) {
	if pageSize <= 0 {
		return 0
	}
	return n / pageSize
}
```

A clause that relates a parameter to a variable, such as `@Requires n < defaultTimeout`, is a condition on callers as usual. The check that a contract does not allow a function to always fail, described in [Saying when a function succeeds](#saying-when-a-function-succeeds), counts a variable as part of the input. Its declaration narrows the values that the check tries.

In an `Ensures` clause, a prime on a variable that reads no memory is reported, as in `defaultTimeout'`, since the variable holds the same value on return. A primed path that reads memory, as in `sizes'[0]`, is the memory on return, as for a parameter. `old(defaultTimeout)` is reported. A struct invariant, and the contract of a function type or of a method of an interface, cannot name a package-level variable yet.

### What a variable refers to

A variable that holds a slice, a map, or a pointer is fixed, but the memory it refers to may not be. `table[0] = 5` assigns no variable. `vego` treats that memory as unchanged only when both of these hold:

- The initialiser made the memory: it is a slice or map literal, `make`, `new`, `&T{...}`, or `[]byte` or `[]rune` of a constant string. No other reference to it existed then.
- Every use of the variable in the build only reads a value out of it.

These uses are reads:

- `v[i]`, `v.f`, or a path of these such as `v[i].f`, that ends in a value with no pointer, slice, or map in it;
- `n, ok := v[k]`, on the same condition;
- `len(v)` and `cap(v)`;
- a comparison with `nil`;
- a `range` over `v` whose elements, and for a map whose keys, hold no pointer, slice, or map.

Any other use lets a reference to the memory out of the variable. Examples are passing `v` to a function, assigning it, slicing it, calling a method on it or on one of its elements, writing an element, and `delete` on a map. A use in code that is not verified counts. So does a use in another package that is built with yours, and a use in the initialiser of another variable, as in `var view = table[1:]`.

When both conditions hold, a literal tells `vego` the elements, the keys and values, or the fields. `Limit` above relies on this. In these cases the memory is unchanged, but what it holds is not known:

- The literal has more than 1024 elements or keys. The length of a slice is still known.
- A key of a map literal is not a constant.
- `make` or `new` made the memory.

What is made inside a literal, such as the inner slices of `[][]int{{1, 2}}`, is ordinary memory.

Otherwise the memory is like memory that a parameter refers to. Nothing is known of what it holds when the function is called, and a write through another slice may change it:

```go
var sizes = []int{1, 2, 4}

// Grow writes the table, and is not verified.
func Grow() {
	sizes[0] = 8
}

// FirstSize reads the table.
//
// @Ensures r = 1
func FirstSize() (r int) {
	return sizes[0]
}
```

```text
vego: postcondition may not hold: r = 1; the contents of sizes are not known to stay as
initialised: the use at globals.go:49 lets a reference to them out
```

The message names the first use that lets a reference to what the variable refers to out, here the write in `Grow`. Every message about something not proved after a function reads such a variable carries this note, also one about an index or an overflow. The length of `sizes` is still known, so `sizes[i]` needs no `Requires` for an `i` below 3.

A package that is built with yours may let out a reference to a variable that a proof relies on. The use is then reported where it is, and in every package `laas` analyses that is built with both:

```text
vego: globalslib.Plans may be changed here, but proofs in package globalslib rely on what it refers to
being only read
```

```text
vego: globalslib.Plans is changed at mid.go:12 in package globalsmid, which this package is built with,
but proofs in package globalslib rely on what it refers to being only read
```

An assignment in such a package to a variable that a proof relies on is reported in the same way, with `rely on it holding the value it was declared with`.

### Changing a variable

A verified function cannot change a package-level variable, or the memory one refers to, yet:

```go
// ResetServed assigns a variable.
//
// @Ensures True
func ResetServed() {
	served = 0
}

// SetSize writes what a variable refers to.
//
// @Ensures True
func SetSize() {
	sizes[1] = 3
}

// ListsSizes names a variable in Modifies.
//
// @Modifies sizes
func ListsSizes() {}
```

```text
vego: cannot verify ResetServed: served is a package-level variable, which a verified function cannot
assign yet
vego: cannot verify SetSize: sizes[1] writes memory that the package-level variable sizes refers to,
which a Modifies clause cannot name yet
vego: in Modifies annotation: sizes is a package-level variable, which a Modifies clause cannot name yet
```

A call that would write such memory, or an `append` that would write into its capacity, is reported with the same reason: `it is memory that the package-level variable sizes refers to, which a Modifies clause cannot name yet`.

### Variables and initialisation

A variable holds its value only once the package has initialised it. `vego` relies on Go's order of initialisation, under the same conditions as for an error variable. Code that Go's ordering does not see can run during initialisation, as described in [When a package-level error is known](#when-a-package-level-error-is-known). Then a variable with an initialiser cannot be read, and the message has the form shown there: `x is not known to have its value yet when this runs: ...`. A variable without an initialiser is zero before any code runs, so it can still be read.

### What this does not cover yet

Some code that uses package-level variables still cannot be verified:

- A counter, a cache, or any other variable that is assigned, also in an `init` function, as `os.Args` is in package `os`. Pass the value as a parameter.
- A logger in a package-level variable, as in `var logger = log.New(os.Stderr, "app: ", 0)`. The logger keeps the writer that its initialiser gave it, and nothing checked that writer. `vego` does not know either that `log.New` returned a logger that is not nil:

  ```go
  var logger = log.New(os.Stderr, "app: ", 0)

  // Notify writes to a package-level logger.
  //
  // @Requires |msg| <= 1000
  // @Ensures True
  func Notify(msg string) {
  	if logger != nil {
  		logger.Printf("report: %s", msg)
  	}
  }
  ```

  ```text
  vego: cannot verify Notify: logger has type *log.Logger, which can hold a function value, an interface
  value, an error, a channel, or an unsafe.Pointer; package-level variables of such types are not
  supported yet
  ```

  Take the logger as a parameter.
- `log.Default()`, which has no shipped contract.
- `flag` variables. `flag.Int` returns an `*int`, and pointers to anything but a struct are not supported. `flag.StringVar(&s, ...)` takes the address of `s`.
- A variable of a function type or an interface type.

A build that sets a string variable with `-ldflags "-X path.name=value"` gives it a value that `vego` does not see. A proof that relies on the value of such a variable, typically a version, does not hold for that build. See [What a proof assumes](#what-a-proof-assumes).

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

The check is made once the function's other checks pass. A function that has a report of its own, such as an index that may be out of range, gets no report from this check, so this message can appear after you fix something else. The search it needs is the costliest question `vego` asks, and the contract of a function with a fault is likely to change anyway.

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
in a verified function, or one that a contract vouches for, can be its first
argument
```

An error that a trusted function returns has no known origin unless the contract of the function vouches for it. See [Errors that a trusted function returns](#errors-that-a-trusted-function-returns). Without that, `errors.Is(err, io.EOF)` on it is reported. You can compare it with `==` instead, as in `err == io.EOF`, which runs no method. That comparison is true only when the function returned `io.EOF` itself, and not when it returned an error that wraps `io.EOF`.

The shipped contracts of `strconv.Atoi`, `strconv.ParseInt`, and the functions of `os` that return an error vouch for their errors, among others listed in [Shipped contracts](#shipped-contracts). The contract of `strconv.Atoi` also says that a failure is a syntax error or a range error, and which number comes with each:

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
// @Requires |name| <= 4096
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

`fmt.Errorf` can format what every function that formats can: numbers, booleans, strings, and slices and structs of them without the methods that `fmt` calls, and errors of known origin. [What can be formatted](#what-can-be-formatted) gives the exact rule. An error has a known origin in two cases:

- It was made by `errors.New` or `fmt.Errorf`, in verified code or in the initialiser of an error variable of any package, and nothing went into it but such values and other errors of known origin. `io.EOF` is one.
- A trusted contract vouches for it, as described in [Errors that a trusted function returns](#errors-that-a-trusted-function-returns). A verified function that returns such an error passes the known origin on to its callers.

It cannot format an error that came from a parameter, or from a trusted function whose contract does not vouch for it. Formatting an error calls its methods, and `vego` cannot see what the methods of an unknown error do. For the same reason, such an error cannot be passed to a trusted function unless that function's contract allows it. See [Arguments that carry code](#arguments-that-carry-code).

An error variable has a known origin where it is formatted when every assignment that can reach that place gives it one. An assignment after the `%w` does not reach it, so you can reuse `err` for the next call after you wrap it. In a loop, an assignment at the end of one iteration reaches a `%w` at the start of the next. See [Reading and writing files](#reading-and-writing-files) for an example.

The shipped contract of `strconv.Atoi` vouches for its error, so its error can be wrapped:

```go
var ErrTooMany = errors.New("too many")

// @Requires |line| <= 1000
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

The second clause is proved because `%w` keeps what `errors.Is` finds in `err`, and the contract of `strconv.Atoi` says that its error is a syntax error or a range error. The `Requires` bounds the length of `line`, which `fmt.Errorf` quotes, as described in [How long a formatted string can be](#how-long-a-formatted-string-can-be).

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
verified function, or one that a contract vouches for, can be formatted
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

An error variable of your own package holds the error it was declared with under these conditions. Nothing in the package changes it, in any of the ways listed in [Which variables a function can read](#which-variables-a-function-can-read). And no code in the package can run before the variable is initialised.

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

## Formatting and logging

Verified code can format values and write them out with `fmt` and `log`:

```go
// @Requires |host| <= 1000
// @Ensures True
func Announce(host string, port int, done, total int) (addr string) {
	addr = fmt.Sprintf("%s:%d", host, port)
	log.Printf("processed %d of %d", done, total)
	_, _ = fmt.Println("listening on", addr)
	return addr
}
```

The shipped contracts of `fmt.Sprintf`, `fmt.Sprint`, `fmt.Sprintln`, `fmt.Printf`, `fmt.Print`, `fmt.Println`, `fmt.Fprintf`, `fmt.Fprint`, `fmt.Fprintln`, `log.Printf`, `log.Print`, `log.Println`, and of the methods `Printf`, `Print`, and `Println` of `*log.Logger` promise little. `fmt.Fprintf`, `fmt.Fprint`, and `fmt.Fprintln` write the footprint of their writer, and the methods of `*log.Logger` write the logger, so a function lists the writer or the logger it prints through (see [Writing to a writer or a logger](#writing-to-a-writer-or-a-logger)). The others write nothing your code can see. `vego` knows nothing of the string that `Sprintf` returns, or of the count and the error that `Println` returns. A function that returns that error can leave its success open, as described in [Functions that cannot promise success](#functions-that-cannot-promise-success).

### What can be formatted

`fmt` calls the `Format`, `GoString`, `Error`, and `String` methods of what it formats. Code that `vego` has not checked could run that way, so `vego` checks every value at each call. These values can be formatted:

- numbers, booleans, and strings, of named types too;
- slices and structs whose elements and fields can be formatted, when their types have none of these four methods;
- a pointer to such a struct, which `fmt` prints as `&` and the fields, or as `<nil>`;
- `nil`;
- errors of known origin, described in [Wrapping errors](#wrapping-errors);
- a value whose `String` or `Error` method has a contract that modifies nothing, described in [Values with a String or Error method](#values-with-a-string-or-error-method).

Methods of a pointer to a type do not count for a value of the type, because `fmt` does not call them on a value. A type that holds itself, such as `type Tree []Tree`, cannot be formatted, since such a slice can hold itself and `fmt` would then not stop. Maps, interface values, function values, and pointers to anything but a struct cannot be formatted, and neither can a value of a type with a `Format` or `GoString` method.

Anything else is reported as `cannot verify`:

```go
// @Ensures True
func Display(v any) {
	_, _ = fmt.Println(v)
}
```

```text
vego: cannot verify Display: Println formats v, a value of type any, and that may run code
nobody has checked: any is an interface, which can hold a value with methods that fmt
would call; only numbers, booleans, strings, and slices and structs of them, pointers to
such structs, errors of known origin, and values whose String or Error method has a
contract that modifies nothing can be formatted
```

A slice passed with `...`, as in `fmt.Println(values...)`, is refused too, because what its elements hold is not known. List the values in the call instead.

### Values with a String or Error method

`fmt` calls the `Error` method of a value that is an error, and the `String` method of one that has `String() string`. Such a value can be formatted when the method has a contract, verified or trusted, that lists nothing under `Modifies`:

```go
type Temperature int

// @Requires t >= -273
// @Ensures True
func (t Temperature) String() (s string) {
	if t < 0 {
		return "below zero"
	}
	return "zero or above"
}

// @Requires t >= -273
// @Ensures True
func ShowTemperature(t Temperature) {
	log.Println("temperature", t)
}
```

At each call, `vego` proves the `Requires` of the method for the value as it is passed, in the state of the call. For a deferred call, that is the state at the return where the call runs. Without the `Requires` of `ShowTemperature`, the call is reported:

```text
vego: precondition of String may not hold where Println formats t: t >= -273
```

`fmt` may call the method any number of times. The call counts as a call of the method, so a `String` method that formats its own value, as `fmt.Sprint(t)` inside `String` would, is reported as recursion without a `Variant`.

These conditions apply:

- The method must modify nothing. `fmt` may call it any number of times, and the proof of the call assumes it changes nothing.
- What the type holds must be plain, because `fmt` prints it instead of calling the method for verbs such as `%d`. A struct with a field whose type has a `String` method cannot be formatted.
- A type with both `Error` and `String` is an error to `fmt`, so only `Error` is called and checked.
- A pointer can be formatted when `*T` has the method. A method with a pointer receiver is called with the pointer, also when it is `nil`, so its `Requires` decides. A method with a value receiver is called on what the pointer points to, so `vego` proves that the pointer is not `nil`.
- `fmt.Errorf` cannot format a value whose type is an error other than `error` itself, because `%w` would put it into the tree of the new error.
- A method of a type of another package needs a contract too, in the trust file if the package is not verified, as in `(time.Duration).String`.

What the method returns has no term in the logic. It counts as one of the parts whose length is assumed, as described in [How long a formatted string can be](#how-long-a-formatted-string-can-be).

### How long a formatted string can be

What `fmt` builds must fit in one allocation, as a joined string must. At each call of a function that formats, and of `fmt.Errorf`, `vego` proves this from the format and from the lengths of the strings and slices that are formatted:

```go
// @Ensures True
func Greet(name string) {
	log.Println("hello", name)
}
```

```text
vego: what Println builds from what it formats may be more than can be allocated; bound
what it formats, as in // @Requires |name| <= 70368744159185
```

The message names each length that nothing at the call bounds, and a bound for it that is enough on the platform `laas` runs for. The number above is for a 64-bit target. Any smaller bound, such as `// @Requires |name| <= 1000`, is enough too. A format that is not a constant needs a bound as well, and the message suggests `|format| <= 100`. A `Requires` clause speaks of the values on entry. When what is formatted is not a parameter, as for a string the function builds, or the function changed it before the call, the message gives the bound and says to check the length before the call. A deferred call is checked where it runs, at each return, with what a pointer it formats points to then.

The bound that `vego` proves is larger than what `fmt` writes, for these reasons:

- `vego` counts six bytes for each byte of a string under `%q`, `%x`, `%X`, and `%#v`. `fmt` writes at most four under `%q`, plus the quotes, and five under `% #x`.
- A width or a precision can be as large as ten million.
- Each verb may format any operand, and the buffer that `fmt` grows may be given twice the room it needs.

The string that `fmt.Sprintf`, `fmt.Sprint`, and `fmt.Sprintln` return is known to be no longer than the bound proved at the call, so you can format it again. That is not known when the call formats an error or a slice of strings, whose lengths `vego` does not know.

Some lengths have no term in the logic: the text of an error, the strings in a slice of strings or in a slice of structs, the name of a file in a logger's header, and the prefix of the standard logger. For these the proof assumes that they do not make what is built longer than can be allocated. See [What a proof assumes](#what-a-proof-assumes).

### Writing to a writer or a logger

`fmt.Fprintf`, `fmt.Fprint`, and `fmt.Fprintln` require a writer that is not `nil`. They call its `Write` method, which is described in [Interfaces and function types of other packages](#interfaces-and-function-types-of-other-packages). The methods of `*log.Logger` that print require a logger that is not `nil` and whose state `ready` holds. They call the `Write` method of the writer the logger holds, so a function that prints through `l` lists `l`, as it lists `w`:

```go
// @Requires w != nil And l != nil And ready(l)
// @Modifies w, l
// @Ensures True
func Inventory(w io.Writer, l *log.Logger, n int) (err error) {
	l.Printf("%d items", n)
	_, err = fmt.Fprintf(w, "%d items\n", n)
	return err
}
```

`ready(l)` holds when the output of the logger is a writer that is not `nil` and its prefix is at most 4096 bytes long. A logger made as a zero value, such as `&log.Logger{}`, has no output, and printing to it panics:

```go
// @Ensures True
func LogsToZero() {
	l := &log.Logger{}
	l.Printf("x")
}
```

```text
vego: precondition of Printf may not hold: ready(l)
```

`log.New` returns a logger whose state `ready` holds. It requires a writer that is not `nil` and a prefix of at most 4096 bytes. The logger keeps the writer, and its methods call the writer's `Write` later, as described in [Functions that keep what they are given](#functions-that-keep-what-they-are-given). What they write is what the writer writes, so a function that prints through a logger made over `w` lists `w`:

```go
// @Requires w != nil
// @Modifies w
// @Ensures True
func LogsTo(w io.Writer, n int) {
	l := log.New(w, "app: ", log.LstdFlags)
	l.Printf("%d items", n)
}
```

A logger that your function is handed by code that is not verified needs `ready(l)` in its `Requires`, as `Inventory` has.

`log.Default()` and a logger in a package-level variable are reported as `cannot verify`, as described in [What this does not cover yet](#what-this-does-not-cover-yet). Use `fmt.Printf` or `log.Printf`, or take the writer or the logger as a parameter.

`fmt.Printf`, `fmt.Print`, and `fmt.Println` write to standard output, and the functions of `log` write to the standard logger. Code that is not verified chooses where those go: it can set `os.Stdout`, and it can call `log.SetOutput` or `slog.SetDefault`. A proof assumes that a write there returns and writes nothing verified code can see. If your program sets the standard logger's output to a writer of its own, it makes that claim about the writer. A writer that logs through the standard logger again never returns, because the logger holds a lock while it writes. See [What a proof assumes](#what-a-proof-assumes).

### Formatting into a buffer

`fmt.Fprintf`, `fmt.Fprint`, and `fmt.Fprintln` can write to a `*bytes.Buffer`, a `*strings.Builder`, or a `*bufio.Writer`. `vego` checks such a call as `fmt.Sprintf` followed by the writer's own `Write` of the formatted bytes. So the requires of that `Write` must hold, and `Modifies` must list the writer:

```go
// @Requires b != nil And |b| <= 1000000 And 0 <= n And n <= 1000
// @Modifies b
// @Ensures True
func WriteItems(b *bytes.Buffer, n int) {
	fmt.Fprintf(b, "%d items\n", n)
}
```

The length of what is formatted comes from the bound described in [How long a formatted string can be](#how-long-a-formatted-string-can-be). The bound counts each operand at the widest it can print under its verb, so it is larger than what is printed. An invariant of a loop that formats must allow for the bound, not for the text you expect. `"%d,"` prints at most 21 bytes, and its bound is between 200 and 500:

```go
// @Requires b != nil And |b| <= 1000000 And 0 <= k And k <= 1000
// @Modifies b
// @Ensures True
func WriteNumbers(b *bytes.Buffer, k int) {
	// @Invariant 0 <= i And i <= k And |b| <= |old(b)| + 500 * i
	// @Variant k - i
	for i := 0; i < k; i++ {
		fmt.Fprintf(b, "%d,", i)
	}
}
```

The same loop with `|b| <= |old(b)| + 21 * i` is reported as `loop invariant may not be preserved`.

That bound does not count the text of an error, what a `String` or `Error` method returns, or the strings and slices inside an element of a slice. When it does not count everything, nothing bounds what `Write` is given. A buffer's `Write` needs such a bound, so the call is reported:

```go
// @Requires b != nil And |b| <= 1000000
// @Modifies b
// @Ensures True
func WriteFailure(b *bytes.Buffer) {
	fmt.Fprintf(b, "failed: %v\n", errors.New("disk full"))
}
```

```text
vego: Fprintf writes to b text whose length is not known: it formats the text of an error, what a String or Error
method returns, or strings or slices inside an element of a slice, whose lengths are not counted, and the Write of
*bytes.Buffer needs a bound on what it is given; format only values whose length the bound counts
```

The `Write` of a `*bufio.Writer` needs no such bound, so the same call into one verifies:

```go
// @Requires bw != nil And ready(bw)
// @Modifies bw
// @Ensures True
func WriteFailureBuffered(bw *bufio.Writer) (err error) {
	_, err = fmt.Fprintf(bw, "failed: %v\n", errors.New("disk full"))
	return err
}
```

A deferred call is checked the same way when it runs. The results of the call are those of the writer's `Write`.

A value converted to an `io.Writer` first, as in `var w io.Writer = &b`, is refused, as described in [Converting a value of your own type](#converting-a-value-of-your-own-type).

### Your own logging function

A logging function of your own that hands its values to `fmt` or `log` cannot be verified, because it formats values that it cannot check, the elements of `args`:

```go
func Logf(format string, args ...any) {
	log.Printf("app: "+format, args...)
}
```

Give it a trusted contract with `formats` instead. `vego` then checks each value at each call of `Logf`, as for `log.Printf`:

```yaml
  example.com/app/internal/logging.Logf:
    reason: Formats with log.Printf; reviewed 2026-11-19.
    formats: [format, args]
    modifies: []
```

`formats` lists the parameter of type `any` or `...any` whose values the function formats, and the string it uses as the format, if it has one. By listing them, you claim all of this about the function:

- It does nothing with those values but format them as package `fmt` does, and it uses that string only as the format.
- It runs no method of the values other than those `fmt` runs, and only while the call lasts, on the goroutine that called it.
- It keeps none of the values.
- It writes nothing your code can see beyond what its `modifies` lists.
- It formats every value before it writes anything that its `modifies` lists, and before it runs any code that its `runs` lists. `fmt.Fprintf` formats into a buffer and then calls `w.Write` once.
- What it builds from them is at most 4096 bytes longer than what `fmt` prints for them, apart from what a logger adds from its own settings, such as its prefix and the name of a file.

`vego` checks the values in the state of the call, which is the state in which they are formatted because the function formats first. An entry with `formats` cannot have `calls`, because a function it is handed could run before the values are formatted. Such an entry cannot be used.

### Functions that do not return

`log.Fatal`, `log.Fatalf`, `log.Fatalln`, `log.Panic`, `log.Panicf`, and `log.Panicln` have no shipped contracts. A trusted contract claims that its function returns, and these do not. A call of one is reported as `cannot verify`, with the message that it has no contract.

## Defer

`vego` verifies a deferred call at the point where it runs. That is at every `return` of the function, after the results have been set. Deferred calls run in reverse order.

```go
type Lock struct{ taken bool }

// @Requires l != nil And ~l.taken
// @Modifies l
// @Ensures l.taken'
func (l *Lock) Acquire() {
	l.taken = true
}

// @Requires l != nil And l.taken
// @Modifies l
// @Ensures ~l.taken'
func (l *Lock) Release() {
	l.taken = false
}

// @Requires l != nil And ~l.taken And c != nil And c.n < c.limit
// @Modifies l, c.n
// @Ensures ~l.taken'
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
// @Requires l != nil And ~l.taken And 0 <= n <= 10
// @Modifies l
// @Ensures ~l.taken'
func Rounds(l *Lock, n int) {
	// @Invariant ~l.taken
	for range n {
		func() {
			l.Acquire()
			defer l.Release()
		}()
	}
}
```

A call through a function value of a type with a contract can be deferred too, and so can a call of a method with a contract through an interface value. See [Function values](#function-values) and [Interfaces](#interfaces). `defer cancel()` verifies for a `context.CancelFunc` that the function is given, whose shipped entry is described in [Interfaces and function types of other packages](#interfaces-and-function-types-of-other-packages). It does not verify after `context.WithCancel`, which has no entry. `defer resp.Body.Close()` verifies for a body that is not closed, as described in [States of interface values](#states-of-interface-values).

`recover` is not supported, because it returns an interface. Call it in a function that is not verified.

### Locks

`vego` ships contracts for the methods of `sync.Mutex` and `sync.RWMutex` that lock and unlock, and for `(*sync.Once).Do`. Their formulas speak of whether the goroutine that runs the function holds the mutex. A formula writes that as `held(m)`, where `m` is a mutex or a pointer to one:

```go
// Deposit adds n to the balance if the result stays within the limit.
//
// @Requires a != nil And ~held(a.mu) And 0 <= n
// @Modifies a.mu, a.balance
// @Ensures ~held(a.mu')
func (a *Account) Deposit(n int) (ok bool) {
	a.mu.Lock()
	defer a.mu.Unlock()
	if n > 1000000-a.balance {
		return false
	}
	a.deposit(n)
	return true
}

// deposit runs while the caller holds the lock.
//
// @Requires a != nil And held(a.mu) And 0 <= n And a.balance + n <= 1000000
// @Modifies a.balance
// @Ensures a.balance' = a.balance + n
func (a *Account) deposit(n int) {
	a.balance += n
}
```

This proof covers one goroutine. It does not show that other goroutines take the lock before they touch `a.balance`. See [What a proof of a function that locks shows](#what-a-proof-of-a-function-that-locks-shows).

`held(a.mu)` is true when the goroutine that runs the function has locked `a.mu` and has not unlocked it since. It says nothing about other goroutines. It is false for a mutex that was just created, such as the one in `&Account{}`.

`Deposit` lists `a.mu` in `Modifies`, because `Lock` and `Unlock` write the mutex. It requires `~held(a.mu)`, because `Lock` on a mutex that the goroutine already holds waits for ever. `vego` reports a `Lock` that may do that, and an `Unlock` of a mutex that the goroutine may not hold, which is a run-time error:

```go
// DepositLocked takes the lock without saying that the caller does not
// hold it.
//
// @Requires a != nil And 0 <= n And a.balance + n <= 1000000
// @Modifies a
func (a *Account) DepositLocked(n int) {
	a.mu.Lock()
	a.balance += n
	a.mu.Unlock()
}
```

```text
vego: precondition of Lock may not hold: ~held(m)
```

The message shows the clause as the contract of `Lock` writes it. `m` is the receiver of `Lock`, here `&a.mu`. An `Unlock` gives `precondition of Unlock may not hold: held(m)`.

The contracts are these:

| Method | Requires | Ensures |
| --- | --- | --- |
| `(*sync.Mutex).Lock` | `~held(m)` | `held(m')` |
| `(*sync.Mutex).Unlock` | `held(m)` | `~held(m')` |
| `(*sync.Mutex).TryLock` | | `result -> ~held(m) And held(m')`, `~result -> (held(m') <-> held(m))` |
| `(*sync.RWMutex).Lock` | `~held(rw)`, `~rheld(rw)` | `held(rw')`, `~rheld(rw')` |
| `(*sync.RWMutex).Unlock` | `held(rw)` | `~held(rw')`, `rheld(rw') <-> rheld(rw)` |
| `(*sync.RWMutex).RLock` | `~held(rw)`, `~rheld(rw)` | `rheld(rw')`, `~held(rw')` |
| `(*sync.RWMutex).RUnlock` | `rheld(rw)` | `~rheld(rw')`, `held(rw') <-> held(rw)` |
| `(*sync.RWMutex).TryLock` | | `result -> ~held(rw) And ~rheld(rw) And held(rw')`, `~result -> (held(rw') <-> held(rw))`, `rheld(rw') <-> rheld(rw)` |
| `(*sync.RWMutex).TryRLock` | `~rheld(rw)` | `result -> ~held(rw) And rheld(rw')`, `~result -> ~rheld(rw')`, `held(rw') <-> held(rw)` |

Every one also requires that the receiver is not `nil` and lists the receiver under `modifies`. A failed `TryLock` or `TryRLock` changes no state. `rheld(rw)` is true when the goroutine holds a read lock on `rw`. The goroutine can hold at most one, because the documentation of `sync` rules out recursive read locking: a second `RLock` can wait for a writer that waits for the first. For the same reason, `RLock` and `Lock` require that the goroutine holds neither lock, and `TryRLock` requires that it holds no read lock.

#### Doing something once

`(*sync.Once).Do` has a shipped contract too. Its state `running(o)` is true while the goroutine that runs the function is inside a call of `Do` on `o`:

```go
// Settings is set up once.
type Settings struct {
	once sync.Once
	size int
}

// Setup sets the size the first time it is called.
//
// @Requires c != nil And ~running(c.once)
// @Modifies c.once, c.size
// @Ensures ~running(c.once')
func (c *Settings) Setup(n int) {
	c.once.Do(func() { c.size = n })
}
```

`Do` requires `~running(o)`, because `Do` on a `Once` whose `Do` the goroutine is inside waits for itself. A function that is not verified could call `Setup` from the function it hands to `Do` on the same `Once`. The function literal that `Do` runs is checked as described in [Functions that a trusted function calls](#functions-that-a-trusted-function-calls). It may not write `c.once`, so it cannot call `Do` on `c.once` either. After `Do` nothing is known of `c.size`, since the function may have run in this call, in an earlier one, or in another goroutine. While `Setup` waits in `Do` for a function that another goroutine runs, that function may write memory that `Setup` relies on. The proof assumes that it does not, as for any other goroutine. See [What a proof of a function that locks shows](#what-a-proof-of-a-function-that-locks-shows). A function literal that `Do` runs cannot call `Do` on another `Once`, for the reason given in [Locking in a function that a trusted function calls](#locking-in-a-function-that-a-trusted-function-calls).

The contract is:

| Method | Requires | Ensures | Calls |
| --- | --- | --- | --- |
| `(*sync.Once).Do` | `o != nil`, `~running(o)` | `~running(o')` | `f()` with no conditions, at most once and only before `Do` returns (`vego` checks the function for any number of calls) |

#### What a proof of a function that locks shows

A verified function that locks a mutex is proved for one goroutine. The proof shows these things about that goroutine:

- It never locks a mutex that it holds.
- It never unlocks a mutex that it does not hold.
- It writes only what `Modifies` lists.
- It meets its contract.

Each of these holds only if no other goroutine writes memory that the function reads or writes while it runs, including while it waits in `Lock`, `RLock`, or `Do`. The one exception is that other goroutines can lock and unlock a mutex that this goroutine does not hold, and call `Do` on a `sync.Once` that this goroutine is not inside `Do` on, which writes that `Once`. What the function that another goroutine hands to `Do` writes is not part of the exception. Taking a lock does not change that assumption. `vego` still assumes that nothing else writes the memory that the lock protects.

So the proof does not show that other goroutines take the lock before they touch the same memory. It also does not show that what the lock protects is unchanged between an `Unlock` and the next `Lock`. A verified function that locks is not proved to be safe to call from several goroutines.

This contract is proved, and it is false in a program where two goroutines deposit at the same time:

```go
// DepositSum adds n to the balance and says what the balance becomes.
//
// @Requires a != nil And ~held(a.mu) And 0 <= n
// @Modifies a.mu, a.balance
// @Ensures ~held(a.mu')
// @Ensures ok -> a.balance' = a.balance + n
func (a *Account) DepositSum(n int) (ok bool) {
	a.mu.Lock()
	defer a.mu.Unlock()
	if n > 1000000-a.balance {
		return false
	}
	a.deposit(n)
	return true
}
```

While `DepositSum` waits in `Lock`, another goroutine can take the lock, deposit, and unlock. `a.balance` on return is then more than `a.balance + n` for the value of `a.balance` at the call. `vego` proves the clause because it assumes that no other goroutine writes `a.balance`. Do not relate the value that memory has when the function is called, before it takes the lock, to its value on return. Other goroutines can change it while the function waits in `Lock`. A contract of a function that runs while the caller holds the lock, such as `deposit`, can relate them.

The lock discipline rests on the same assumption. This function is proved, and it crashes if another goroutine changes `t.on` between the two `if` statements:

```go
// Switch locks only when on is set.
type Switch struct {
	mu sync.Mutex
	on bool
	n  int
}

// @Requires t != nil And ~held(t.mu)
// @Modifies t.mu, t.n
// @Ensures ~held(t.mu')
func (t *Switch) Step() {
	if t.on {
		t.mu.Lock()
	}
	t.n = 1
	if t.on {
		t.mu.Unlock()
	}
}
```

A proof about several goroutines needs goroutines and channels, which `vego` does not support yet.

#### Values that hold a mutex cannot be copied or overwritten

`sync` documents that a mutex and a `Once` must not be copied after first use. `vego` refuses every copy and every assignment of a value that holds a mutex: a `sync.Mutex`, a `sync.RWMutex`, a `sync.Once`, or a struct with one as a field at any depth. Such a value can only be created, used through a pointer, and changed through the methods of the mutex.

```go
// Snapshot copies the account, and its mutex with it.
//
// @Requires a != nil
// @Ensures True
func Snapshot(a *Account) (balance int) {
	b := *a
	return b.balance
}
```

```text
vego: cannot verify Snapshot: *a copies a value of type Account, which holds a sync.Mutex; use a
pointer to it; a value that holds a state, such as a sync.Mutex, must not be copied or overwritten,
since its state changes only through its methods and sync documents that a Mutex must not be copied
after first use
```

These are refused, each with a message that says what to write instead:

- a value of such a type that is assigned, passed, returned, converted, or put into a composite literal, as `*a` above;
- a parameter, result, or receiver of such a type, since the value is copied at the call or the return;
- a method with a value receiver of such a type, called directly or through a pointer, and a pointer converted to an interface whose method has such a receiver;
- a field selected from a value that cannot be addressed, as in `m[k].balance` for a map of such structs, and a call that returns such a value;
- a `range` variable that holds an element of such a type, and the variable of a three-clause `for` loop of such a type;
- an assignment to a variable, field, or element of such a type, as in `*a = Account{}`;
- `append` to a slice of such elements, since `append` copies every element when it moves the slice.

A composite literal, a variable declaration without a value or with a composite literal, `new`, `&Account{}`, and `make([]Account, n)` create new values and are allowed. So are `a.mu.Lock()`, `as[i].mu.Lock()`, and `&as[i]`, which use the value where it is. Hold such values by pointer, and build a slice of them with its final length.

#### Locking in a function that a trusted function calls

A function literal that a trusted function calls while it runs, such as the function that `sort.Search` calls, cannot lock a mutex that exists when the trusted function is called. It cannot call `Do` on such a `sync.Once` either:

```go
// SearchLocked locks the account in each call of the function that
// sort.Search calls.
//
// @Requires a != nil And ~held(a.mu) And 0 <= n
// @Modifies a.mu
// @Ensures True
func SearchLocked(a *Account, n int) (i int) {
	return sort.Search(n, func(k int) bool {
		a.mu.Lock()
		defer a.mu.Unlock()
		return k > 3
	})
}
```

```text
vego: precondition of Lock may not hold: ~held(m), in the function literal run by sort.Search at
guide.go:895:24
```

`vego` checks such a literal once for every call, in a state where everything that any call writes is unknown. The mutex is one of those things, so whether the goroutine holds it is not known there. A mutex that the literal creates itself can be locked. Lock outside the call instead. See [Functions that a trusted function calls](#functions-that-a-trusted-function-calls).

#### Trusted contracts for functions that lock

A trusted function that locks a mutex that it reaches must require that the caller does not hold it, as in `~held(c.mu)`. Without that clause, its claim that it returns is false whenever the caller holds the mutex. A `modifies` that covers a struct that holds a mutex makes the caller forget whether it holds the mutex, unless the `ensures` says so again, as in `~held(c.mu')`.

A formula can name an unexported field only of a struct declared in the package where the formula is written. For an entry in the trust file, that is the package of the function or type the entry describes, and a shipped entry can name none. So `a.mu.mu` is refused outside package `sync`. The fields of a mutex differ between versions of Go, and other goroutines change them. Speak of a mutex through `held` and `rheld`.

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
| key | yes | The full name of the function as Go prints it, such as `sort.Ints`, `example.com/pkg.Func`, or `(*bytes.Buffer).Len`. For a method of an interface or a function type of another module, the method or the type, such as `(io.Writer).Write` or `context.CancelFunc`; see [Interfaces and function types of other packages](#interfaces-and-function-types-of-other-packages). |
| `reason` | yes | Why you believe the contract. |
| `modifies` | yes | What the function may write, in the form of a `Modifies` clause. `[x]` is the elements of slice `x`, `[b]` is the struct `b` points to, and `[b.count]` is one field. For an interface value, `[r]` is every state of what `r` holds, for an `io.Reader` or an `any` too. Write `modifies: []` if it writes nothing a caller can see and changes no state of an interface value. |
| `receiver` | no | For a method of an interface, the name that the contract uses for the value the method is called on. See [States of interface values](#states-of-interface-values). |
| `requires` | no | A list of formulas. Callers must prove each one. |
| `ensures` | no | A list of formulas. Callers can assume each one. |
| `runs` | no | Parameters that carry code the function may call, at any depth inside the value. See [Arguments that carry code](#arguments-that-carry-code). |
| `keeps` | no | Parameters whose code the function keeps after it returns, each with the results and parameters it keeps it in, as in `r: [result]`. See [Functions that keep what they are given](#functions-that-keep-what-they-are-given). An entry that does not list a parameter claims that the function keeps nothing of it once it returns. For a method of an interface, that claim covers every implementation. |
| `vouches` | no | Error results whose errors verified code may format, compare, and pass to `errors.Is`, results that hold function values or interface values verified code may call, and parameters under whose memory the function writes such values. See [Errors that a trusted function returns](#errors-that-a-trusted-function-returns) and [Function values and interface values that a trusted function returns](#function-values-and-interface-values-that-a-trusted-function-returns). |
| `calls` | no | Function parameters that the function calls while it runs, each with what holds when it calls them. See [Functions that a trusted function calls](#functions-that-a-trusted-function-calls). |
| `formats` | no | The parameter of type `any` or `...any` whose values the function formats as package `fmt` does, and the string it uses as the format, if any. See [Your own logging function](#your-own-logging-function). |
| `prints` | no | For a function that formats and writes to a writer it is given, as `{w: fmt.Sprintf}`: the writer, and a function of the same package that takes the other parameters. It claims that the function formats as that one does, calls `Write` of the writer once with exactly what that one returns, calls nothing else of the writer, and returns what `Write` returned. A call into a `*bytes.Buffer`, a `*strings.Builder`, or a `*bufio.Writer` is then checked as described in [Formatting into a buffer](#formatting-into-a-buffer). The entry may require no more than that the writer is not nil, list only the writer in `modifies`, and have no `ensures`, `keeps`, or `calls`. |

Put the formulas in quotes. Several characters that formulas use have a special meaning in YAML.

A function that builds a string or a slice in proportion to its arguments panics when what it builds is more than can be allocated. Its entry must bound the arguments under `requires`, as the shipped entry of `strings.Repeat` does with `"|s| * count <= MaxAlloc"`. Nothing else stops a call that asks for more. A buffer that grows by `append` may be given twice the room it needs, so bound twice the length, as the shipped entry of `strings.ToUpper` does with `"6 * |s| + 65544 <= MaxAlloc"`. A function that joins the elements of a `[]string` builds at most as many copies of the longest element and the separator as there are elements, so its entry bounds each element, as the shipped entry of `strings.Join` does:

```yaml
    requires:
      - "Forall i in [0, |elems|) : |elems| * (|elems[i]| + |sep| + 1) <= MaxInt"
      - "Forall i in [0, |elems|) : |elems| * (|elems[i]| + |sep| + 1) <= MaxAlloc"
```

A caller proves it from a bound on every element, as in `@Requires |parts| <= 100 And Forall i in [0, |parts|) : |parts[i]| <= 100`. On a 32-bit target, where `MaxAlloc` is larger than `MaxInt`, both bounds are needed, since the length is an `int`.

The names in an entry are the parameter and result names from the function's source, including the receiver. For the standard library, `go doc -src bytes.Buffer.Len` shows that the receiver is called `b`. If the function does not name its results, use `result` for a single result, or `result1`, `result2`, and so on for several. This applies only to trusted contracts, because a verified function must name its results.

### Shipped contracts

`vego` includes contracts for these functions of the standard library:

- `sort.Ints`, `sort.IntsAreSorted`, `sort.SearchInts`, `sort.Search`, `sort.Find`, `sort.Strings`
- `strings.Contains`, `strings.HasPrefix`, `strings.HasSuffix`, `strings.Index`, `strings.LastIndex`, `strings.IndexByte`, `strings.LastIndexByte`, `strings.Cut`, `strings.TrimPrefix`, `strings.TrimSuffix`, `strings.TrimSpace`, `strings.Split`, `strings.Fields`, `strings.Join`, `strings.Replace`, `strings.ReplaceAll`, `strings.Repeat`, `strings.Count`, `strings.EqualFold`, `strings.ToUpper`, `strings.ToLower`, `strings.TrimLeft`, `strings.TrimRight`, `strings.SplitAfter`
- `bytes.Contains`, `bytes.HasPrefix`, `bytes.HasSuffix`, `bytes.Index`, `bytes.LastIndex`, `bytes.IndexByte`, `bytes.LastIndexByte`, `bytes.Cut`, `bytes.TrimPrefix`, `bytes.TrimSuffix`, `bytes.TrimSpace`, `bytes.Equal`, `bytes.Join`, `bytes.Replace`, `bytes.ReplaceAll`, `bytes.Repeat`, `bytes.Count`, `bytes.EqualFold`
- `strings.IndexFunc`, `strings.LastIndexFunc`, `strings.ContainsFunc`, `strings.FieldsFunc`, `strings.TrimFunc`, `strings.TrimLeftFunc`, `strings.TrimRightFunc`, `strings.Map`, and the `bytes` functions of the same names
- `unicode/utf8.RuneCountInString`, `unicode/utf8.DecodeRuneInString`, `unicode/utf8.DecodeRune`, `unicode/utf8.AppendRune`, `unicode/utf8.RuneLen`, `unicode/utf8.ValidString`
- `unicode.IsSpace`, `unicode.IsDigit`, `unicode.IsLetter`, `unicode.IsUpper`, `unicode.IsLower`, which say what they report for ASCII and for a value that is no character
- `strconv.Itoa`, `strconv.Atoi`, `strconv.ParseInt`, `strconv.ParseUint`, `strconv.ParseBool`, `strconv.FormatInt`, `strconv.AppendInt`, `strconv.Quote`, `strconv.Unquote`
- `math.Sqrt`, `math.Min`, `math.Max`, `math.Abs`, `math.Floor`, `math.Ceil`, `math.Trunc`, `math.Round`, `math.Pow`, `math.Mod`, `math.Log`, `math.Exp`, `math.Inf`, `math.NaN`, `math.IsNaN`, `math.IsInf`, which say only that they return and write nothing, since nothing can be stated of a float
- the methods `Date`, `Year`, `Month`, `Day`, `Hour`, `Minute`, `Second`, `Nanosecond`, `Weekday`, `YearDay`, `Unix`, `UnixMilli`, `Add`, `AddDate`, `Sub`, `Before`, `After`, `Equal`, and `IsZero` of `time.Time`, `time.Now`, `time.Since`, `time.Until`, `time.Unix`, `time.Date`, and the methods `Seconds`, `Milliseconds`, and `Nanoseconds` of `time.Duration`
- `os.Remove`, `os.Open`, `os.Create`, `os.WriteFile`, `os.MkdirAll`, `os.Getenv`, `os.LookupEnv`, `os.Getwd`, and the methods `Read`, `Write`, and `Close` of `*os.File`, described in [Reading and writing files](#reading-and-writing-files)
- `math/rand.Intn`, `math/rand.Int`
- `fmt.Sprintf`, `fmt.Sprint`, `fmt.Sprintln`, `fmt.Printf`, `fmt.Print`, `fmt.Println`, `fmt.Fprintf`, `fmt.Fprint`, `fmt.Fprintln`, described in [Formatting and logging](#formatting-and-logging)
- `io.NopCloser`, `io.LimitReader`, `io.TeeReader`, `io.MultiReader`, `io.MultiWriter`, described in [Wrappers in package io](#wrappers-in-package-io)
- `bufio.NewScanner` with `Scan`, `Text`, and `Err`; `bufio.NewReader` with `ReadByte`; `bufio.NewWriter` with `Write`, `WriteByte`, and `Flush`; and the states `ready` of `bufio.Scanner`, `bufio.Reader`, and `bufio.Writer`, described in [Wrappers of readers and writers](#wrappers-of-readers-and-writers)
- the methods `Write`, `WriteString`, `WriteByte`, `WriteRune`, `Grow`, `Len`, `String`, and `Reset` of `*strings.Builder`, and the same with `Bytes` and `Truncate` of `*bytes.Buffer`, described in [Building text in a buffer](#building-text-in-a-buffer)
- `log.Printf`, `log.Print`, `log.Println`, `log.New`, and the methods of `*log.Logger` of the same names, with the state `ready` of `log.Logger`, described in [Writing to a writer or a logger](#writing-to-a-writer-or-a-logger)
- `path.Join`, `path.Clean`, `path.Dir`, `path.Base`, `path.Ext`, `path.IsAbs`, `path.Split`, `path/filepath.Join`, `path/filepath.Clean`, `path/filepath.Dir`, `path/filepath.Base`, `path/filepath.Ext`, `path/filepath.Rel`, `path/filepath.Split`. The bound `|result| <= |path| + 2` of `path/filepath.Clean` and `Dir` allows for Windows, where `Clean` can put `.\` before a path. It is read from the source for every system, and the tests check it on Unix only.
- `regexp.Compile` and the methods `MatchString`, `Match`, `FindString`, and `FindStringSubmatch` of `*regexp.Regexp`, which say nothing of what matches
- `(*net/http.Request).PathValue`, `(net/http.Header).Get` and `Set`, and `net/http.NewServeMux`
- the methods of `sync.Mutex` and `sync.RWMutex` that lock and unlock, and `(*sync.Once).Do`, described in [Locks](#locks)

It also includes contracts for generic functions of `slices`, `maps`, and `cmp`, described in [Generic functions of other packages](#generic-functions-of-other-packages), and for `(io.Writer).Write`, `(io.Reader).Read`, `(io.Closer).Close`, `(context.Context).Err`, and `context.CancelFunc`, which are described in [Interfaces and function types of other packages](#interfaces-and-function-types-of-other-packages), and the state `closed` of `io.Closer`, described in [States of interface values](#states-of-interface-values).

A function of package `bytes` with two slice parameters cannot be given one slice twice, or two slices that may share memory. `bytes.Equal(a, a)` is reported as `the slices passed to Equal as a and b may overlap`, as for any function with two slice parameters of one element type (see [Slices that share no memory](#slices-that-share-no-memory)).

The contracts are in `vego/trusted/std` in the source of `laas`. They state only behaviour that the function's documentation promises, read from the documentation of the oldest Go that `laas` builds with. A clause that the documentation does not give, such as `fresh` of a result, a `requires` that keeps an allocation within bounds, or a claim under `vouches`, rests on reading the function's source, and the reason of the entry says what was read. The tests of `vego` check each contract against the real function. For a function that calls a function it is given, the tests also check that it calls it only with arguments that its contract under `calls` allows. The contracts of `strconv.Atoi`, `strconv.ParseInt`, `strconv.ParseUint`, `strconv.ParseBool`, `strconv.Unquote`, `path/filepath.Rel`, `regexp.Compile`, `(context.Context).Err`, and the functions of `os` that return an error vouch for their errors. For those, the tests also check that every error in the tree of a returned error has a type whose methods were read against what `vouches` claims. A contract for a method of an interface or a function type is tested against several implementations from the standard library, and against one that does at random everything the documentation of the type allows. An entry in your own file with the same key replaces the shipped contract.

### What the shipped contracts do not say

A shipped contract states only what the documentation of its function promises, and some of that has no formula yet. So some contracts say less than you may need:

- `strings.Index`, `strings.LastIndex`, `strings.Cut`, `strings.Contains`, and their `bytes` forms do not say that the instance they find is the first or the last, or that `-1` or `false` means that there is none. `strings.IndexByte` and `strings.LastIndexByte` say both of a byte.
- `sort.Strings` does not say that the strings are in order. It says that each element after the call is one of those before it, and that each one before is still there, but not how many times.
- The predicates of `unicode` say what they report for ASCII, and nothing of other characters.
- `strconv.Unquote` does not bound the length of its result. `strconv.Quote` bounds its result by `10 * |s| + 2`.
- The functions of `math` say only that they return.
- The functions of `os` say nothing of the files they read or write.
- The contracts of `strings.Builder` and `bytes.Buffer` say how long the buffer is and nothing of what it holds.
- The contracts of generic functions say only what can be read at every type argument they are used with. `slices.Clone`, `Grow`, `Clip`, `Delete`, `DeleteFunc`, `Insert`, `Reverse`, and `Compact` do not say what the elements are, and `Delete`, `DeleteFunc`, and `Compact` do not say that they set the elements they drop to zero. `slices.Sort` does not say that the elements are in order, and `cmp.Compare` does not say which of `-1` and `1` it returns. `slices.ContainsFunc` and `IndexFunc` do not say which element the function they are handed chose. The functions of `maps` say how many keys a map has and which keys it has, and nothing of what it holds under a key.
- The documentation of `slices.Grow` says that the result has the nilness of `s`. For a nil `s` and an `n` above 0 it returns a slice that is not nil, so the contract says only that a slice that is not nil gives one that is not nil, and that a nil `s` with `n` equal to 0 gives nil.

Some functions of the standard library have no shipped contract, because no true contract can be written yet:

- `os.ReadFile` does not return for every input. See [Reading and writing files](#reading-and-writing-files).
- `os.ReadDir` and `os.Stat` return values of `io/fs.DirEntry` and `io/fs.FileInfo`, whose methods have no contracts. `os.ReadDir` also collects every entry of a directory, which on a 32-bit target can be more than can be allocated.
- `flag.Parse` can end the program.
- `sort.SearchStrings` needs a sorted slice of strings, and a formula cannot say that.
- `bytes.Split` and `bytes.Fields` return slices inside their argument, which a contract cannot say of every element.
- The methods of `bytes.Buffer` and `strings.Builder` that read, `ReadFrom`, `WriteTo`, and the methods that speak of the capacity. See [Building text in a buffer](#building-text-in-a-buffer).
- `(*regexp.Regexp).FindStringIndex` names its result differently in different releases of Go.
- `regexp.MustCompile` panics on a pattern that does not compile. Call `regexp.Compile` and handle its error.
- `http.Error` and the `Header` method of `http.ResponseWriter` write memory of the writer.
- `slices.SortFunc` and `slices.BinarySearchFunc` require that the comparison function is a strict weak ordering, which a contract cannot require of a function it is handed. See [Sorting a slice of structs](#sorting-a-slice-of-structs).
- `maps.Keys`, `maps.Values`, and the other functions that return iterators need a range over a function.

### Generic functions of other packages

A verified function can call a generic function, such as `slices.Contains`, when the function has a trusted contract. The contract is an entry of the trust file, shipped or your own, under the generic name of the function:

```go
// HasRole reports whether role is one of roles.
//
// @Ensures r <-> Exists i in [0, |roles|) : roles[i] = role
func HasRole(roles []string, role string) (r bool) {
	return slices.Contains(roles, role)
}
```

These generic functions have shipped contracts:

- `slices.Contains`, `slices.Index`, `slices.Equal`, `slices.ContainsFunc`, `slices.IndexFunc`
- `slices.Clone`, `slices.Grow`, `slices.Clip`, `slices.Delete`, `slices.DeleteFunc`, `slices.Insert`, `slices.Reverse`, `slices.Compact`
- `slices.Sort`, `slices.BinarySearch`, `slices.Max`, `slices.Min`
- `maps.Clone`, `maps.Copy`, `maps.DeleteFunc`
- `cmp.Compare`

`vego` does not verify generic code. A generic function of your own package can be called in the same way, when your trust file gives it an entry. A generic function with annotations is reported as `generic functions are not supported yet`.

#### What a contract means at each type argument

One entry serves every type argument. At each call, `vego` reads the entry at the type arguments of that call. A clause means there what it means of those types:

- for integers, `=`, `<`, and arithmetic are those of numbers;
- for strings, `=` compares the bytes, as Go's `==` does, and a formula has no order of strings;
- for booleans, `=` is the same truth value;
- for pointers, `=` says that they point to the same place, and a pointer to a value of size zero can only be compared with `nil`;
- a struct cannot be compared or used as a whole;
- nothing can be said of a float.

A call at which a clause of the entry has no meaning is refused. The message names the clause, the type argument, and what to call instead:

```go
// HasMember asks for a whole struct.
//
// @Ensures True
func HasMember(ms []Member, m Member) (r bool) {
	return slices.Contains(ms, m)
}
```

```text
vego: the trusted contract of slices.Contains (slices.yaml:21) cannot be used with S = []Member,
E = Member: in its ensures "result <-> Exists i in [0, |s|) : s[i] = v": a value of type E, which is
Member here, is a struct, and a formula cannot compare a struct or use it as a whole; call
slices.ContainsFunc instead, with a function literal that compares what you need of the elements,
or write a loop
```

`slices.ContainsFunc` and `slices.IndexFunc` take a function literal, which `vego` verifies where it is written, as for any function that a trusted function calls (see [Functions that a trusted function calls](#functions-that-a-trusted-function-calls)). The literal can compare the fields:

```go
// HasName looks for a member by name.
//
// @Ensures r -> |ms| > 0
func HasName(ms []Member, name string) (r bool) {
	return slices.ContainsFunc(ms, func(m Member) bool { return m.Name == name })
}

// AgeOf returns the age of the member with a name, or -1.
//
// @Ensures True
func AgeOf(ms []Member, name string) (age int) {
	i := slices.IndexFunc(ms, func(m Member) bool { return m.Name == name })
	if i < 0 {
		return -1
	}
	return ms[i].Age
}
```

The contract of `IndexFunc` says that the result is `-1` or an index of `ms`, so `ms[i]` is in range after the test. It does not say which element the function chose. A formula cannot apply the literal to a struct, so the literal is verified for every value of its parameter's type.

The functions whose elements may be of any type, such as `Clone`, `Delete`, `Insert`, and `DeleteFunc`, have contracts that say only lengths, capacities, whether a slice is nil, and where the result lies. They can be used with slices of structs. `Contains`, `Index`, and `Equal` say which elements are equal, and cannot be used with structs or floats. `Max`, `Min`, and `BinarySearch` order elements, and cannot be used with strings or floats:

```go
// Oldest returns the greatest age.
//
// @Requires |ages| > 0
// @Ensures Forall i in [0, |ages|) : ages[i] <= r
func Oldest(ages []int) (r int) {
	return slices.Max(ages)
}

// Last returns the name that sorts last.
//
// @Requires |names| > 0
// @Ensures True
func Last(names []string) (r string) {
	return slices.Max(names)
}
```

```text
vego: the trusted contract of slices.Max (slices.yaml:247) cannot be used with S = []string,
E = string: in its ensures "x[0:|x|) <= result": operator <= cannot be applied to string or slice
values; a formula has no order of them; write a loop instead
```

`slices.Sort` and `cmp.Compare` say nothing about order, so that they can be used with strings. [What the shipped contracts do not say](#what-the-shipped-contracts-do-not-say) lists what each contract leaves out.

#### Type arguments that cannot be passed

`vego` refuses a call of a generic function with any of these type arguments:

- a type that can hold code, such as an error, an interface, or a function;
- a type that `vego` does not model, such as an array or `complex128`;
- an interface where the constraint is `comparable`, since `==` on two interface values can panic;
- a type that holds a `sync.Mutex`, a `sync.RWMutex`, or a `sync.Once`, since generic functions copy their elements;
- a type with methods, or whose values hold values with methods, unless the entry claims that the function runs none of them.

```go
// CloneErrors copies a slice of errors.
//
// @Requires |errs| <= 100
// @Ensures True
func CloneErrors(errs []error) (r []error) {
	return slices.Clone(errs)
}
```

```text
vego: cannot verify CloneErrors: slices.Clone is called with S = []error, which is or holds an
error; a generic function cannot be called yet with a type argument that can hold code
```

Generic code can reach the methods of its type arguments through its constraint, by converting a value to an interface, and by reflection. Each shipped entry claims that its function runs none of them, so `slices.Sort` of a type with a `String` method is verified. A generic function of your own needs that claim to be called with such a type (see [Writing an entry for a generic function](#writing-an-entry-for-a-generic-function)).

#### Memory and allocation

`slices.Grow` returns memory that is new or lies within its argument. A write past the length of what it returns writes the argument's memory when there was room, so the function must list the argument:

```go
// AppendZero grows buf by one element and sets it.
//
// @Requires |buf| < 1000
// @Ensures |r| = |buf| + 1
func AppendZero(buf []byte) (r []byte) {
	r = slices.Grow(buf, 1)
	r = r[:len(r)+1]
	r[len(r)-1] = 0
	return r
}
```

```text
vego: r[len(r) - 1] is assigned, which AppendZero may not modify; it is memory that Grow returned,
which its contract places within s when it is not new, and AppendZero passed buf as s; list buf in a
// @Modifies clause
```

`slices.Clone` returns a new slice, so its own elements can be written without a `Modifies` entry. What those elements point to is shared with the slice that was copied, so a write through `c[0][0]` of a clone of a `[][]int` still needs one.

The functions that allocate, `Clone`, `Grow`, and `Insert`, require that what they allocate can be allocated. Their `requires` uses `elemsize(s)`, the number of bytes of an element of `s`, which depends on the type argument (see [Formulas](#formulas)). For `slices.Grow` it is `2 * (|s| + n) * elemsize(s) + 65536 <= MaxAlloc`, and `|s| + n <= MaxInt`, which is the only bound for elements of size zero.

#### Sorting a slice of structs

`slices.SortFunc` and `slices.BinarySearchFunc` have no shipped contract. Their documentation requires that the comparison function is a strict weak ordering, and a contract cannot yet require that of a function it is handed.

When the verified code needs the values of one field in order, copy them out and sort them with `slices.Sort`:

```go
// SortedNames returns the names of the members in order, which are new.
//
// @Requires |ms| <= 1000
// @Ensures |r| = |ms|
func SortedNames(ms []Member) (r []string) {
	r = make([]string, len(ms))
	// @Invariant 0 <= i And i <= |ms| And |r| = |ms|
	// @Variant |ms| - i
	for i := 0; i < len(ms); i++ {
		r[i] = ms[i].Name
	}
	slices.Sort(r)
	return r
}
```

To sort the structs themselves, write the call of `slices.SortFunc` in a function of your own that is not verified, and give that function an entry in your trust file:

```go
// SortByAge sorts members by age. It is not verified: its contract is an
// entry of the project's trust file.
func SortByAge(ms []Member) {
	slices.SortFunc(ms, func(a, b Member) int { return cmp.Compare(a.Age, b.Age) })
}

// YoungestFirst sorts members by age and returns the youngest age.
//
// @Requires |ms| > 0
// @Modifies ms
// @Ensures Forall i in [0, |ms|) : r <= ms'[i].Age
func YoungestFirst(ms []Member) (r int) {
	SortByAge(ms)
	return ms[0].Age
}
```

```yaml
  guide.SortByAge:
    reason: >-
      SortByAge calls slices.SortFunc with a function that returns
      cmp.Compare(a.Age, b.Age). That is a strict weak ordering, since
      cmp.Compare of two integers is the order of the integers, so the
      documentation of SortFunc says that it sorts ms in ascending order of
      age. It calls no method of a Member and keeps nothing.
    modifies: [ms]
    ensures:
      - "Forall i in [0, |ms|) : Forall j in [i, |ms|) : ms'[i].Age <= ms'[j].Age"
```

The entry claims that after the call the members are in ascending order of age, and that the call writes only `ms`. That claim is about your own code. Its comparison compares two integers with `cmp.Compare`, which is an order, so the documentation of `slices.SortFunc` promises the result. A contract for `slices.SortFunc` itself would have to hold for every comparison function a caller could hand it, and for one that is not an order the documentation promises nothing.

#### Writing an entry for a generic function

An entry for a generic function of your own uses the parameter names of the generic signature. This helper of a package is called from verified code under an entry of the project's trust file:

```go
// Votes counts how often v occurs in s.
func Votes[S ~[]E, E comparable](s S, v E) int {
	n := 0
	for _, x := range s {
		if x == v {
			n++
		}
	}
	return n
}

// CountVotes counts the votes for a name.
//
// @Ensures 0 <= r And r <= |names|
func CountVotes(names []string, name string) (r int) {
	return Votes(names, name)
}
```

```yaml
  guide.Votes:
    reason: >-
      Votes counts the elements of s that are equal to v, in a loop over s
      that calls no method of a value of type S or E, or of what such a
      value holds, and keeps nothing.
    asserts: {S: [], E: []}
    modifies: []
    ensures:
      - "0 <= result And result <= |s|"
```

`asserts: {S: [], E: []}` claims that the function runs no method of a value of type `S` or `E`, or of a pointer to one, or of anything such a value holds. The claim covers what the function calls too, `fmt` and `reflect` included. It holds while the call lasts and later, through anything the function returns, keeps, or registers. Read the function's source before you write it. For a type parameter only the empty list can be claimed.

`vego` checks the entry at each type argument it is called with, as it checks any entry (see [What is checked in an entry](#what-is-checked-in-an-entry)). It also refuses a clause that names a field, a state, or an address of a value of a type parameter, such as `s[0].Name`, at every type argument. A type parameter has no fields. A clause that contradicts itself at one type argument only, as `result > 300` does for a `uint8` result, is refused at that type argument and used at the others.

#### What is not supported yet

- Generic functions as values, as in `f := slices.Contains[[]int]`, and handing one to a trusted function.
- Methods of generic types, such as `atomic.Pointer[T].Load`, reported as `calls of methods of generic types are not supported yet`.
- `maps.Keys`, `maps.Values`, and the other functions that return iterators, which need a range over a function.
- A clause that holds only for some type arguments, such as an order that `Sort` could state for integers.

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

A trusted contract describes what the function's own code does. Some arguments bring code with them. An `error` has methods, and their code is chosen by whoever created the error. The same is true of other interface values. A struct can have a field that holds a function, and the value can be nested at any depth inside a struct, slice, or map. A field of type `unsafe.Pointer` counts too, also one that its type does not export, since it can point to a function or an interface value. A trusted function could call that code, for example `err.Error()` or `l.sink(text)`, and the code could write memory that your proof depends on.

Two types of the standard library are counted by what their package lets their `unsafe.Pointer` hold:

- `sync/atomic.Pointer[T]` counts as a `*T`. Its package stores only a `*T` there, so it holds code exactly when `T` does.
- `runtime.Pinner` counts as holding nothing. It holds the pointers it pins, and nothing calls them.

So an `*os.File` carries no code. Its only `unsafe.Pointer` is in an `atomic.Pointer` of a type that holds no code, and on Windows also in a `runtime.Pinner`.

A state of an interface value counts as memory that a caller can see. A trusted function that may close a value it is given, also one that it type-asserts from an `io.Reader` or an `any`, must list that parameter in `modifies`. Otherwise its entry claims that the state stays as it was.

For this reason `vego` refuses to pass such a value to a trusted function:

```text
vego: cannot verify TellsUnknown: e is passed to tell, which is trusted, and is an error
whose origin is not known; tell could run code through it that nobody has seen. If its
contract holds whatever that code does, list e under runs in the contract if tell runs it
only while the call lasts, or under keeps, with where it keeps it, if it keeps it in a
result or a parameter for later calls
```

There are three ways to deal with this.

The first is to pass an error that verified code created with `errors.New` or `fmt.Errorf`, or one that a contract vouches for. An error that verified code created has only the standard library's methods and wraps nothing from outside. An error variable also qualifies if its initialiser used only plain values and other errors of this kind, in its own package or another. `var ErrRead = fmt.Errorf("read: %w", io.EOF)` qualifies. `var ErrLate = fmt.Errorf("late: %w", context.DeadlineExceeded)` does not, because `context.DeadlineExceeded` is not made by `errors.New` or `fmt.Errorf`.

The second is to make the call from unverified code. This is the right choice for logging an error that came from elsewhere. The unverified caller logs the error, and the verified function only returns it.

A function that only formats what it is given, as `fmt.Println` and `log.Printf` do, needs no `runs`. Its entry lists the values under `formats` instead, and `vego` checks each value at each call, as described in [What can be formatted](#what-can-be-formatted).

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
- Once it returns, it holds no value that can hold code anywhere that value was not held when the call began, unless the entry lists the parameter under `keeps`.

A method of a logger with `runs: [l]` meets the third claim. The logger held its writer before the call, and it holds the same writer afterwards.

A function that stores a callback and calls it later, such as one that registers a handler, makes these claims false. Do not list its parameter under `runs` alone. If it keeps the callback in a result, or in memory that a parameter reaches, list the parameter under `keeps`, as described in [Functions that keep what they are given](#functions-that-keep-what-they-are-given). Otherwise call the function from code that is not verified.

When the parameter can hold a function value of a type with a contract (see [Function values](#function-values)), `runs` claims that the function calls such a value only with arguments that meet the `Requires` clauses of its type. The same goes for an interface value with a method that has a contract (see [Interfaces](#interfaces)): the function calls such a method only with arguments that meet the method's `Requires`. For a function value of a type with a contract, and an interface value whose methods all have contracts, the rest of the claim then has to hold only for values that meet their contracts, and every value that verified code passes does. For any other code, the claim has to hold whatever code arrives. That includes an interface value of a type with a method that has no contract, even when other methods of the type have one, such as `context.Context`. It also includes the methods of an interface without contracts, such as `fmt.Stringer`, an `any`, and an interface type written in place that embeds a named one.

A trusted function may run code that verified code made when it lists under `runs` a parameter that can hold a function value, or an interface value whose methods all have contracts. Verified code can make values of those, and of no other interface. It makes a value of an interface whose contracts speak of a state, such as `io.ReadCloser`, only through a trusted function that keeps a value it is given in such an interface. See [Making a value of an interface with a state](#making-a-value-of-an-interface-with-a-state) and [Functions that keep what they are given](#functions-that-keep-what-they-are-given). That code could call back into the verified code that handed it over. So a function that calls such a trusted function cannot itself be made into a function value or a method of an interface value. The message says which call and which parameter are the reason:

```text
vego: cannot verify MakeSink: logNumber may call through a function value or an interface value,
and code that a function value runs cannot do that yet: no contract of a function type or of a
method of an interface has a variant, so nothing would prove that such calls end; logNumber calls
logRecord, which is trusted and runs what r holds, which can be a value of io.Writer, whose methods
all have contracts, so that it can hold code that verified code made. Make the value in code that
is not verified, or keep that call out of what logNumber runs
```

A trusted method that is made into a function value, as in `w.Get`, or into a method of an interface value is handed its receiver at each call. If the receiver can carry code, the entry must list it under `runs`, as for a call written out.

The trust report shows `runs`, so that a reviewer of the trust file notices the larger claim.

### Functions that a trusted function calls

Some functions take a function and call it while they run, such as `sort.Search` and `strings.IndexFunc`. You can hand such a function a function literal written at the call. `vego` verifies the literal there, with what is known at the call:

```go
// @Requires Forall i in [0, |s|) : Forall j in [i, |s|) : s[i] <= s[j]
// @Ensures 0 <= i <= |s|
// @Ensures Forall k in [0, i) : s[k] < x
// @Ensures i < |s| -> s[i] >= x
func Position(s []int, x int) (i int) {
	return sort.Search(len(s), func(i int) bool { return s[i] >= x })
}
```

The literal reads `s[i]`. That read is in range because the contract of `sort.Search` says that it calls the function only with an `i` in `[0, n)`, and `n` is `len(s)` here. The shipped contract is:

```yaml
  sort.Search:
    reason: Documented to call f(i) only for i in the range [0, n), and ...
    requires:
      - "n >= 0"
    runs: [f]
    calls:
      f(i):
        requires: ["0 <= i < n"]
    modifies: []
    ensures:
      - "(Forall i in [0, n) : Forall j in [i, n) : f(i) -> f(j)) -> (0 <= result And result <= n And (Forall i in [0, result) : ~f(i)) And (result < n -> f(result)))"
```

The field `calls` gives a contract to a function parameter. Its key names the parameter and gives names to the parameters of its function type, as in `f(i)`, or `do()` for a function without parameters. The `requires` under it states what holds whenever the trusted function calls `f`. It can name the parameters of `f` and those of the trusted function. It is read in the state at the time of that call. The parameter must also be listed under `runs`.

#### What can be handed over

These can be handed to a parameter with a contract under `calls`:

- a function literal written at the call;
- a function, as in `strings.IndexFunc(line, isSeparator)`;
- a method value, as in `c.bump`, whose receiver is evaluated at the call;
- a value of a named function type with a contract, which must not be nil.

A function or a method value is checked as a call of its contract with the arguments the trusted function passes. A value is checked as a call of the contract of its type. Anything else is reported as `cannot verify`. That includes a value of a function type without a contract, `nil`, and a variable that holds a literal:

```go
// @Ensures True
func FieldsOf(line string) (n int) {
	isComma := func(r rune) bool { return r == ',' }
	return len(strings.FieldsFunc(line, isComma))
}
```

```text
vego: cannot verify FieldsOf: isComma holds a function literal and is used here other than by
calling it; a variable that holds a function literal is supported only when it is never assigned
again and only called. To use the literal as a value, declare the variable with a function type
that has a contract, as in var isComma T = func...; to hand it to a trusted function that calls
it, write the literal where it is handed over
```

A literal, a function, or a method value passed to a parameter that the entry lists under `runs` without a contract under `calls` is reported too. With an entry for `each` that has `runs: [f]` and no `calls`:

```go
// @Ensures True
func Visits(n int) {
	each(n, func(i int) {})
}
```

```text
vego: cannot verify Visits: the function literal is handed to each as f, which its trusted contract
lists under runs with no contract under calls; give f a contract under calls in the entry for
guide.each
```

#### What a run knows

Each call that the trusted function makes of what it was handed is a run. The trusted function may make any number of runs, including none, in an order you do not know, between writes of its own and writes of earlier runs. So `vego` verifies a run once, in a state that stands for all of them. In that state:

- everything known at the call holds, except what the handed functions or the trusted function may write;
- the arguments meet the `requires` under `calls`.

After the call, what the handed functions may write is forgotten, as a loop forgets what its body writes. That covers the variables a literal assigns and the memory it writes:

```go
// @Ensures ~seen
func HasComma(line string) (seen bool) {
	_ = strings.IndexFunc(line, func(r rune) bool {
		if r == ',' {
			seen = true
		}
		return false
	})
	return seen
}
```

```text
vego: postcondition may not hold: ~seen
```

A run is part of the function that hands it over. It is held to the built-in checks, to the `Modifies` clauses of that function, and to the order of evaluation. A run that calls that function again is recursion of it, checked against its `Variant`. A message about a run ends in `, in the function literal run by sort.Search at f.go:L:C`, or `, in isSeparator run by strings.IndexFunc at f.go:L:C`.

A call that hands over a function cannot be deferred, and a trusted function that calls a function it is given cannot be used as a function value.

#### What a run may write

A run may not write anything that the trusted function's `modifies` covers. That includes memory the calling function created:

```yaml
  example.com/shop.count:
    reason: Calls record once and then adds one to t.Calls; reviewed 2026-11-19.
    requires: ["t != nil", "t.Calls < 1000"]
    runs: [record]
    calls:
      record(): {}
    modifies: [t]
    ensures: ["t.Calls' = t.Calls + 1"]
```

```go
// @Requires t != nil And t.Calls < 1000
// @Modifies t
// @Ensures True
func Reset(t *Hits) {
	count(t, func() {
		t.Calls = 0
	})
}
```

```text
vego: t.Calls is assigned, which count may write itself while it runs the function it is
handed; a function it is handed may not write what it may write, in the function literal run by
count at callbacks.go:75:11
```

The contract of `count` describes what `count` does to `t`. If a run could write `t` too, the contract would no longer say what `t` holds afterwards. A run could also call the trusted function again on the same memory. For `(*sync.Once).Do` that would never return. A function that `Do` runs and that calls `Do` on the same `Once` waits for itself. The rule covers such a call too, since the inner call writes what the outer one does. A run could also copy the `Once` while `Do` holds its lock and call `Do` on the copy, which never returns either. `vego` refuses that copy. See [Locks](#locks) for the shipped contract of `Do`.

#### Results that depend on what is handed over

The `ensures` of an entry can apply a function parameter with a contract under `calls`, as in `f(i)` above. `f(x)` is the value that `f` returns for `x`. `f` must have one integer parameter and one integer or boolean result. The `requires` under `calls` must not read memory, and no `requires` of the entry can apply `f`.

This is only meaningful when `f` returns the same result whenever it is called with the same argument. So for every function handed to such a parameter, `vego` proves that it does, in every state a run stands for:

```go
// @Requires n >= 0
// @Ensures True
func Coin(n int) (i int) {
	return sort.Search(n, func(i int) bool {
		return rand.Intn(2) == 0
	})
}
```

```text
vego: the function literal run by sort.Search is not proved to return the same result whenever
it is called with the same argument, which the trusted contract of sort.Search relies on
```

A result that depends on something a run writes, or on memory that the trusted function writes, is reported the same way. The proof compares the values a function returns. For a pointer or a slice that is the pointer or the slice itself, not the memory it refers to. An entry whose documentation assumes such a function, as that of `strings.FieldsFunc` does, says `deterministic: true` under the key, and the same proof is made without an application:

```yaml
    calls:
      f(c):
        deterministic: true
```

After the call, `vego` knows, for every argument that the type of `f` and the `requires` under `calls` allow, that `f(x)` is what a run with that argument returns. In `Position` that is `f(i) <-> s[i] >= x`. Together with the order of `s` it proves that `f` is false and then true, so the `ensures` of `sort.Search` gives the result.

#### What a contract under calls claims

`calls` adds to what `runs` claims. With `calls`, the entry claims these things:

- The function calls a parameter under `calls` only with arguments that meet its `requires`, in the state at that call.
- The rest of the contract holds for every function that meets those `requires`, returns, and writes nothing the entry's `modifies` covers, whatever else it writes. That includes memory that the trusted function reads.
- With `deterministic: true`, or when the `ensures` applies the parameter, the contract has to hold only for a function that returns the same result whenever it is called with the same argument. `f(x)` in the `ensures` is the value that such a function returns for `x`.

The trust report shows each contract under `calls` in a line such as `calls f(i) when: 0 <= i < n`.

### Functions that keep what they are given

Some functions keep a value they are given and run its code later. A registry keeps a handler and calls it when it fires:

```go
// Event is called with a number that is not negative.
//
// @Requires n >= 0
// @Ensures True
type Event func(n int)

type Hub struct {
	events []Event
}

func (h *Hub) Add(e Event) { h.events = append(h.events, e) }

func (h *Hub) Fire(n int) {
	for _, e := range h.events {
		e(n)
	}
}
```

`runs` cannot describe `Add`, because `Add` keeps `e` after it returns. List the parameter under `keeps` instead, with the results and parameters in which the function keeps it:

```yaml
  (*example.com/app/events.Hub).Add:
    reason: Appends e to the events of h, which only Fire reads; it calls nothing. Read 2026-11-20.
    requires: ["h != nil"]
    runs: [h]
    keeps:
      e: [h]
    modifies: [h]
    vouches: [h]

  (*example.com/app/events.Hub).Fire:
    reason: Calls each event of h with n, on the calling goroutine, before it returns. Read 2026-11-20.
    requires: ["h != nil", "n >= 0"]
    runs: [h]
    modifies: []
```

With these entries, a verified function can register a handler and fire it:

```go
// @Requires n >= 0
// @Ensures True
func record(n int) {}

// @Requires h != nil
// @Modifies h
// @Ensures True
func Subscribe(h *Hub) {
	h.Add(record)
	h.Fire(1)
}
```

`Add` lists `h` under `runs` as well, because `h` holds code. Every trusted function that is handed a value that can hold code must list it under `runs` or `keeps`. Its `vouches: [h]` claims that what it writes into `h` meets the contract of `Event`.

#### What keeps claims

By listing a parameter under `keeps` with its destinations, you claim all of this about the function, for whatever code the parameter holds:

- While the call lasts, the function runs none of that code, unless `runs` lists the parameter too.
- When it returns, it holds the code only in memory that the destinations reach.
- It has started or registered nothing that runs the code later. That rules out a goroutine, a timer, a finalizer or cleanup, a callback given to another package such as `context.AfterFunc`, and a package-level variable.

As for `runs`, for a function value of a type with a contract and an interface value whose methods all have contracts, the claim has to hold only for values that meet their contracts. For any other code it has to hold whatever code arrives.

Under this claim, the code runs later only in code that holds a reference to the kept value, which it can reach only through a destination or a copy of one. Go's types then make that a call of a trusted function that is handed a value that can hold code, or a call through a function value or an interface value. A trusted function handed such a value lists it under `runs`, and its entry then covers what the kept code does during that call: it runs the code only before it returns, only on its own goroutine, and writes nothing outside its `modifies`. A call through a value is counted as one that may call through a value. So `Fire` above cannot be made to call back into the verified code that registered the handler without the cycle being refused, as described in [Arguments that carry code](#arguments-that-carry-code).

A function that keeps a callback somewhere no destination reaches has no true entry. This applies to `http.HandleFunc`, `time.AfterFunc`, and a function that stores a handler in a package-level registry. Call such a function from code that is not verified.

#### Checking an entry against the source

Before you write `keeps` for a function of another module, read its source and check these things:

1. Find where the argument is stored, directly or inside another value. Each place must be inside a result or inside memory that a listed parameter reaches.
2. Find every read of each of those places. Each read must be in a function or method that runs when it is called. None may be in a goroutine (`go`), a timer (`time.AfterFunc`, a `time.Timer` or `time.Ticker`), a finalizer or cleanup (`runtime.SetFinalizer`, `runtime.AddCleanup`), or a callback that the function registers with another package (`context.AfterFunc`).
3. Check that no package-level variable holds the argument or what it is stored in.
4. Check what the functions that read it run of the kept value, because their entries make claims about it. A type assertion of the kept value to another interface, such as `w.(io.StringWriter)`, followed by a call, runs a method that no contract covers, and makes the entry of that function false.

This entry looks true and is not:

```go
func NewPrefetcher(r io.Reader) *Prefetcher {
	p := &Prefetcher{r: r, ahead: make(chan []byte, 1)}
	go p.fill()
	return p
}
```

`NewPrefetcher` stores `r` only in its result, so `keeps: {r: [result]}` looks right. But it starts a goroutine, `p.fill`, that calls `r.Read` while the caller goes on. The entry would be false.

#### What a function finds on what it is handed

A function of another package that is handed an interface value may assert it to another type, or use reflection, and call what it finds. `vego` then counts every method with an exported name and every function value of your package as code the call may run (see [Cycles through function values and interface methods](#cycles-through-function-values-and-interface-methods)). An entry may claim more, under `asserts`, for each parameter that can hold code, the receiver of a method included:

```yaml
  io.NopCloser:
    asserts:
      r: [io.WriterTo]
```

By listing a parameter under `asserts`, you claim all of this about the function, while the call lasts, and when what it returns or keeps is called later through the entries of the methods of what it returns:

- It calls nothing that the parameter holds, or that a call of what the parameter holds returns, at any depth, but the methods of the interfaces and the function values of the function types that the parameter's type reaches through fields, elements, and pointers, and those of the listed types.
- It finds the listed types, and no others that hold code, by a type assertion, and uses no reflection to call what the parameter holds.

An empty list, `r: []`, claims that it asserts the value to nothing that holds code. A method of a concrete type of another package that holds no code, such as `syscall.Errno`, runs only its own code and need not be listed. Write an interface that cannot be named by its methods, as `"interface{ Timeout() bool }"`, which may use only predeclared types. The claim affects only which cycles `vego` reports.

Read the source to check the claim. Every type assertion on the value, or on what it is stored in, and every call of what it holds, has to be within the list. An assertion to a concrete type of another package, such as `bufio`'s `w.(*Writer)` in `NewWriterSize`, needs no listing when what it leads to calls only methods the parameter's type already has.

The shipped entries with `asserts` are tested by a harness whose readers and writers also have the methods of the other optional interfaces of `io` and `fmt` and return errors that record their calls. A call of one of those methods fails the test. The harness catches only the interfaces it has methods of, so the claim rests on reading the source, as `keeps` does.

An entry with `asserts` cannot be used when any of these holds:

- A listed name is not a parameter, or its type can hold no code.
- A listed type does not resolve, holds no code, or is an interface written by its methods with a type that is not predeclared.
- The parameter is listed under `formats`, which says already what the function runs of it.
- The parameter of a function is listed under neither `runs` nor `keeps`.

#### What vego checks in an entry with keeps

An entry with `keeps` cannot be used when any of these holds:

- A listed name is not a parameter, or its type can hold no code.
- A parameter is listed with no destination.
- A destination is not a result or another parameter, or its type can hold no code.
- A destination is a parameter under which `modifies` lists nothing that can hold the kept code. Keeping a value in memory that a parameter reaches writes that memory.
- The kept parameter can hold a function value, or a value of an interface whose methods all have contracts, and a destination can hold neither. A later call handed that destination would run code that verified code made without being counted.
- The parameter has a contract under `calls`, or is listed under `formats`.

A function literal, a function, or a method value of a function type without a contract cannot be handed to a parameter under `keeps`. A trusted function with `keeps` cannot be made into a function value or a method of an interface value.

### Wrappers of readers and writers

`vego` ships entries for `bufio.NewScanner`, `bufio.NewReader`, and `bufio.NewWriter`, for some methods of what they return, and for the wrappers of package `io`. Each keeps the reader or writer it is given, and the methods of what it returns run it later.

#### Reading lines

A `bufio.Scanner` reads lines from a reader:

```go
// @Requires r != nil And limit >= 0
// @Modifies r
// @Ensures 0 <= n And n <= limit
func PrintLines(r io.Reader, limit int) (n int, err error) {
	sc := bufio.NewScanner(r)
	// @Invariant 0 <= n And n <= limit And ready(sc)
	// @Variant limit - n
	for n < limit && sc.Scan() {
		fmt.Println(sc.Text())
		n++
	}
	return n, sc.Err()
}
```

`Scan`, `Text`, and `Err` are the methods with entries. `Scan` and `Text` require the state `ready` of the scanner. It holds when the scanner was made by `bufio.NewScanner` with a reader that is not `nil`, and neither `Split` nor `Buffer` has been called on it since. `NewScanner` ensures it, and `Scan` keeps it. A loop that calls `Scan` forgets it, as it forgets what any call writes, so the loop's invariant must state `ready(sc)`.

`Text` returns at most 65536 bytes, the size of the buffer of a ready scanner. That bound lets `fmt.Println(sc.Text())` be proved not to build more than can be allocated.

A loop needs a variant, and a reader may never end. So `for sc.Scan()` alone cannot be verified:

```go
// @Requires r != nil
// @Modifies r
// @Ensures True
func ReadAll(r io.Reader) {
	sc := bufio.NewScanner(r)
	for sc.Scan() {
	}
}
```

```text
vego: loop needs a // @Variant annotation to prove that it terminates
vego: precondition of Scan may not hold: ready(s)
```

Bound the number of lines, as `PrintLines` does.

A scanner that code which is not verified hands your function may have another split function. Require the state in the contract, `@Requires sc != nil And ready(sc)`, and list the scanner under `@Modifies`.

`ReadString`, `ReadBytes`, `ReadLine`, `ReadSlice`, and `(*bufio.Scanner).Bytes` have no entries:

- `ReadString` and `ReadBytes` do not return from a reader that never sends the delimiter. They grow their buffer until the program runs out of memory. Use a `Scanner`, whose buffer is bounded.
- `ReadLine`, `ReadSlice`, and `Bytes` return a slice of the buffer that the next call overwrites. No entry can name that memory.

#### Errors that pass through

The error that `Err` returns may be one that the reader returned. Under the shipped entries nothing is known of it, so a function can return it as it is, as `PrintLines` does, but cannot wrap it:

```go
// @Requires r != nil And limit >= 0
// @Modifies r
// @Ensures 0 <= n And n <= limit
func ReadLines(r io.Reader, limit int) (n int, err error) {
	sc := bufio.NewScanner(r)
	// @Invariant 0 <= n And n <= limit And ready(sc)
	// @Variant limit - n
	for n < limit && sc.Scan() {
		fmt.Println(sc.Text())
		n++
	}
	if err := sc.Err(); err != nil {
		return n, fmt.Errorf("read lines: %w", err)
	}
	return n, nil
}
```

```text
vego: cannot verify ReadLines: formatting err would run the methods of an error whose origin is
not known; only an error made by errors.New or fmt.Errorf, here or in a verified function, or one
that a contract vouches for, can be formatted
```

To wrap it, your trust file needs an entry for `(io.Reader).Read` that vouches for the errors of the readers your callers pass, as described in [Wrapping the errors of Read and Write](#wrapping-the-errors-of-read-and-write). It also needs an entry for `Err` that vouches for what it returns:

```yaml
  (*bufio.Scanner).Err:
    reason: >-
      Err returns nil, an error that the reader returned other than io.EOF,
      or an error of bufio or io made by errors.New (ErrTooLong,
      ErrNegativeAdvance, ErrAdvanceTooFar, ErrBadReadCount, io.ErrNoProgress).
      A ready Scanner splits with ScanLines, which returns no error. Our entry
      for (io.Reader).Read vouches for the errors of every reader; reviewed
      2026-11-20.
    requires: ["s != nil", "ready(s)"]
    runs: [s]
    vouches: [result]
    modifies: []
```

With both entries, `ReadLines` verifies. The claim of the `Err` entry rests on the claim of the `Read` entry. If the `Read` entry is false for some reader, so is this one.

#### Writing through a buffer

A `*bufio.Writer` made over `w` writes what `w` writes, and memory of its own. `bufio.NewWriter` returns the writer it is given when that writer is already a large enough `*bufio.Writer`, and then what it returns is memory that `w` writes. Its entry says `fresh(result, w)` (see [New values and values made over a writer](#new-values-and-values-made-over-a-writer)), so `Modifies w` covers what the writes through it change:

```go
// @Requires w != nil
// @Modifies w
// @Ensures True
func WriteBuffered(w io.Writer) (err error) {
	bw := bufio.NewWriter(w)
	if _, err = bw.Write([]byte("done\n")); err != nil {
		return err
	}
	return bw.Flush()
}
```

Without `w` in `Modifies`, the write is reported:

```go
// @Requires w != nil
// @Ensures True
func WriteBufferedUnlisted(w io.Writer) (err error) {
	bw := bufio.NewWriter(w)
	_, err = bw.Write([]byte("done\n"))
	return err
}
```

```text
vego: Write may modify bw, which WriteBufferedUnlisted may not modify; it is memory that NewWriter returned,
which its contract places in the footprint of w when it is not new; list w in a // @Modifies clause
```

A function can also take the `*bufio.Writer` as a parameter. It then lists the writer and requires that it is ready:

```go
// @Requires bw != nil And ready(bw)
// @Modifies bw
// @Ensures True
func WriteTotal(bw *bufio.Writer, total []byte) (err error) {
	if _, err = bw.Write(total); err != nil {
		return err
	}
	return bw.Flush()
}
```

A `*bufio.Writer` cannot be converted to an `io.Writer`. Its `Write` calls through the writer it keeps, and nothing proves yet that calls through values that wrap values end:

```go
// @Requires w != nil
// @Modifies w
// @Ensures True
func WriterAsWriter(w io.Writer) (err error) {
	bw := bufio.NewWriter(w)
	var x io.Writer = bw
	_, err = x.Write([]byte("x"))
	return err
}
```

```text
vego: cannot verify WriterAsWriter: converting a value of type *bufio.Writer to io.Writer is not supported yet: its
Write calls through the writer it keeps, and nothing proves yet that calls through values that wrap values end; pass
the Writer itself to fmt.Fprintf, Fprint, or Fprintln, which then calls its own Write, or format into a string, as
with fmt.Sprintf, and pass it to the Writer's own Write as []byte(s)
```

It can be handed to `fmt.Fprintf` all the same. No interface value is made: `vego` checks the call as `fmt.Sprintf` followed by the Writer's own `Write`, whose entry requires `ready(bw)` (see [Formatting into a buffer](#formatting-into-a-buffer)):

```go
// @Requires w != nil And 0 <= n <= 1000
// @Modifies w
// @Ensures True
func WriteCount(w io.Writer, n int) (err error) {
	bw := bufio.NewWriter(w)
	if _, err = fmt.Fprintf(bw, "%d items\n", n); err != nil {
		return err
	}
	return bw.Flush()
}
```

Formatting into a string first and writing it with the Writer's own `Write` verifies too:

```go
// @Requires w != nil And 0 <= n <= 1000
// @Modifies w
// @Ensures True
func WriteCountFormatted(w io.Writer, n int) (err error) {
	bw := bufio.NewWriter(w)
	s := fmt.Sprintf("%d items\n", n)
	if _, err = bw.Write([]byte(s)); err != nil {
		return err
	}
	return bw.Flush()
}
```

`Write`, `WriteByte`, and `Flush` have entries. `ready(bw)` holds when the last of `bufio.NewWriter`, `bufio.NewWriterSize`, and `Reset` that set the writer's output set one that is not `nil`. `WriteString` has no entry, because it calls the `WriteString` method of the writer it wraps when that writer has one, and no entry covers that method. Write `bw.Write([]byte(s))` instead.

The same holds for a `*bufio.Reader`. `bufio.NewReader` may return the reader it is given, and its entry says `fresh(result, rd)`. `ReadByte` requires `ready(br)`.

Some values of the standard library own memory besides their struct. Their methods write that memory, and a `Modifies` clause that lists such a value covers it. These are the values and what each owns:

- a `*bytes.Buffer` and a `*strings.Builder` own the array of their buffer, and a struct that holds one by value owns that array too;
- a `*bufio.Writer`, a `*bufio.Reader`, and a `*bufio.Scanner` own the array of their buffer and the writer or reader they keep;
- a `*log.Logger` owns the writer it writes to.

So a write to `bw` may change a byte slice that is the writer's buffer. A slice that the function was given may be that buffer, since nothing says where its caller got it:

```go
// @Requires bw != nil And ready(bw) And |p| > 0
// @Modifies bw
// @Ensures r = p[0]
func WriteThenRead(bw *bufio.Writer, p []byte) (r byte) {
	_ = bw.WriteByte('x')
	return p[0]
}
```

```text
vego: postcondition may not hold: r = p[0]
```

Read what you need before the write, or use memory that the function makes itself. The methods of the writer make the only new memory that the writer comes to own, so memory that the function makes lies apart from what the writer owns.

A value that owns memory cannot be copied or overwritten, as a value that holds a mutex cannot (see [Values that hold a mutex cannot be copied or overwritten](#values-that-hold-a-mutex-cannot-be-copied-or-overwritten)). A copy would share what the original owns:

```text
vego: cannot verify CopiesBuffer: *b copies a value of type bytes.Buffer, which owns memory; use a pointer
to it; a value that owns memory must not be copied or overwritten, since a copy
would share what the original owns, which only the methods of each may write
```

Only the shipped entries and verified functions may write such a value. A call of a function that your trust file gives a `modifies` over one is reported, because nothing says how what the value owns changes:

```text
vego: cannot verify ResetsByProject: resetWriter may modify bw, a *bufio.Writer, which owns memory, and
only a contract that comes with vego or a verified function says how what such a value owns may change
```

#### Wrappers in package io

`io.NopCloser`, `io.LimitReader`, `io.TeeReader`, `io.MultiReader`, and `io.MultiWriter` have shipped entries. Each keeps the readers and writers it is given in the value it returns, and that value's `Read`, `Write`, or `Close` meets the entry of its interface whenever what it keeps meets theirs:

```go
// @Requires r != nil And log != nil
// @Modifies r, log
// @Ensures True
func ReadLogged(r io.Reader, log io.Writer) (err error) {
	rc := io.NopCloser(io.TeeReader(r, log))
	defer rc.Close()
	_, err = rc.Read(make([]byte, 512))
	return err
}
```

Each requires that what it is given is not `nil`. A read through what they return writes what the readers and writers they keep write, so a function lists each of them, as `ReadLogged` lists `r` and `log`.

Call `MultiReader` and `MultiWriter` with each reader or writer written out as its own argument. List each of those arguments:

```go
// @Requires header != nil And body != nil
// @Modifies header, body
// @Ensures True
func ReadParts(header, body io.Reader) (err error) {
	all := io.MultiReader(header, body)
	_, err = all.Read(make([]byte, 512))
	return err
}
```

A `*os.File` writes nothing behind the file, so `io.MultiWriter(os.Stdout, f)` with a file `f` needs nothing listed.

A slice handed whole, as in `io.MultiReader(parts...)`, is not supported yet. No `Modifies` clause can name what the readers of a slice write, so the read is refused:

```go
// @Requires Forall i in [0, |parts|) : parts[i] != nil
// @Ensures True
func ReadAllParts(parts []io.Reader) (err error) {
	all := io.MultiReader(parts...)
	_, err = all.Read(make([]byte, 512))
	return err
}
```

```text
vego: all.Read may modify the footprint of all, which ReadAllParts may not modify; it is a value that
MultiReader returned at wrappers.go:114:9, and its contract places its footprint in those of what parts
holds, which no // @Modifies clause can list yet; pass the values written out, one argument each, and
list each of them
```

`NopCloser` ensures that what it returns is new and not closed, so a function can close it once. Closing it closes nothing of the reader it wraps.

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

### Reading and writing files

The shipped contracts of `os.Open`, `os.Create`, and the `Read`, `Write`, and `Close` methods of `*os.File` vouch for their errors, so you can wrap them with `%w`. `os.ReadFile` has no shipped contract. It does not return for a file that never ends, such as `/dev/zero`, or for one larger than can be allocated, and a shipped contract cannot know which files your program reads. Read a file with a loop that stops at a bound:

```go
// ReadConfig reads at most 4096 bytes of a file.
//
// @Requires |name| <= 4096
// @Ensures err = nil -> |data| <= 4096
func ReadConfig(name string) (data []byte, err error) {
	f, err := os.Open(name)
	if err != nil {
		return nil, fmt.Errorf("open %s: %w", name, err)
	}
	buf := make([]byte, 4096)
	n := 0
	// @Invariant 0 <= n And n <= 4096 And |buf| = 4096 And fresh(buf)
	// @Variant 4096 - n
	for n < len(buf) {
		m, rerr := f.Read(buf[n:])
		n += m
		if rerr == io.EOF || m == 0 {
			break
		}
		if rerr != nil {
			f.Close()
			return nil, fmt.Errorf("read %s: %w", name, rerr)
		}
	}
	if cerr := f.Close(); cerr != nil {
		return nil, fmt.Errorf("close %s: %w", name, cerr)
	}
	return buf[:n], nil
}
```

The loop stops when a read returns no bytes, since the contract of `Read` allows a read of none without an error, and then the `Variant` would not decrease.

If your program reads only files that it controls, you can give `os.ReadFile` an entry of your own. The entry claims something about the files your program reads, so its reason must say what they are:

```yaml
  os.ReadFile:
    reason: >-
      This program reads only regular files that it wrote itself, each small
      enough to be read into memory twice over. os.ReadFile returns for
      such a file; it does not for a file that never ends, such as
      /dev/zero, or one larger than can be allocated, so that is what this
      entry claims of every name passed to it. The rest is read from the
      source of os: ReadFile opens the file as os.Open does, reads it with
      (*os.File).Read into new memory, and closes it, so its errors are
      those that the shipped entries of Open and Read vouch for, and its
      result is new memory.
    requires:
      - "|name| < MaxInt"
      - "4 * |name| + 65536 <= MaxAlloc"
    vouches: [result2]
    modifies: []
    ensures:
      - "fresh(result1)"
```

The `requires` and the `vouches` are those of `os.Open`, and the tests of `vego` check the entry against `os.ReadFile` on regular files. The claim about which files are read is yours. With the entry, a function can wrap the error:

```go
// @Requires |name| <= 4096
// @Ensures True
func LoadSettings(name string) (data []byte, err error) {
	data, err = os.ReadFile(name)
	if err != nil {
		return nil, fmt.Errorf("load %s: %w", name, err)
	}
	return data, nil
}
```

`vego` decides whether an error can be formatted from what its variable can hold where it is formatted. That is the errors assigned to the variable on the paths that lead there. In `WriteReport`, only the error of `os.Create` reaches the `%w`. The later call of `fmt.Fprintln`, whose errors nothing vouches for, reuses `err` after the `%w`, so it does not matter:

```go
// @Requires |name| <= 4096 And |title| <= 1000
// @Ensures True
func WriteReport(name, title string) (err error) {
	f, err := os.Create(name)
	if err != nil {
		return fmt.Errorf("create %s: %w", name, err)
	}
	_, err = fmt.Fprintln(f, title)
	f.Close()
	return err
}
```

If any path to the `%w` brings an error that nothing vouches for, the `%w` is refused. Here both calls lead to the same `%w`:

```go
// @Requires |name| <= 4096 And |title| <= 1000
// @Ensures True
func ReportOnce(name, title string) (err error) {
	f, err := os.Create(name)
	if err == nil {
		_, err = fmt.Fprintln(f, title)
		f.Close()
	}
	if err != nil {
		return fmt.Errorf("report %s: %w", name, err)
	}
	return nil
}
```

```text
vego: cannot verify ReportOnce: formatting err would run the methods of an error whose origin is not
known; only an error made by errors.New or fmt.Errorf, here or in a verified function, or one that a
contract vouches for, can be formatted; err may hold here the error assigned fmt.Fprintln(f, title) at
files.go:75:12, a call whose errors nothing vouches for, on a path that reaches this use; give that
error a variable of its own
```

Wrap the error of `os.Create` where it is returned, as `WriteReport` does, and return the error of `fmt.Fprintln` unwrapped. A loop counts as a path too. An error assigned at the end of one iteration reaches a `%w` at the start of the next.

`vego` follows a variable along the paths only in the function or the function literal that declares it. Some variables are decided from every assignment to them in the function instead, wherever the error is used:

- a variable that a function literal assigns, unless the literal is written in a `defer` statement of the function or literal that declares the variable, as in `defer func() { ... }()`;
- a variable used inside a function literal, at that use.

A function literal can run between any two statements of the function around it, so what it assigns may reach any use. A literal written in a `defer` statement of the function that declares the variable runs only when that function returns, after every use outside the literal. A literal deferred inside another function literal runs when that literal returns, so its assignments count everywhere. For a variable that is decided from every assignment, give the error you wrap a variable of its own. An error variable whose address is taken, or that a `range` assigns, has no known origin anywhere in the function.

An `*os.File` is an `io.Writer`, so `fmt.Fprintf`, `fmt.Fprintln`, and a logger made by `log.New` can write to it:

```go
// @Requires |name| <= 4096 And |line| <= 1000
// @Ensures True
func LogToFile(name, line string) (err error) {
	f, cerr := os.Create(name)
	if cerr != nil {
		return fmt.Errorf("create %s: %w", name, cerr)
	}
	l := log.New(f, "app: ", 0)
	l.Println(line)
	return f.Close()
}
```

A `*bufio.Writer` made over the file with `bufio.NewWriter(f)` can be written through, as described in [Writing through a buffer](#writing-through-a-buffer). The `Write` of an `*os.File` writes nothing behind the file, so the function lists nothing:

```go
// @Requires |name| <= 4096
// @Ensures True
func BufferToFile(name string, line []byte) (err error) {
	f, cerr := os.Create(name)
	if cerr != nil {
		return fmt.Errorf("create %s: %w", name, cerr)
	}
	bw := bufio.NewWriter(f)
	if _, werr := bw.Write(line); werr != nil {
		f.Close()
		return werr
	}
	if ferr := bw.Flush(); ferr != nil {
		f.Close()
		return ferr
	}
	return f.Close()
}
```

Every call that opens, reads, or writes a file is assumed to return. See [What a proof assumes](#what-a-proof-assumes).

### Function values and interface values that a trusted function returns

A function value or an interface value that a trusted function returns is code that the author of the contract may not have read. If a result can hold, at any depth, a function value of a type with a contract or an interface value with a method that has a contract, the entry must list the result under `vouches`. Otherwise the entry cannot be used, and each call reports:

```text
the trusted contract of F cannot be used: its result m can hold a function value or an interface
value of a type with a contract; list it under vouches to claim that every such value meets the
contract of its type
```

With `vouches: [m]`, you claim that every such value in `m` meets the contract of its type, or the contracts of its methods. That includes what the contract says the value writes: nothing a caller can see outside what its `Modifies` or `modifies` lists. The claim also covers the values in memory that `m` reaches and that the function allocated or wrote during the call.

The claim cannot be made for every function. Take a function that is not verified, `NewLineWriter(c *Counter) io.Writer`, whose writer adds one to `c.N` at each `Write`. Its entry may say `modifies: []`, since the function itself writes nothing. Listing its result under `vouches` would claim that the writer writes nothing a caller can see, which is false: the caller holds `c`. Such a function needs a wrapper that verified code can call without the writer, or it stays out of verified code.

A trusted function can also write such a value into memory it is given. If its `modifies` covers memory that can hold, at any depth, a function value or an interface value of a type with a contract, list the parameter that the memory belongs to under `vouches`:

The shipped entry of `(*bufio.Scanner).Scan` is one:

```yaml
  (*bufio.Scanner).Scan:
    requires:
      - "s != nil"
      - "ready(s)"
    runs: [s]
    modifies: [s]
    vouches: [s]
    ensures:
      - "ready(s')"
```

With `vouches: [s]`, you claim that every such value that the function writes into, or leaves in, the memory its `modifies` covers under `s` meets the contract of its type. A `*bufio.Scanner` holds an `io.Reader`, which has a shipped contract. Without `vouches: [s]`, each call reports that the entry cannot be used, and says to list `s`.

With `runs: [s]`, the entry also claims that the contract of `Scan` holds whatever code `s` holds, and that includes its split function. The requires `ready(s)` limits that to scanners whose split function is `bufio.ScanLines`, as described in [Reading lines](#reading-lines).

### Interfaces and function types of other packages

An interface or a function type of another module has no doc comment that you can annotate. An entry in the trust file gives it a contract instead. The key of an entry for a method of an interface is the method as Go prints it, as in `(io.Writer).Write`. The key of an entry for a function type is the type, as in `context.CancelFunc`.

`vego` ships entries for these:

- `(io.Writer).Write`
- `(io.Reader).Read`
- `(io.Closer).Close`
- `(context.Context).Err`
- `context.CancelFunc`

With them, this verifies:

```go
// @Requires ctx != nil And cancel != nil And w != nil
// @Modifies w
// @Ensures True
func Work(ctx context.Context, cancel context.CancelFunc, w io.Writer) (err error) {
	defer cancel()
	if err := ctx.Err(); err != nil {
		return fmt.Errorf("work: %w", err)
	}
	_, err = w.Write([]byte("done"))
	return err
}
```

The shipped entries state what the documentation of each type asks of every implementation. The entry for `Write` is:

```yaml
  (io.Writer).Write:
    reason: ...
    receiver: w
    modifies: [w]
    ensures:
      - "0 <= n And n <= |p|"
      - "n < |p| -> err != nil"
```

`Write` lists its receiver, so it may write what the writer holds, as a buffer does, which is the writer's footprint (see [Methods that write behind their receiver](#methods-that-write-behind-their-receiver)). A function that writes through an `io.Writer` lists it in `Modifies`, as `Work` does. So does a function that formats into one with `fmt.Fprintf`, or that writes through a `*bufio.Writer` or a `*log.Logger` made over it. Without `w` in `Modifies`, the write is reported:

```go
// @Requires w != nil
// @Ensures True
func SaveUnlisted(w io.Writer, b []byte) (err error) {
	_, err = w.Write(b)
	return err
}
```

```text
vego: w.Write may modify the footprint of w, which SaveUnlisted may not modify; list it in a // @Modifies clause
```

The entry for `Read` says that `0 <= n <= |p|` and that `Read` may write all of `p` and what the reader holds, as a position or a buffer. A function that reads through an `io.Reader` lists it in `Modifies`. So does one that reads through a `*bufio.Scanner` or a `*bufio.Reader` made over it, and through what `io.NopCloser`, `io.LimitReader`, or `io.TeeReader` return. It also requires `|p| > 0`: the documentation says only that a `Read` into an empty slice should return 0, and `iotest.DataErrReader` never returns from one. The entry for `Err` says that the error is nil, `context.Canceled`, or `context.DeadlineExceeded`, what `errors.Is` finds in each, and vouches for them. The entry for `context.CancelFunc` says that a cancel function writes nothing that verified code can see. The entry for `Close` is described in [States of interface values](#states-of-interface-values). It claims nothing of the errors that `Close` returns.

The documentation of `io.Reader` and `io.Writer` says nothing about a value that was closed, so their entries do not speak of `closed` and hold before and after `Close`. The tests of `vego` call `Read` and `Write` after `Close` on the closers of the standard library, and each still meets its entry.

A call through such a value is checked like a call of a method with a contract in source. See [Interfaces](#interfaces) and [Function values](#function-values). The value must not be nil, the `requires` must hold, and afterwards `vego` knows the `ensures` and forgets only what `modifies` lists.

An entry for a type has the fields of a trusted contract, with three differences:

- The names are those of the method or the function type, and an unnamed result is `result`, as in a trusted contract. A method has no receiver to name.
- `runs` and `calls` are not allowed. A call through such a value cannot be handed code that nobody has seen.
- `vouches` can list only results of type `error`.

The key must name the interface that declares the method. Go gives `io.ReadWriter` the `Write` of `io.Writer`, so the entry for it is `(io.Writer).Write`, and it applies to `io.ReadWriter` too. An entry keyed `(io.ReadWriter).Write`, or by an alias or a type defined from `io.Writer`, is reported with the key to use.

An entry for a type of the module that you verify is refused. Write the contract in the doc comment where the type is declared.

#### What an entry for a type claims

An entry for a type is a claim about every value of the type that verified code gets from code that is not verified. That includes a value that a caller passes, a value in memory that an argument reaches, and a value that a call through another value returns. For an entry for a method, it includes the values of every interface that has the method from that declaration. You claim that each such value, called with arguments that meet the `requires`:

- returns without panicking;
- leaves the `ensures` true;
- writes nothing that verified code can see, outside what `modifies` lists;
- returns, in a result listed under `vouches`, only errors that meet the conditions in [Errors that a trusted function returns](#errors-that-a-trusted-function-returns);
- keeps none of the slices, pointers, and maps it is handed once the call returns, unless `keeps` lists the parameter.

The last claim is what `io.Writer` and `io.Reader` document of `p`: an implementation must not retain it. `vego` relies on it when a struct hands memory it owns to a method of an interface, as a buffered writer hands its buffer to `Write`. A verified implementation is checked for it where it is converted.

The first claim fails most often for real readers and writers. A `Read` from a pipe, a terminal, or a network connection returns only when data or an error arrives, and a reader that never makes progress never returns. A proof that a verified function ends assumes that every such call returns.

The third claim depends on the caller. A caller that is not verified can pass a `*bytes.Buffer` to one verified function twice, once as an `io.Writer` and once as a `*bytes.Buffer`. `Write` then changes memory that the function reads through its other parameter, and the claim is false. The same goes for a writer that writes into a struct and a pointer to that struct, passed together. Verified code cannot make such a pair itself.

The entry does not cover two kinds of values. A value that verified code makes is checked against the entry where it is made. A value that a trusted function returns or writes is covered by the `vouches` of that function's entry. See [Function values and interface values that a trusted function returns](#function-values-and-interface-values-that-a-trusted-function-returns).

An entry for a type may also list `asserts` for the parameters of the method or the function type, as an entry for a function does. It then claims, for every value of the type, what its call finds on what it is handed (see [What a function finds on what it is handed](#what-a-function-finds-on-what-it-is-handed)).

The trust report shows an entry for a type with a line that states this claim.

#### Making a value of such a type

Verified code can make a value of such a type from its own types and functions. The method or function is checked against the entry where the value is made:

```go
// discard writes nothing anywhere.
type discard struct{}

// @Ensures n = |p| And err = nil
func (discard) Write(p []byte) (n int, err error) {
	return len(p), nil
}

// @Ensures w != nil
func Discard() (w io.Writer) {
	return discard{}
}
```

A writer of your own whose `Write` writes its own struct converts, as described in [Converting a value of your own type](#converting-a-value-of-your-own-type). Verified code cannot pass a `*bytes.Buffer` as an `io.Writer`, since its `Write` needs a bound that the contract of `(io.Writer).Write` does not give. It can pass it to `fmt.Fprintf` itself, as described in [Formatting into a buffer](#formatting-into-a-buffer). Nor can it pass a closer of its own as an `io.Closer`, since the shipped contract of `Close` speaks of the state `closed`. See [Making a value of an interface with a state](#making-a-value-of-an-interface-with-a-state). A type whose `Write` has a contract that writes nothing behind the receiver does convert. A `net.Conn` or an `http.ResponseWriter` cannot be converted to `io.Writer` either, because each declares a `Write` of its own. See [Converting between interfaces](#converting-between-interfaces). Make such a conversion in code that is not verified.

#### Wrapping the errors of Read and Write

The shipped entries for `Read` and `Write` do not vouch for errors. The documentation of `io.Reader` and `io.Writer` says nothing about the errors an implementation returns, so verified code can return such an error and compare it with `nil`, but cannot wrap it:

```go
// @Requires w != nil
// @Modifies w
// @Ensures True
func Save(w io.Writer, b []byte) (err error) {
	if _, err := w.Write(b); err != nil {
		return fmt.Errorf("save: %w", err)
	}
	return nil
}
```

```text
vego: cannot verify Save: formatting err would run the methods of an error whose origin is not
known; only an error made by errors.New or fmt.Errorf, here or in a verified function, or one that
a contract vouches for, can be formatted
```

To wrap them, replace the shipped entry with one of your own that vouches:

```yaml
  (io.Reader).Read:
    reason: >-
      The readers our callers pass are *os.File, *bytes.Reader, and
      *bufio.Reader over those. Read returns the bytes read, 0 <= n <= len(p).
      Their errors are io.EOF and io.ErrNoProgress, made by errors.New,
      os.ErrInvalid, and *fs.PathError holding a syscall.Errno, os.ErrClosed,
      or os.ErrDeadlineExceeded, a *poll.DeadlineExceededError; the methods
      of each only read its fields; reviewed 2026-11-19.
    requires: ["|p| > 0"]
    vouches: [err]
    modifies: [p]
    ensures: ["0 <= n And n <= |p|"]
```

```go
// @Requires r != nil And |buf| > 0
// @Modifies r, buf
// @Ensures err = nil -> 0 <= n <= |buf|
func Load(r io.Reader, buf []byte) (n int, err error) {
	n, err = r.Read(buf)
	if err != nil {
		return 0, fmt.Errorf("load: %w", err)
	}
	return n, nil
}
```

With `vouches: [err]`, you claim that every reader that verified code in the module gets from code that is not verified returns only errors that meet the conditions of `vouches`: their methods return without panicking and write nothing a caller can see, `==` on them is identity, and what `errors.Is` reports of them does not change. Before you write the entry, list the readers that the callers of your verified code pass, and read the source of the errors each returns and of every error in their trees. A reader that wraps another returns the errors of the reader it wraps.

A type of your own that is converted to `io.Reader` under such an entry must return only errors of known origin, such as errors made by `errors.New` or `fmt.Errorf` and error variables that hold one. It can wrap an error of known origin with `fmt.Errorf`, as in `fmt.Errorf("read: %w", ErrLong)`.

#### Types without a shipped entry

`(fmt.Stringer).String` has no shipped entry. Its documentation states no contract, and the `String` methods of many types panic on a nil pointer.

`net.Conn` declares a `Close` of its own, so its values do not have the state `closed` of `io.Closer`, and none of its methods has an entry.

Only `Err` of `context.Context` has an entry. `Done` returns a channel, which `vego` does not model, and `Value` takes an `any`, which cannot be passed to a method of an interface value. So a `context.Context` can be passed to a verified function, and to a trusted function under `runs`, but not to a function value or to a method of an interface value, and verified code cannot make one.

`context.WithCancel` has no true entry yet, so `defer cancel()` verifies for a `cancel` that a function is given, as in `Work`, and not for one it gets from `context.WithCancel`. The function keeps its parent context in both results, so `keeps: {parent: [result1, result2]}` looks right. But for a parent of a type outside the standard library it starts a goroutine that waits on the parent's `Done`, and for a parent with an `AfterFunc` method it registers a function that runs the parent's `Value` and `Done` on whatever goroutine cancels the parent. `keeps` claims that a function starts and registers nothing that runs what it keeps, so that entry would be false (see [Functions that keep what they are given](#functions-that-keep-what-they-are-given)).

#### One entry for each type in a build

Without `-vego.trusted`, each module reads its own trust file, so two modules built together can give one type two entries. A value that one module checked against its entry could then reach verified code of the other, which relies on another entry. `vego` reports this in every package that is built with both:

```text
vego: the trust files of this build give (example.com/lib.Sink).Put two contracts, at
a/vego-trusted.yaml:4 and at b/vego-trusted.yaml:4; a value that verified code checked against one
can reach verified code that relies on the other. Make the entries the same, or run laas with
-vego.trusted naming one file
```

A module whose proofs were made with no entry for a type conflicts with a module that gives it one. With no entry, a trusted function that returns a value of the type was not asked to vouch for it:

```text
vego: the trust files of this build give (example.com/lib.Sink).Put a contract at
b/vego-trusted.yaml:4, and the proofs of package example.com/a were made with none; what they let
through can reach verified code that relies on the entry: add the same entry to the trust file of
its module, or run laas with -vego.trusted naming one file
```

The check sees only packages that are built together in one run. Run `laas` on the module of the main package as well as on the modules it uses.

### Error variables in a trusted contract

A trusted contract can name error variables, as in `err = io.EOF` and `is(err, io.EOF)`. The contract means the same in every package that calls the function, so its names do not depend on what any file imports:

- A name on its own is an error variable of the package that declares the function, such as `ErrSyntax` in an entry for `strconv.Atoi`.
- A name after the import path of its package is an error variable of that package. Write a path that is a Go identifier as in Go, as in `io.EOF`. Put any other path in quotes, as in `"io/fs".ErrNotExist` or `"example.com".ErrRoot`. YAML then needs the formula in single quotes: `'is(err, "io/fs".ErrNotExist)'`.

The package must be in the build of the package that calls the function. An entry that names a variable that does not exist, or a package that is not in the build, cannot be used. Only a trusted contract can use a path in quotes. The annotations of a verified function name packages as their file imports them.

### Limits of trusted contracts

A trusted contract does not make an unsupported signature callable. If a function has a parameter or result of an unsupported type, such as an array or a channel, verified code cannot call it even with an entry. Write a small wrapper whose signature uses only supported types, and trust the wrapper.

An entry for a method of an interface or a function type of the module that you verify is reported in the trust file:

```text
vego: the trusted contract names (example.com/shop.Store).Get, a method of an interface type of the
module of this package; write its contract in the doc comment of the method where the interface is
declared
```

Write the contract in the doc comment of the method where the interface is declared, as described in [Interfaces](#interfaces). An entry for a type of another module is described in [Interfaces and function types of other packages](#interfaces-and-function-types-of-other-packages).

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

An entry that lists parameters under `runs` or `keeps`, or results under `vouches`, shows them in the lines `runs code held by:`, `keeps code held by:`, and `vouches for the errors and function values in:`, and each contract under `calls` in a line such as `calls f(i) when: 0 <= i < n`. Each is a claim about code that `vego` does not read. See [Arguments that carry code](#arguments-that-carry-code) and [Errors that a trusted function returns](#errors-that-a-trusted-function-returns).

An entry for a method of an interface or a function type shows the reach of its claim in a line such as:

```text
    a claim about Write of every value of io.Writer, or of an interface that has Write from it, that
    verified code gets from code that is not verified: from a caller, directly or in memory an
    argument reaches, or from a call through a value; a value that a trusted function returns or
    writes is claimed by that function's vouches
```

Such an entry can be relied on where no call names it, for example where a value of the type is passed to a trusted function under `runs`. The report then lists, in a line `relied on in:`, the packages whose proofs rest on it.

When answers came from the answer cache, the report has a line `Answers of Z3 read from the answer cache:` with the directory, after its opening sentences. See [Keeping answers between runs](#keeping-answers-between-runs).

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
5. Split functions that use unsupported Go. Move the logic into a verified function that works on plain data. Leave the part that uses an interface whose methods have no contract, a function value whose type has no contract, or a goroutine unverified, and have it call the verified function.

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

The second is that a verified function can read only package-level variables that nothing changes, as described in [Package-level variables](#package-level-variables). A function that reads a counter, a cache, or another variable that is assigned must receive the value as a parameter instead.

### For one core component

The steps are the same, but design the component first so that it stays within the supported subset of Go.

- Use plain data: structs, slices, integers, strings, maps with integer, string, or boolean keys, and pointers to structs. Keep interfaces and arrays out of its types, and give every function type in them a contract.
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
- Run without `-vego.cache`, or with a cache directory that the job makes itself. A cache that other runs wrote is part of what the proofs rest on.
- Set a time limit on the job. Small functions take well under a second each. Long functions take longer: one of 120 statements that write and read a slice takes about 10 s. `-vego.rlimit` limits the work per proof obligation, not the total run time. `-vego.cost` shows which functions take the time; see [Finding out where the time goes](#finding-out-where-the-time-goes).

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
| `the contract of F cannot be used: its Ensures annotation at f.go:n:c cannot be read (...)` | A clause of the callee's contract cannot be read; it is also reported where it is written. The message ends with what the call relies on until it is fixed. | Fix the clause. See [Calls](#calls). |
| `this call may not end: F calls x.M() at f.go:n:c, which may run T.M, ...` | A cycle of calls goes through a call with no static callee, or through code of another package. The message names the cycle. | Break the cycle. See [Cycles through function values and interface methods](#cycles-through-function-values-and-interface-methods). |
| `F has annotations, so each of its results needs a name` | A verified function has an unnamed or blank result. | Name every result in the signature. |
| `an annotation is written "// @Keyword ...", with one space before the @ and none after it` (or `with nothing but one space`) | The comment looks like an annotation but has different spacing, or something stands before the `@`. | Write `// @Keyword ...`. |
| `a comment directly after an annotation is not read as part of it` | An ordinary comment follows an annotation in the same comment group. | Start the line with `// @` to continue the annotation, or put an empty `//` line before the comment. |
| `this comment has an @ and a character that ends a line on the screen but not for Go`, or `this file has annotations and a carriage return that does not end a line` | The comment contains a character such as U+2028, or a carriage return without a newline. An editor may show what follows it as a separate line, but `vego` reads it as part of the same line. | Remove the character. |
| `syntax error in Requires annotation: && is not a spelling of the formula language; write And`, and the same for `\|\|`, `!`, `==`, and `ℤ` | The formula uses a spelling of Go, or `ℤ` for the integers. | Write `And`, `Or`, `~`, `=`, or `Z`. |
| `unknown annotation "W"` | The word after `// @` is not a keyword. | Correct the keyword. If another tool reads the comment, declare the word with `-vego.other-tags`. |
| `Ensures annotation is not attached to a function` | The clause is not in the doc comment of a function. | Move it into the doc comment. |
| `x is assigned, which F may not modify; list it in a // @Modifies clause`, with `, as p.f` when a path from a parameter reaches it | No `Modifies` entry covers memory of this kind. The path stops before a field that your package cannot name, such as an unexported field of `os.File`. | Add it to `Modifies`, by the path the message names. |
| `... which F may not modify: nothing its // @Modifies clauses list is known to cover it` | An entry covers memory of this kind, but `vego` cannot prove it is this memory. It may be another element, another struct, or a slice that was replaced after `F` was called. | Make the entry match. For a replaced slice, the callee needs a `fresh ... Or within ...` clause. |
| `x.M may modify the footprint of x, which F may not modify; list it in a // @Modifies clause` | The method writes behind its receiver, and `F` does not list the value. | Add the value to `Modifies`. See [Methods that write behind their receiver](#methods-that-write-behind-their-receiver). |
| `x.M may modify the footprint of x, ...; it is a value that G returned at f.go:n:c, and its contract places its footprint in those of what s holds, which no // @Modifies clause can list yet; ...` | `x` was made over a slice of readers or writers handed whole, as in `io.MultiReader(s...)`. | Pass each reader or writer as its own argument and list each one. See [Wrappers in package io](#wrappers-in-package-io). |
| `the footprint of what is passed to G as w may hold memory that what is passed as y reaches, and G relies on it not doing so: ...` | `F` cannot show where `y` comes from, or a value of unknown origin, or a call that may store one, may have put it into memory that `y` reaches. The message says which. | Pass a value read from your own parameters or made in `F`, or one that a contract says is new or within such a value. Make the call before the one that may store. |
| `x may be read before or after the call to F, which may change it, and Go does not fix the order` | Go may read `x` before or after `F` runs in this statement, and the two are not proved to give the same value. | Read `x` or call `F` in a statement of its own, in the order you mean. The message ends with such a statement, as in `x0 := x before it`, where one fits. See [Reads that Go may make before or after a call](#reads-that-go-may-make-before-or-after-a-call). |
| `cannot verify F: g is called in the target of this assignment, and Go may call it before or after append writes into the array of s` | The call may run on either side of the write, and it may read or write memory. | Assign the result of `g` to a variable in a statement of its own first. See [An append beside a call](#an-append-beside-a-call). |
| `this may add a key to m, the map that the loop at f.go:n:c ranges over, ...` | A write in a `range` over `m` may add a key that `m` lacks. Go may or may not visit it. | Collect the new entries in another map and add them after the loop. See [Changing the map a loop ranges over](#changing-the-map-a-loop-ranges-over). |
| `F may modify m while the loop at f.go:n:c ranges over it, and may add a key, ...` | A call in a `range` over `m` may change `m`. | Change the map in the loop's body, or after the loop. |
| `what is known here says that m has a number of keys other than \|m\|, which no map can` | The clauses before a `range` over `m` describe a map whose keys and count disagree, as `\|m\| = 1 And has(m, 1) And has(m, 2)` does. | Fix the clauses that say which keys `m` has. |
| `Visited done: a Visited annotation names the keys that a range over a map has visited, ...` | The `Visited` annotation is not directly above a `range` over a map, or its name is taken, or nothing names it. The message says which. | Move it above the loop, rename it, or name it in an `Invariant`. See [Loops over a map](#loops-over-a-map). |
| `x is assigned, which F may not modify; list the whole map in a // @Modifies clause: an entry of a map whose values are pointers, ...` | `Modifies m[k]` names what the value under `k` refers to, not the entry. | List `m`, and say what is kept with `Forall k in m`. See [Writing one entry](#writing-one-entry). |
| `cannot verify F: P formats x, a value of type T, and that may run code nobody has checked: ...` | `fmt` would call a method of `x`, or of what it holds, or follow a pointer in it. The message says which. | Format the fields you need, or a string you build from them. See [What can be formatted](#what-can-be-formatted). |
| `what F builds from what it formats may be more than can be allocated` | The bound on what `fmt` writes for this call is not proved to fit in one allocation. | Bound the lengths of the strings and slices it formats, and of the format if it is not a constant. See [How long a formatted string can be](#how-long-a-formatted-string-can-be). |
| `cannot verify F: P formats what the slice s holds, which can be anything` | A slice of values to format is passed with `...`. | List the values in the call. For a logging function of your own, see [Your own logging function](#your-own-logging-function). |
| `the keys a and b of this map literal may be equal` | Two keys of a map literal are not proved to differ, so it is not known which entry the map keeps. | Prove that they differ, or assign the entries one by one. |
| `s.items may come to refer to memory that existed when F was called and that it did not own; ...` | The value stored into an owned field is memory the struct did not own: a parameter, or what another struct owns. | Copy it into new memory, as `slices.Clone` does, or do not declare the field owned. See [What an owned field may refer to](#what-an-owned-field-may-refer-to). |
| `p.items is memory that p owns, stored into memory at f.go:n:c; ...` | What a struct owns is kept somewhere other than its owned field. | Copy it, or do not declare the field owned. See [Keeping what a struct owns in one place](#keeping-what-a-struct-owns-in-one-place). |
| `F returns memory that p owns; say so with within(r, p) in an Ensures, or return a copy` | A function returns what an owner it is handed owns. | Add `within(r, p)` to its contract, or return a copy. |
| `x is memory that p owns, and G is handed what reaches a T, which can own it; ...` | A verified function is handed what an owner owns beside something that reaches an owner. | Copy it, or pass it alone. See [What a function may assume of what it is handed](#what-a-function-may-assume-of-what-it-is-handed). |
| `Modifies lists x, but F never needs to modify it` | The `Modifies` list allows more than the body needs. | Remove or narrow the entry. |
| `invariant of T may not hold for what is passed to F as x` | The struct invariant is not proved at the call. | Restore it before the call. In a loop, repeat it as a loop invariant. |
| `invariant of T may not hold for x on return` | The struct invariant is not proved at the end of the function. | Restore it before returning. |
| `the contract of F may also be met by a function that always returns an error` | No example input was found for which the contract forces success. | Add a clause of the form `condition -> err = nil`. See [Errors](#errors). |
| `specification of F has a hole` | Reported by `-vego.audit`. A trivial implementation satisfies the contract. | Relate the result to the input. |
| `nothing can satisfy the Requires clauses of F` | The `Requires` clauses contradict each other or the parameter types, so no call could satisfy them. | Fix the `Requires` clauses. |
| `the slices passed to F as a and b may overlap` | Two slice arguments with the same element type are not proved to be separate memory. | Pass two slice parameters of your own function, or a slice that the function allocated. For a slice stored in a struct, state `apart(s.items, A)` in the `Requires`. See [Slices that share no memory](#slices-that-share-no-memory). |
| `cannot verify F: it calls G, which has no contract` | `G` is neither verified nor trusted. | Annotate `G`, or add it to the trust file. |
| `cannot verify F: parameter x has unsupported type T` | `T` is outside the supported subset. | Keep `T` out of the signatures of verified functions. |
| `cannot verify F: x is assigned at f.go:n; package-level variables that are changed are not supported yet` | `F` reads a package-level variable that something in the build assigns, takes the address of, or names in a `//go:linkname` directive or in assembly. | Pass the value as a parameter. See [Which variables a function can read](#which-variables-a-function-can-read). |
| `cannot verify F: x has type T, which can hold a function value, an interface value, an error, a channel, or an unsafe.Pointer` | `F` reads a package-level variable of such a type. | Pass the value as a parameter. |
| `cannot verify F: x is a package-level variable, which a verified function cannot assign yet`, or `x[i] writes memory that the package-level variable x refers to, which a Modifies clause cannot name yet` | `F` changes a package-level variable or what one refers to. | Leave the change to code that is not verified, or pass the memory as a parameter. See [Changing a variable](#changing-a-variable). |
| `the Requires clause P reads only package-level variables, and their declarations do not show that it holds` | No caller can choose the values the clause is about. | Test the value in the body. See [What vego knows of the value](#what-vego-knows-of-the-value). |
| `x may be changed here, but proofs in package p rely on it holding the value it was declared with`, or `... rely on what it refers to being only read` | A package in the build changes a variable, or lets out a reference to what it refers to, and a proof relies on it. | Remove the change, or the proof that relies on the variable. See [What a variable refers to](#what-a-variable-refers-to). |
| `cannot verify F: formatting err would run the methods of an error whose origin is not known` | `fmt.Errorf` is given an error whose origin is not known, such as one from a parameter or from a trusted function whose contract does not vouch for it. The message names an assignment to `err` on a path to the use that gives it no known origin. | Return the error unchanged, or wrap your own error. If the error comes from a trusted function, see [Errors that a trusted function returns](#errors-that-a-trusted-function-returns). If the message says to give that error a variable of its own, do so, as in [Reading and writing files](#reading-and-writing-files). |
| `cannot verify F: comparing two errors can panic when both hold the same uncomparable type` | Neither error is `nil`, an error made by `errors.New` or `fmt.Errorf`, or an error variable that holds one or holds a pointer, integer, string, or boolean, or an array or struct of these. | Compare one of them with an error variable instead. See [Comparing errors](#comparing-errors). |
| `cannot verify F: errors.Is would run the Is and Unwrap methods of err, an error whose origin is not known` | `errors.Is` is asked about an error from a parameter, or from a trusted function whose contract does not vouch for it. | Compare it with an error variable using `==`. See [Asking errors.Is](#asking-errorsis). |
| `E is assigned at f.go:n, so it is not known to hold the error it was declared with`, or `x.E is assigned at f.go:n in package x` | The package of the error variable assigns it, or takes its address. | Remove the assignment, or pass the error as a parameter. |
| `x.E is changed at f.go:n in package p, which this package is built with` | A package in the build assigns the error variable, or one that went into it. | Remove the assignment. See [When a package-level error is known](#when-a-package-level-error-is-known). |
| `x is passed to F, which is trusted, and is an error whose origin is not known` (or `a value of type T, which is or holds an interface value`, or a function value, a channel, or an `unsafe.Pointer`) | The trusted function `F` could call code that `x` carries. | See [Arguments that carry code](#arguments-that-carry-code), and [Functions that keep what they are given](#functions-that-keep-what-they-are-given) for a function that keeps it. |
| `the trusted contract of F ... cannot be used: its keeps lists h ...` | The entry's `keeps` names no destination, a destination that cannot hold the code, or a parameter that `modifies` does not cover. The message says which. | See [What vego checks in an entry with keeps](#what-vego-checks-in-an-entry-with-keeps). |
| `cannot verify F: G keeps code it is given, and cannot be used as a value` | A trusted function with `keeps` is used as a function value or a method of an interface value. | Call it directly. |
| `... which F may not modify; it is memory that G returned, which its contract places within s, and F passed b as s; list b in a // @Modifies clause` | `F` writes a slice that a trusted function returned inside the memory of an argument, as `bytes.TrimSpace` and `bytes.Cut` do. | List the argument under `Modifies`. |
| `... which F may not modify; it is memory that G returned, and its contract does not say that this is new memory` | `F` writes through what a trusted function returned, such as `bufio.NewWriter`, which may return memory that existed when `F` was called. | Take the value as a parameter and list it under `Modifies`. See [Writing through a buffer](#writing-through-a-buffer). |
| `precondition of Printf may not hold: ready(l)` (or of `Scan`, `Write`, and the other methods of `log.Logger`, `bufio.Scanner`, `bufio.Reader`, and `bufio.Writer`) | The value is not known to be ready: made by its constructor, with an output or input that is not `nil`. | Make it with its constructor, add `ready(x)` to the `Requires`, or, in a loop, to the invariant. |
| `postcondition may not hold: P; the contents of t are not known to stay as initialised: the use at f.go:n lets a reference to them out` (or another message about something not proved, with the same note) | What is not proved may rest on what the package-level variable `t` refers to, which is ordinary memory because of that use. | See [What a variable refers to](#what-a-variable-refers-to). |
| `the trusted contract of F (f.yaml:n) cannot be used with E = T: in its ensures "...": ...; call FFunc instead, ... or write a loop` | A clause of the entry of a generic function has no meaning at this type argument, such as a comparison of structs or an order of strings. | Call what the message names instead. See [What a contract means at each type argument](#what-a-contract-means-at-each-type-argument). |
| `the trusted contract of F (f.yaml:n) cannot be used with E = T: ...; the entry has this defect at every type argument, so fix the entry` | The entry of a generic function has a defect that does not depend on the type argument, such as a name that is no parameter. | Fix the entry. |
| `F is called with E = T, which is or holds an error; a generic function cannot be called yet with a type argument that can hold code`, and similar | A type argument is one that a generic function cannot be called with. | See [Type arguments that cannot be passed](#type-arguments-that-cannot-be-passed). |
| `F is called with E = T, and F may run the method ..., which a value of that type reaches; ... asserts: {E: []}` | The entry of the generic function does not claim that it runs no method of its type argument. | If the function runs none, add the claim to its entry. See [Writing an entry for a generic function](#writing-an-entry-for-a-generic-function). |
| `the trusted contract of F cannot be true of this call` | The contract contradicts what is known at the call. | The entry is wrong, or it needs a `requires` clause. |
| `the trusted contract ... cannot be used` | The entry in the trust file is invalid. The message says why. | Fix the entry. Check the parameter names. |
| `..., in the function literal called at f.go:n:c`, or `..., in the function literal deferred at f.go:n:c and run at the return at f.go:n:c` (or `at the end of the function at`, or `at the end of the function literal at`) | The problem is in the body of a function literal, at the call named at the end. For a deferred literal, the message names the `defer` statement and where the literal runs. | Fix the body, or what holds at that call. See [Function literals](#function-literals). |
| `cannot verify F: the function literal is used as a value of type T, which has no contract` | The literal is passed, returned, or stored as a value of a function type that has no contract. | Declare a named function type with a contract and use it there. |
| `the function value f may be nil` | A call through `f` is not proved to have a value to call. | Add `f != nil` to the `Requires` clauses, or check `f` before the call. |
| `cannot verify F: f has type T, which has no contract` | `f` is called, and its type has no contract. | Declare a named function type with a contract and use it for `f`. See [Function values](#function-values). |
| `cannot verify F: x is used as a value of type T, which has no contract` | A function, method value, or literal is given a function type that has no contract. | Give it a named function type with a contract. |
| `cannot verify F: converting x to T is not supported` | A function value of another type is converted to a function type. | Make the value of the type it is used as, from a function, a method value, or a literal. |
| `..., in g used as a value of type T at f.go:n:c`, or `..., in the function literal used as a value of type T at f.go:n:c` | The function, method value, or literal does not meet the contract of `T` where it is made into a value of `T`. | Fix the function or the literal, or the contract of `T`. See [Making a function value](#making-a-function-value). |
| `..., in the function literal run by G at f.go:n:c`, or `..., in g run by G at f.go:n:c` | The problem is in a run of a function handed to the trusted function `G`. | Fix the function, or what holds at the call. See [Functions that a trusted function calls](#functions-that-a-trusted-function-calls). |
| `x is assigned, which G may write itself while it runs the function it is handed` | A function handed to `G` writes memory that the `modifies` of `G` covers. | Write other memory, or make the write outside the function handed over. |
| `the function literal run by G is not proved to return the same result whenever it is called with the same argument` | The contract of `G` speaks of what the function returns, and its result may depend on something other than its argument. | Make the result depend only on the argument and on memory that nothing writes during the call. |
| `cannot verify F: x is passed to G as f, which G calls, and its type T has no contract` | Only a literal, a function, a method value, or a value of a type with a contract can be handed to `G`. | Hand over one of those. |
| `cannot verify F: the function literal is handed to G as f, which its trusted contract lists under runs with no contract under calls` | The entry of `G` does not say how `G` calls `f`. | Give `f` a contract under `calls` in the entry. |
| `cannot verify F: G calls a function it is given, and cannot be used as a value` | A trusted function with a contract under `calls` is used as a function value. | Call it directly. |
| `the Ensures clauses of T are not proved to be satisfiable for every call that its Requires allow` | Some call that the `Requires` of `T` allow has no result that meets its `Ensures`. | Add the condition to the `Requires` clauses, or weaken the `Ensures`. |
| `cannot verify F: a function literal used as a value cannot assign x` | The literal assigns a variable of the function around it. | Return the value from the literal, or write it into memory that the contract of the type lists. |
| `... calls through the function value f, and code that a function value runs cannot do that yet`, or `g may call through a function value or an interface value, and code that a function value runs cannot do that yet` (or `that an interface value runs`) | Code that a function value or an interface value runs would call through a function value or an interface value. The message ends with the call or the trusted function under `runs` that is the reason. | Leave that code unverified, or keep that call out of it. See [Function values that call function values](#function-values-that-call-function-values), [Interface values that call interface values](#interface-values-that-call-interface-values), and [Arguments that carry code](#arguments-that-carry-code). |
| `cannot verify F: x is passed to the function value f and is an error whose origin is not known` (or `to the method s.M`) | The value may come from code that is not verified, which could run the methods of the error. | Pass an error made by `errors.New` or `fmt.Errorf`, or call from code that is not verified. |
| `the interface value p may be nil` | A call through `p` is not proved to have a value to call. | Add `p != nil` to the `Requires` clauses, or check `p` before the call. |
| `cannot verify F: p.M calls I.M, which has no contract` | The method has no contract, in source or in the trust file. | Write the contract in the doc comment of the method where `I` is declared, give a method of another module an entry, or make the call in code that is not verified. See [Interfaces](#interfaces) and [Interfaces and function types of other packages](#interfaces-and-function-types-of-other-packages). |
| `..., in (*T).M used as a method of I at f.go:n:c` | The method of `T` does not meet the contract of `I.M` where a `T` is converted to `I`. | Fix the method, or the contract of `I.M`. See [What a conversion checks](#what-a-conversion-checks). |
| `... which I.M may not modify; I.M can list only what its parameters refer to, so a method that writes what its receiver refers to cannot be used as a method of I yet` (or `the contract of T ... as a value of type T`) | The method writes behind its receiver, which the contract it is made into cannot name. | Keep the conversion, or the method value, in code that is not verified. |
| `... which I.M may not modify; it is not part of the footprint of *T, which is the struct t points to` | The method writes memory outside its own struct, such as what a field points to, and `I.M` writes behind its receiver. | Keep what the method writes in its struct, or keep the conversion in code that is not verified. See [Converting a value of your own type](#converting-a-value-of-your-own-type). |
| `x.M may modify the footprint of x, ...; it is the memory that t points to, converted at f.go:n:c; list t in a // @Modifies clause` | A value of your own type was converted to an interface whose methods write behind their receiver, and the function does not list it. | Add `t` to `Modifies`. |
| `x.M may modify the footprint of x, ...; x holds a value converted at f.go:n:c in a loop, ...` | The value was converted in a loop and called after it, and nothing is known of its footprint after the head of the loop. | Convert the value before the loop or after it. |
| `converting a value of type *bufio.Writer to io.Writer is not supported yet: its Write calls through the writer it keeps, ...` | A `*bufio.Writer` was passed where an `io.Writer` is wanted, as to `fmt.Fprintf`. | Format into a string with `fmt.Sprintf` and pass it to the Writer's own `Write` as `[]byte(s)`. See [Writing through a buffer](#writing-through-a-buffer). |
| <code>precondition of WriteString may not hold: 2 * (&#124;b&#124; + &#124;s&#124;) + 65536 <= MaxAlloc; it holds when ...</code> | The buffer may grow past what can be allocated. | Bound the length of the buffer and of what is written, as the message says. See [Building text in a buffer](#building-text-in-a-buffer). |
| `cap(b): b is a strings.Builder, whose capacity no contract speaks of; ...` | A formula names the capacity of a buffer. | Bound its length, <code>&#124;b&#124;</code>, instead. |
| `it calls (*bytes.Buffer).ReadFrom, which has no shipped entry: ...` | `ReadFrom` calls through the reader it is given and asserts it to other types. | Read with `Read` in a loop and write what it returns with `Write`. |
| `converting a value of type *bytes.Buffer to io.Writer is not supported: ...` | The `Write` of a buffer needs a bound that the contract of `(io.Writer).Write` does not give. | Pass the buffer itself to `fmt.Fprintf`, `fmt.Fprint`, or `fmt.Fprintln`, or write with its own `WriteString`. See [Formatting into a buffer](#formatting-into-a-buffer). |
| `Fprintf writes to b text whose length is not known: ...` | What is formatted has a part whose length the bound on formatting does not count, and the buffer's `Write` needs a bound. | Format only values whose length the bound counts, or write to a `*bufio.Writer`. |
| `converting a value of type *T to I is not supported yet: *T owns an interface value through p.out, ...` | `T` owns, through an owned pointer, a struct that owns an interface value, and the methods of `I` write behind their receiver. | Own the interface value in `T` itself, or call the methods of `*T` on the pointer. |
| `... list bs[0] in a // @Modifies clause, which covers what it owns; ...` | A clause lists a slice of buffers, which does not cover the arrays its elements own. | List the element. |
| `T.M has a value receiver, and the pointer that the interface value holds may be nil` | A `*T` that may be nil is converted to an interface, and `M` copies what it points to. | Convert a pointer that is not nil. |
| `cannot verify F: comparing interface values is not supported yet` | Two interface values, or an interface value and a value of another type, are compared. | Compare with `nil` only. |
| `cannot verify F: type assertions and type switches are not supported yet` | The type that an interface value holds is not known. | Make the assertion in code that is not verified. |
| `cannot verify F: converting x, a J, to I is not supported: I has M from I.M, and J has M from J.M` | `I` has a method from a declaration that `J` does not have. | Make `I` embed the interface that declares the method. See [Converting between interfaces](#converting-between-interfaces). |
| `the contract of B.M is not part of this interface` | The interface gets a method of one name from two declarations, and Go keeps the other one. | Declare the method once, with its contract. |
| `a contract can only be declared on a method of a defined interface type at package level without type parameters` | The contract is on a method of an interface type written in place, of an alias, or of a generic type. | Declare a named interface type at package level. |
| `... has unsupported type interface{p.A}; an interface literal that embeds a declared interface ...` | An interface type written in place embeds a named interface. | Declare a named type, as in `type D interface{ A }`. |
| `cannot verify F: w is used as a method of I, which hands its receiver to M at each call; M is trusted, and its receiver ...` (or `as a value`) | A trusted method whose receiver can carry code is made into a method of an interface value or a function value. | List the receiver under `runs`, if the contract holds whatever that code does. See [Arguments that carry code](#arguments-that-carry-code). |
| `the trusted contract names (p.J).M, but J has M from (p.I).M; key the entry (p.I).M` | The entry is keyed by an interface that embeds the declaration, an alias, or a type defined from it. | Use the key the message gives. |
| `the trusted contract names (p.I).M, a method of an interface type of the module of this package` (or `a function type of the module`) | The trust file has an entry for a type that you can annotate. | Write the contract in the doc comment where the type is declared. |
| `... which I.M may not modify; the entry (p.I).M in the trust file does not list it, so code that writes it cannot be used there` (or `the contract of T does not list it`) | A value that verified code makes writes memory that the contract of its type does not list. | Write nothing that the contract does not list. |
| `g may return an error whose origin is not known in err, and the trusted contract of K vouches for the errors there` | A value that verified code makes could return an error that the entry of its type is claimed to vouch for. | Return only errors made by `errors.New` or error variables that hold them. |
| `its modifies "x" covers memory that can hold a function value or an interface value of a type with a contract; list x under vouches` | A trusted function writes memory that can hold such a value. | List the parameter under `vouches` if you can claim what that says. See [Function values and interface values that a trusted function returns](#function-values-and-interface-values-that-a-trusted-function-returns). |
| `the trust files of this build give K two contracts` (or `a contract at F, and the proofs of package P were made with none`) | Modules built together give one type different entries. | Make the entries the same, or run `laas` with `-vego.trusted`. See [One entry for each type in a build](#one-entry-for-each-type-in-a-build). |
| `cannot verify F: Go converts a value to an interface type here, and which expression it converts could not be told` | A value without an expression of its own, such as one result of a call with several, is converted to an interface. | Assign the value to a variable of its own type first. |
| `cannot verify F: f holds a function literal and is used here other than by calling it` | The variable that holds the literal is passed, compared, or assigned again. | Only call the variable. |
| `precondition of c.Close may not hold: ~closed(c)` | The value may have been closed already, by an earlier `Close` or by the caller. | Add `~closed(c)` to the `Requires` clauses, and close each value once. See [States of interface values](#states-of-interface-values). |
| `the interface values passed to F as a and b may share their states` | `F` lists one of the two in `Modifies`, and they may be one value or hold one value. | Pass two interface parameters of your own function whose contract lists one of them, or a value that a call created with `fresh`. |
| `... covers the states of what the interface value p.f holds, not the place that holds it; to assign it, list the struct that holds it` | `Modifies p.f` for an interface field does not cover the field. | List `p` in `Modifies`. |
| `x has type T, which has no states` | A formula or a `Modifies` entry speaks of a state of an interface value whose type has none. | Name a state that the type has, or declare one. A `Modifies` entry for an interface value without states covers nothing; to assign it, list what holds it. |
| `cannot verify F: converting a value of type T to I is not supported yet: I has the state ...` | A contract of `I` speaks of a state, which nothing ties to the methods of `T`. | Make the conversion in code that is not verified. See [Making a value of an interface with a state](#making-a-value-of-an-interface-with-a-state). |
| `the Ensures clause "P" names no result and nothing on return, so it speaks of the state when F is called` | The clause reads memory that `F` may modify as it was at the call. | Add the prime for the value on return, or move the clause to a `Requires`. See [Before and after](#before-and-after). |
| `a state can be declared only on a defined interface type that declares a method of its own`, `I.M names its receiver r, but I has no states` | A `State` or `Receiver` annotation is where it has no effect. | Declare the state on the interface that declares the methods whose contracts speak of it. |
| `r names the receiver, which a contract can use only as the argument of a state, as in open(r), and in Modifies` | The contract of a method uses its receiver in another way, as in `r != nil`. | Speak of the receiver only through its states. It is never nil at a call. |
| `the trust files of this build declare the states of I differently` (or `declare states of I at F, and the proofs of package P were made with none`) | Modules built together disagree about the states of one interface. | Make the declarations the same, or run `laas` with `-vego.trusted`. |
| `precondition of Lock may not hold: ~held(m)`, or `precondition of Unlock may not hold: held(m)` | The goroutine may already hold the mutex it locks, or may not hold the one it unlocks. | Add `~held(a.mu)` to the `Requires` clauses, and unlock on every path, as with `defer a.mu.Unlock()`. See [Locks](#locks). |
| `cannot verify F: x copies a value of type T, which holds a sync.Mutex`, and the other messages that end in `must not be copied after first use` | Go copies or overwrites a value that holds a mutex here. | Do what the message says: use a pointer, give the method a pointer receiver, or build the slice with its final length. See [Values that hold a mutex cannot be copied or overwritten](#values-that-hold-a-mutex-cannot-be-copied-or-overwritten). |
| `cannot verify F: x copies a value of type T, which owns memory` | Go copies or overwrites a value that owns memory, such as a `bytes.Buffer`, here. | Use a pointer to it, as described in [Writing through a buffer](#writing-through-a-buffer). |
| `cannot verify F: g may modify x, a T, which owns memory, and only a contract that comes with vego or a verified function says how what such a value owns may change` | A function that your trust file trusts writes a value that owns memory, such as a `*bufio.Writer`. | Verify the function, or write the value only through its shipped methods. |
| `... is an unexported field of T, declared in package p, and a formula in package q cannot name it` | A contract names a private field of another package. | Name an exported field, or the state of a mutex with `held`. See [Names](#names). |
| `cannot verify F: recover is not supported` | `recover` returns an interface. | Call `recover` in a function that is not verified. |
| `cannot verify F: a formula built to verify it has grown beyond 1048576 nodes, which is the limit` | An expression or a run of statements builds a formula that grows faster than the code, as `x = x + x` does when repeated. | Split the function, or the expressions in it, into smaller ones. |
| `analysis skipped due to errors in package` | The package does not compile, or the toolchain does not match. | See [Running it](#running-it). |
| `the answer cache entry ... is damaged: ...; to empty the cache, remove DIR` | An entry in the `-vego.cache` directory is not whole, or is for another question. The package fails, and so does every package verified after it. | Remove the directory. See [Keeping answers between runs](#keeping-answers-between-runs). |
| `Z3 answers a problem otherwise than the answer cache entry ... says`, `Z3 answered one problem in two ways`, or `a Z3 process of this run runs other files than the first one did` | An answer kept in the `-vego.cache` directory is not the answer Z3 gives, or Z3 changed during the run. The package fails, and so does every package verified after it. | Remove the directory, and check that only one Z3 5.4.1 is installed. |
| `the answer cache DIR is inside ..., which holds go.mod`, and similar | The `-vego.cache` directory is in a module or a repository. | Use a directory outside every module and repository, such as `$HOME/.cache/vego`. |
| `DIR is not empty and is not an answer cache; give -vego.cache a new or empty directory` | The `-vego.cache` directory holds files and was not made by `-vego.cache`. | Give a new or empty directory, such as `$HOME/.cache/vego`. |
| `the answer cache needs the Z3 binary itself, and P runs Q` | `-vego.z3` names a script or a link to another program, and `-vego.cache` is set. | Name the Z3 binary with `-vego.z3`, or run without `-vego.cache`. |
| `internal error of vego: ...; run again with -vego.speculate=false, and report it at https://github.com/spachava753/laas/issues` | `vego` found a defect in itself while it asked Z3, such as a question handed to a Z3 process that had been stopped. The package fails, and so does every later package of the run. | Run again with `-vego.speculate=false`, and report the message. |

## What is not supported

`vego` supports functions and methods over these types: the integer types, `bool`, `string`, `error`, the float types, structs, pointers to structs, slices, maps with integer, string, or boolean keys, function types, and interface types. In the body it supports assignments, `if`, `switch`, `for` and `range` loops with `break` and `continue`, `return`, `defer`, calls to named functions and methods, function literals that are called or deferred where they are written or bound to a variable that is only called, function values of named function types with a contract (see [Function values](#function-values)), calls through interface values of methods with a contract (see [Interfaces](#interfaces)), functions handed to a trusted function that calls them while it runs (see [Functions that a trusted function calls](#functions-that-a-trusted-function-calls)), and recursion. The built-ins `len`, `cap`, `min`, `max`, `new`, `make`, `append`, and `delete` are supported, and so are composite literals, slicing, and the arithmetic, comparison, shift, and bitwise operators.

A function that uses any of the following is reported as `cannot verify`:

- calls of a method of an interface that has no contract, in source or in the trust file, and converting a value to an interface with such a method (see [Interfaces](#interfaces)); of the standard library, only `(io.Writer).Write`, `(io.Reader).Read`, `(io.Closer).Close`, and `(context.Context).Err` have shipped contracts (see [Interfaces and function types of other packages](#interfaces-and-function-types-of-other-packages));
- converting a value of a type that is not an interface to an interface whose contracts speak of a state, such as a closer of your own to `io.Closer` (see [Making a value of an interface with a state](#making-a-value-of-an-interface-with-a-state));
- an entry in the trust file for a type of the module of the analysed package, or one with `runs`, `keeps`, or `calls`;
- calling a method of `bytes.Buffer` or `strings.Builder` that has no shipped contract, such as `Read`, `Next`, `ReadFrom`, `WriteTo`, or `Cap`, and converting either to `io.Writer`, since its `Write` needs a bound that the contract of `(io.Writer).Write` does not give; passing one to `fmt.Fprintf`, `fmt.Fprint`, or `fmt.Fprintln` is supported (see [Building text in a buffer](#building-text-in-a-buffer) and [Formatting into a buffer](#formatting-into-a-buffer));
- formatting into a `bytes.Buffer` or a `strings.Builder` a part whose length the bound on formatting does not count, such as the text of an error, or what a `String` method returns even when its contract bounds it;
- converting a `*bufio.Writer` or a `*bufio.Reader` to an interface, since their methods call through the writer or the reader they keep (see [Writing through a buffer](#writing-through-a-buffer)), and converting a value of another shipped type that owns memory, such as a `*log.Logger`, to an interface whose methods write behind their receiver;
- in a struct that owns memory (see [Structs that own memory](#structs-that-own-memory)): an exported owned field, a struct type with type parameters, and a struct that owns itself through its fields; storing into an owned field memory that something else refers to, a value it is handed, or what another field or another owner owns, so that moving owned memory from one owner or field to another is refused; returning what a local owner owns while something else refers to the owner, or a struct value that holds what an owner owns; handing what an owner owns to a method of an interface declared in source, which may keep what it is handed; converting an owner that owns an interface value through an owned pointer, or one that owns an interface value to an interface whose method is handed memory, such as `io.Writer`; and storing an owner into its own owned field;
- `io.MultiReader` and `io.MultiWriter` handed a slice whole, as in `io.MultiReader(rs...)`, when what they return is read or written (see [Wrappers in package io](#wrappers-in-package-io));
- `context.WithCancel` and the functions like it, which keep the context they are given and run it on other goroutines (see [Types without a shipped entry](#types-without-a-shipped-entry));
- a function that keeps code it is given anywhere but in a result or in memory that a parameter reaches, such as a registry, a goroutine, or a timer, which has no true entry; making a trusted function with `keeps` into a value; and handing a function literal, a function, or a method value of a type without a contract to a parameter under `keeps` (see [Functions that keep what they are given](#functions-that-keep-what-they-are-given));
- comparing interface values in code with anything but `nil`, type assertions, and type switches;
- a cycle of calls that goes through a call through an interface value or a function value, or through code of another package (see [Cycles through function values and interface methods](#cycles-through-function-values-and-interface-methods)), reported as `this call may not end`;
- converting an interface value to an interface whose methods it does not have from the same declarations, other than `any`;
- interface types written in place that embed a named interface, generic interface types, and interfaces that embed `error`;
- calls of methods promoted from an embedded interface field, method expressions such as `I.M`, and method values of interface methods;
- calls of function values whose type has no contract, and making a function value of such a type from a function, a method, or a literal (see [A function type without a contract](#a-function-type-without-a-contract));
- converting a function value to another function type, and method expressions such as `T.M`;
- a function literal used as a value that assigns a variable it captures (see [Function literals as values](#function-literals-as-values));
- code that a function value or an interface value made by verified code runs and that calls through a function value or an interface value (see [Function values that call function values](#function-values-that-call-function-values) and [Interface values that call interface values](#interface-values-that-call-interface-values));
- a contract on a function type whose `Ensures` only a change of the elements of a slice or a map, of an entry of a map, or memory that the call creates, can meet;
- maps whose keys are pointers, structs, floats, or interface values, and arrays as keys;
- passing an error of unknown origin, or a value that can hold a function value of a type without a contract, an `any`, or an interface value with a method that has no contract, to a function value or to a method of an interface value;
- handing a trusted function anything but a function literal written there, a function, a method value, or a value of a type with a contract, for a parameter with a contract under `calls`; a variable that holds a literal cannot be handed over;
- deferring a call that hands over a function, and using a trusted function with a contract under `calls` as a value;
- applying a function parameter in a trusted contract unless it has one integer parameter and one integer or boolean result, and a contract under `calls` for a function that is given or returns an error, an interface, or a function;
- copying or assigning a value that holds a `sync.Mutex`, a `sync.RWMutex`, or a `sync.Once`, parameters, results, and receivers of such a type, a method with a value receiver of such a type, `append` to a slice of them, and `range` variables and loop variables of such a type (see [Values that hold a mutex cannot be copied or overwritten](#values-that-hold-a-mutex-cannot-be-copied-or-overwritten));
- `recover`;
- generic functions and types of your own package with annotations, a call of a generic function without a trusted contract, a generic function used as a value, methods of generic types, and type arguments that can hold code, that are not modelled, or that hold a `sync.Mutex`, a `sync.RWMutex`, or a `sync.Once` (see [Generic functions of other packages](#generic-functions-of-other-packages));
- goroutines, channels, and `select`;
- arrays, and structs that contain an array;
- pointers to anything other than a struct;
- reading a package-level variable that something in the build changes, or whose type can hold a function value, an interface value, an error, a channel, or an `unsafe.Pointer`; assigning a package-level variable, writing what one refers to, and naming one in `Modifies` (see [Package-level variables](#package-level-variables));
- `copy`;
- annotations on a type declared inside a function body, such as an invariant on a local struct or a contract on a local interface;
- formatting a value whose type has a method `Format`, `GoString`, `Error`, or `String`, a pointer, a map, an interface value other than an error of known origin, a function value, or a value of a type that holds itself, with `fmt.Errorf` or a function whose entry lists it under `formats`, and passing such a function a slice with `...` for the values it formats (see [What can be formatted](#what-can-be-formatted));
- a logger in a package-level variable, and `log.Default()`;
- a call in the target of an assignment whose right-hand side is an `append` that may write into the array of its slice, unless the call modifies nothing and refers to no memory or a call among the operands of the `append` orders it (see [An append beside a call](#an-append-beside-a-call));
- a call with several results as the arguments of another call, as in `g(f())`;
- comparing structs with `==`;
- comparing two errors with `==` when neither is `nil`, an error made by `errors.New` or `fmt.Errorf`, an error that a trusted contract vouches for, or an error variable that holds one or holds a pointer, integer, string, or boolean, or an array or struct of these (see [Comparing errors](#comparing-errors));
- `errors.As`, `errors.Join`, `errors.Unwrap`, and `errors.Is` on an error whose origin is not known (see [Asking errors.Is](#asking-errorsis));
- `goto`, `fallthrough`, labelled `break` and `continue`, and `defer` inside a loop, except inside a function literal that the loop calls.

Some limits are reported in other ways. A write through what `bufio.NewReader` or `bufio.NewWriter` returns, in a function that does not list the reader or the writer it was made over, is reported as `Write may modify bw, which F may not modify; it is memory that NewWriter returned, which its contract places in the footprint of w when it is not new; list w in a // @Modifies clause`. List it, as described in [Writing through a buffer](#writing-through-a-buffer). A state can be declared only for an interface, and only as a boolean. A `State` annotation on a struct type is reported at the annotation as `a state can be declared only on a defined interface type that declares a method of its own`, and a state of a struct type in your trust file is reported in the file. A mutex or a `sync.Once` that exists when a trusted function is called cannot be used in a function literal that it calls, and its `Lock` or `Do` is reported as a precondition that may not hold, as described in [Locking in a function that a trusted function calls](#locking-in-a-function-that-a-trusted-function-calls). A formula that names an unexported field of a struct of another package is reported at the annotation, as described in [Names](#names). A method of a type that writes what its receiver points to, or relies on what it points to, cannot be used as a method of an interface. The conversion reports the obligation that fails, as described in [What a conversion checks](#what-a-conversion-checks). An entry in the trust file for a type of the module that you verify is reported in the trust file, as described in [Limits of trusted contracts](#limits-of-trusted-contracts). Two different entries for one type in packages built together are reported in every package built with both, as described in [One entry for each type in a build](#one-entry-for-each-type-in-a-build).

Some true contracts are not proved at the default limit. A function that writes one field through twenty-four or more different pointers has postconditions that are reported as not proved, with the note about the resource limit (see [Helping the prover](#helping-the-prover)).

Floating-point values are supported but opaque. They can be passed around and used in arithmetic, but nothing can be stated or proved about their values. An integer converted from a float can have any value of its type, so check its range in code before you use it as an index.

## What a proof assumes

A proof by `vego` depends on the following assumptions. Each concerns something `vego` cannot see.

- Trusted contracts are true. This applies to the shipped contracts and to your own. A trusted function returns without panicking when its `requires` clauses hold. It writes nothing a caller can see outside its `modifies` list, which includes package-level variables and the memory they refer to, and changes no state of an interface value outside it, also of one that it type-asserts from another interface or an `any`. It does not keep the pointers and slices it receives. For a parameter listed under `runs`, it runs the code the parameter carries only before it returns and only on the goroutine that called it, and holds no value that can hold code anywhere it was not held when the call began, unless `keeps` lists the parameter. For a parameter listed under `keeps`, it runs the code during the call only if `runs` lists the parameter too, holds it when it returns only in memory that the results and parameters listed there reach, and has started or registered nothing that runs it later: no goroutine, timer, finalizer or cleanup, callback given to another package, or package-level variable. For a parameter listed under `prints`, the function formats as the function that `prints` names does, calls the `Write` of that parameter once with exactly what that function returns, calls nothing else of it, and returns what `Write` returned. For a parameter listed under `runs` or `keeps`, all of this holds whatever value is passed. For a function value of a type with a contract, it holds for every value that meets the contract, and the function calls the value only with arguments that meet the `Requires` of its type. For an interface value whose methods all have contracts, it holds for every value whose methods meet them. For an interface value with a method that has a contract, the function calls such a method only with arguments that meet its `Requires`. For any other code, which includes every method of an interface value with a method that has no contract, it holds whatever code runs. For the parameters listed under `formats`, it does nothing with the values but format them as package `fmt` does, using the listed string only as the format, runs no method of them but those `fmt` runs, only while the call lasts and on the goroutine that called it, keeps none of them, and builds from them at most 4096 bytes more than `fmt` prints for them, apart from what a logger adds from its own settings. For a parameter with a contract under `calls`, it calls the function only with arguments that meet its `requires`, and the contract holds for every function that meets them, returns, and writes nothing its `modifies` covers. With `deterministic: true`, or an application such as `f(i)`, it needs to hold only for a function that returns the same result whenever it is called with the same argument, and `f(i)` is that result. For a result listed under `vouches`, the errors it returns meet the conditions in [Errors that a trusted function returns](#errors-that-a-trusted-function-returns), and the function values and interface values it returns meet the contracts of their types, including what those contracts say they write. For a parameter listed under `vouches`, so do the function values and interface values that the function writes into, or leaves in, the memory its `modifies` covers under that parameter. Where such a value runs what the function keeps, as the reader that `io.TeeReader` returns runs the reader and the writer it is given, it meets its contract whenever what the function keeps meets theirs.
- The methods of `bytes.Buffer`, `strings.Builder`, `bufio.Writer`, `bufio.Reader`, `bufio.Scanner`, and `log.Logger` that have shipped entries write nothing that verified code can see other than the struct and the memory that the value owns, as [Writing through a buffer](#writing-through-a-buffer) lists it. After a call, the value owns only what it owned before the call and memory that the call made. The read position of a `bytes.Buffer` never passes the end of what was written to it. Every method of `bytes.Buffer` keeps it so, and `|b|` is the number of bytes between the two.
- Code of another package runs code of the verified package only as `vego` follows it, which [Cycles through function values and interface methods](#cycles-through-function-values-and-interface-methods) describes: during a call that the verified package makes, it runs only what that call hands it, through the arguments and the receiver. Code that it kept from an earlier call, a value it stored, or code that it runs on another goroutine or at another time, does not call back into a verified function while that function runs, so that the call never ends. A cycle that stays in the package, or that goes through what a call hands to another package, is found and reported.
- A claim under `asserts` is true: the function calls nothing that the parameter holds, or that a call of what the parameter holds returns, but what the claim allows, and uses no reflection on it (see [What a function finds on what it is handed](#what-a-function-finds-on-what-it-is-handed)). For a type parameter of a generic function, the function runs no method of a value of the type parameter's type, or of a pointer to one, or of anything such a value holds, directly or through what it calls, `fmt` and `reflect` included, neither while the call lasts nor later through anything it returns, keeps, or registers (see [Writing an entry for a generic function](#writing-an-entry-for-a-generic-function)). Each shipped entry of a generic function makes this claim, read from the source of its package.
- Unverified callers respect the contract. They satisfy the `Requires` clauses, pass structs whose invariants hold, and do not pass overlapping slices for two slice parameters of the same element type. For a parameter whose footprint the contract lists in `Modifies`, they pass no other argument that reaches memory in that footprint without going through an interface value: `Log` relies on the `Lines` that `t` points to not being memory that the methods of `r` write. For two interface parameters with states of which the contract lists one in `Modifies`, they do not pass one value twice, two values that hold one value, or a value and one that wraps it, unless one of them is nil. They call a function value that verified code made only with arguments that meet the `Requires` of its type, and a method of an interface value that verified code made only with arguments that meet the `Requires` of the method. For a parameter whose type owns memory (see [Structs that own memory](#structs-that-own-memory)), they pass a struct whose owned memory is reached by nothing else they pass: not by the other arguments, not by the struct's other fields, and not by what its other owned fields refer to. Memory that a method returns from what its struct owns, which its contract shows with `within(result, s)`, is not stored by code that is not verified, and is not passed to a verified function together with the struct it came from or with anything that reaches that struct.
- Code of a package that declares a struct that owns memory, where it is not verified, builds and changes such structs so that nothing else refers to the memory an owned field refers to, no two owned fields refer to the same memory, and an owned field comes to refer only to memory made since, or to part of what it referred to before.
- An interface value that reaches verified code from code that is not verified meets the contracts of its methods. That includes a value passed as an argument, a value in memory that an argument reaches, a value that a call through another value returns, and a value that a trusted function returns or writes, which its entry vouches for. Called with arguments that meet the `Requires` of a method, the method returns without panicking, leaves its `Ensures` true, and writes nothing that verified code can see outside what its `Modifies` lists. When the contract lists the receiver, that is the value's footprint, and the method adds to it only memory that it creates during the call. A method may keep a pointer it is handed, but no later call of the value's methods writes through it: a `Store` whose `Put(v *Value)` keeps `v` and whose `Touch()` then writes `*v` breaks this, and `vego` cannot see it. The same holds of a pointer that verified code stores into memory that the value's methods write or that the value handed out, as with `within(m, w)`: a `Sink` that hands out a table of pairs, and whose `Put` adds one to each pair in the table, breaks this. For a result that the contract of the method lists under `Vouches`, the errors it returns meet the conditions in [Errors that a trusted function returns](#errors-that-a-trusted-function-returns). This holds also when the value holds a pointer to a struct that verified code holds.
- The same holds of the methods and function types that entries of the trust file give contracts, which is what such an entry claims (see [What an entry for a type claims](#what-an-entry-for-a-type-claims)). In particular, a caller that is not verified does not pass a verified function such a value together with a pointer to memory that the value writes, as a `*bytes.Buffer` passed both as an `io.Writer` and as a `*bytes.Buffer` would be. Every call through such a value returns: a `Read` from a pipe, a terminal, or a connection returns only once data or an error arrives.
- Packages that are built together give each type at most one entry, and declare the same states for an interface. `vego` reports two entries for one type, or an entry against none, and two different declarations of the states of an interface, or a declaration against none, in every package that `laas` analyses and that is built with both. A program whose main package is never given to `laas` is not checked.
- A function value that reaches verified code from code that is not verified meets the contract of its type. That includes a value passed as an argument, a value in memory that an argument reaches, and a value made with `reflect.MakeFunc` or by generic code. Called with arguments that meet the `Requires` of its type, such a value returns without panicking, writes only what the `Modifies` of its type lists, and leaves its `Ensures` true. For a result that the contract of its type lists under `Vouches`, the errors it returns meet the conditions in [Errors that a trusted function returns](#errors-that-a-trusted-function-returns).
- Unverified code respects Go's type system. It does not use `unsafe`, `reflect`, or cgo to give one piece of memory two types or to change a string. It uses `unsafe.Pointer` only in the patterns that the documentation of package `unsafe` allows, so it turns a `uintptr` back into a pointer only where those patterns say. A `uintptr` that a function keeps or passes on and later converts back to a pointer, as in `lib.RunAt(uintptr(unsafe.Pointer(&hook)))` followed by a call through `*(*func())(unsafe.Pointer(a))`, breaks this: an integer carries no code, so `vego` does not follow the call, and `go vet` reports it as a possible misuse of `unsafe.Pointer`.
- A declaration of a state, shipped, in a trust file, or in source, is true of every value of the interface that verified code gets from code that is not verified. Every method whose contract does not list the receiver in `Modifies` leaves every state of the value unchanged. For the shipped state `closed` of `io.Closer`, this means that `Read` and `Write` on an `io.ReadCloser`, an `io.WriteCloser`, or an `io.ReadWriteCloser` never close the value, which the documentation does not say. A method declared on an interface with states, such as `Close`, changes the states of the value and writes nothing that verified code can see. A `gzip.Writer` over a `bytes.Buffer` that verified code holds breaks this, since its `Close` flushes into the buffer. Do not vouch in the trust file for a closer that writes memory on `Close`. Code that is not verified does not change a state of a value that verified code holds while a verified function runs, other than through calls that the function makes.
- No other goroutine writes memory that a verified function reads or writes while it runs, also while the function waits in `Lock`, `RLock`, or `Do`. The one exception is that other goroutines can lock and unlock a mutex that the goroutine running the function does not hold, and call `Do` on a `sync.Once` that this goroutine is not inside `Do` on, which writes that `Once`. What the function that another goroutine hands to `Do` writes is not part of the exception. Closing an interface value that the function uses counts as such a write. A proof covers one goroutine. A function that takes a lock is not proved to be safe to call from several goroutines. See [What a proof of a function that locks shows](#what-a-proof-of-a-function-that-locks-shows).
- Every call that waits for another goroutine returns: `Lock` and `RLock` return once the other goroutines release the mutex, and `(*sync.Once).Do` returns once the function that another goroutine runs in it returns. A deadlock that the verified function takes part in breaks this.
- No other goroutine unlocks a mutex that the goroutine running a verified function holds.
- Code that is not verified does not copy a value that holds a `sync.Mutex`, a `sync.RWMutex`, or a `sync.Once` after it was first used, as the documentation of `sync` requires, or a `strings.Builder` that is not zero, as the documentation of `strings` requires. A copy of a `Builder` that has been written panics at its next write.
- No code outside the packages that a verified package is built with changes a package-level variable that a proof relies on, or lets out a reference to what such a variable refers to when a proof relies on it being only read. No code does either through `unsafe`, `reflect`, C code of a cgo package, or an object file (`.syso`) linked into the program. `vego` reads the `//go:linkname` directives and the assembly files of the build, and counts what they name as changed. When a verified package is built with a package that makes such a change, the verified package does not rely on the variable. The change is also reported wherever it meets a proof that does rely on it.
- `errors.New`, `fmt.Errorf`, and `errors.Is` behave as they do in the Go releases that `laas` is tested with. Each call of `errors.New` or `fmt.Errorf` returns a new pointer. The errors they return have no `Is` method. `Unwrap` returns the operand of the one `%w`. `errors.Is` finds an error, or an error it wraps, that is the target. The tests of `vego` check this against the running toolchain.
- The compiler evaluates each statement in an order that the Go specification allows. Calls, `&&`, and `||` run from left to right, an operation runs after its operands, and an assignment assigns only after it has evaluated everything. Where the specification leaves the order open, `vego` proves that every order it allows gives the same values.
- The program runs on the platform `laas` was run for. The sizes of `int`, `uint`, and pointers, the layout of structs, and `MaxAlloc` are those of the `GOOS` and `GOARCH` that `laas` runs with. A proof for a 64-bit target does not hold for a 32-bit target.
- The program is built without `-ldflags "-X ..."` for a variable that a proof relies on. The linker sets a string variable that way, typically a version, to a value that `vego` does not see.
- The program is built from the files `laas` read. Files left out by a build constraint or a file name such as `_windows.go` are not read, so their annotations are not checked. Run `laas` once for each configuration you ship.
- A write to standard output or standard error returns. Code that is not verified may set `os.Stdout` and `os.Stderr` to any `*os.File`. A pipe that nobody reads breaks this, and so does a pipe whose reader has closed it, which ends the program with `SIGPIPE`.
- A call that opens, reads, or writes a file returns. This covers `os.Open`, `os.Create`, `os.WriteFile`, `os.MkdirAll`, `os.Getwd`, and `Read`, `Write`, and `Close` of an `*os.File`, also one that code that is not verified passes in. Opening a FIFO waits for its other end, reading a FIFO, a pipe, or a terminal waits for data, writing a pipe that nobody reads waits, and a file system that does not answer, such as a network mount that is gone, waits for ever. A write to standard output or standard error through a broken pipe ends the program, as above.
- The output of the standard logger writes nothing that verified code can see, and returns. Code that is not verified sets that output with `log.SetOutput`, or with `slog.SetDefault` to a `slog.Handler`. A program that sets it to a writer or a handler of its own makes this claim about that code. A writer or a handler that logs through the standard logger again never returns, because the logger holds a lock while it writes. The same goes for a writer made by verified code whose `Write` calls something that logs.
- The machine has enough memory and stack.
- The key and the value of every entry of a map take memory of their own in the heap, as Go's runtime keeps them, and the heap spans at most `MaxAlloc` bytes. `vego` uses this to bound the number of keys of a map by the size of a key and a value, as described in [How many keys a map can have](#how-many-keys-a-map-can-have). The Go specification does not say how a map is stored; the runtime of the Go releases that `laas` is tested with stores it this way, for keys and values of size zero and for large ones kept behind a pointer. Entries of different maps take memory of their own too, though `vego` bounds one map at a time.
- What formatting builds from parts whose length the logic has no term for is not longer than can be allocated. Those parts are:
  - the text of an error;
  - what a `String` or `Error` method returns;
  - the strings and slices held in the elements of a slice, such as the strings of a `[]string`, when the slice is formatted;
  - the name of a file that a logger's header shows, with `log.Lshortfile` or `log.Llongfile`;
  - the prefix of the standard logger, which code that is not verified sets with `log.SetPrefix`.

  `vego` proves the rest of the bound at each call of a function that formats and of `fmt.Errorf`, as described in [How long a formatted string can be](#how-long-a-formatted-string-can-be). On a 64-bit target, these parts would have to be terabytes long. On a 32-bit target, where one allocation can be at most about 4 GB, this can be reached.
- Z3 is correct. Every proof rests on Z3 5.4.1 answering correctly that a problem has no solution.
- With `-vego.cache`, nothing but `vego` writes the cache directory. An answer read from the directory is used as Z3's answer. `vego` checks that each entry is whole and is for the question asked, and solves a sample again on each run. An entry changed by someone who also fixes its hash cannot be told from an answer, in the same way that an edited Z3 binary cannot. Whoever can write the directory can make any proof that uses it succeed. See [Keeping answers between runs](#keeping-answers-between-runs).
- Your formulas say what you intend. `vego` does not check a formula for out-of-range indexes or division by zero, so a formula that contains one may mean something other than you expect. See [Formulas](#formulas).

## Summary

### Annotations

| Annotation | Where | Meaning |
| --- | --- | --- |
| `Requires P` | doc comment of a function, of a named function type, or of a method in a named interface type | `P` must be true when the function, a value of the type, or the method is called. |
| `Ensures P` | doc comment of a function, of a named function type, or of a method in a named interface type | `P` is true when the function, a value of the type, or the method returns. |
| `Modifies a, b.f` | doc comment of a function, of a named function type, or of a method in a named interface type | The memory the function, a value of the type, or the method may write that a caller can see. |
| `Variant e` | doc comment of a recursive function | `e` is never negative and is smaller at each recursive call. |
| `Invariant P` | directly above a loop | `P` is true each time the loop tests its condition. |
| `Variant e` | directly above a `for` loop | `e` is never negative and decreases on each iteration. |
| `Assert P` | in a function body | `P` must be true at this point and can be used afterwards. |
| `Snapshot n = e` | in a function body | `n` is the value `e` has at this point, in the annotations that follow in the block. |
| `Visited done` | directly above a `range` over a map | `done` is the set of keys the loop has passed before the current iteration, in the annotations of the loop and its body. |
| `Vouches err` | doc comment of a named function type, or of a method in a named interface type, beside its contract | The errors that values of the type return in `err` have a known origin; `vego` checks it of every value that verified code makes. |
| `Invariant P` | doc comment of a struct type | `P` is true for every parameter, receiver, and result of the type at function boundaries. |
| `Owns f, g` | doc comment of a struct type | A value of the type owns the memory its fields `f` and `g` refer to. |
| `Predicate name(x, y) ::= P` | top level | Names a formula over its parameters. |
| `State name` | doc comment of a named interface type that declares a method | Declares a state of the values of the interface. |
| `Receiver r` | doc comment of a method in a named interface type | Names the value the method is called on, so that its contract can speak of its states as `name(r)`, list it in `Modifies` when the method writes behind it, or place a result within it, as in `within(m, r)`. |

### Formulas

| Form | Meaning |
| --- | --- |
| `~P`, `P And Q`, `P Or Q` | not, and, or (in order of precedence, tightest first); Go's `!`, `&&`, and `\|\|` are reported |
| `P -> Q`, `P <-> Q` | implies, if and only if (lowest precedence) |
| `True`, `False` | the constants |
| `=`, `!=`, `<`, `<=`, `>`, `>=` | comparisons, which can be chained: `0 <= i < n`; Go's `==` is reported |
| `+`, `-`, `*`, `/`, `%` | arithmetic on mathematical integers; `/` and `%` round as in Go |
| `MaxInt`, `MinInt`, `MaxInt8` ... `MaxUint64` | limits of the Go integer types |
| `MaxAlloc` | the largest number of bytes in one allocation |
| <code>&#124;A&#124;</code> | length of a slice or string, or number of keys in a map |
| <code>&#124;b&#124;</code> | for a `strings.Builder` or a `bytes.Buffer`, or a pointer to one: what `b.Len()` returns, the bytes not yet read |
| `A[i]`, `m[k]`, `p.f` | element, map value, field |
| `A[lo:hi) <= x` | the comparison holds for every element from `lo` up to `hi` |
| `Forall k in [a, b) : P`, `Exists k in [a, b] : P` | quantifiers over an interval |
| `Forall k in Z : P` | quantifier over all integers |
| `Forall k in m : P`, `Exists k in m : P` | quantifiers over the keys a map has, or that a loop has visited |
| <code>&#124;done&#124;</code>, `has(done, k)` | for a `Visited` name: the number of places the loop has passed before the current iteration, which is the number of iterations unless it deletes keys it has not reached; whether it passed `k` before it |
| `"text"`, `nil` | a string; the nil pointer, error, function value, or interface value |
| `'/'`, `'\n'` | the number of a character, as in Go |
| `cap(A)` | the capacity of a slice |
| `elemsize(A)` | the number of bytes of an element of a slice; 0 for values of size zero |
| `A = nil`, `A != nil` | for a slice: whether it is nil, which <code>&#124;A&#124; = 0</code> is not |
| `&p.f`, `&s[i]` | the address of a struct reached through a pointer or an element of a slice; nil when that pointer is nil |
| `ErrEmpty`, `io.EOF` | an error variable of the package, or of an imported package |
| `limit`, `lib.Limit`, `table[i]` | in the contract of a verified function, a package-level variable that nothing changes, of the package or of an imported package |
| `"io/fs".ErrNotExist` | in a trusted contract, an error variable named by the path of its package |
| `err = ErrEmpty` | the two are the same error |
| `x = y` | for two interface values: the same value, one copied from the other; not Go's `==` |
| `is(err, target)` | `errors.Is(err, target)` reports true |
| `valid(x)`, `valid(s.store')`, `valid(old(s))` | the invariants of the struct `x` is or points to hold, with those of what it owns |
| `has(m, k)` | the map contains the key |
| `held(m)`, `held(a.mu')` | the goroutine that runs the function holds the `sync.Mutex` or `sync.RWMutex`; `m` is a mutex or a pointer to one |
| `rheld(rw)` | the goroutine holds a read lock on the `sync.RWMutex` |
| `running(o)` | the goroutine is inside a call of `Do` on the `sync.Once` |
| `closed(c)`, `closed(resp.Body')` | `Close` has been called on what the `io.Closer` `c` holds |
| `name(x)` | the state `name` of the interface value `x`, declared with a `State` annotation or in the trust file |
| `name(x, y)` | a predicate |
| `f(x)` | in the `ensures` of a trusted contract, what the function parameter `f` returns for `x` |

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
| `Modifies m[k]` | the entry of key `k`: whether the map has it, its value, and the number of keys; for a map of pointers, slices, maps, or interface values, what the value under `k` refers to |
| `Modifies g[from][to]` | the entry `to` of the map held under `from` |
| `Modifies rc`, `Modifies p.f` | if `rc` or `f` is an interface value: every state of what it holds and, when its methods write behind their receiver, its footprint, the memory they may write; not the variable or the field; a function value field is the field itself |
| `Modifies bw` | for a `*bufio.Writer`, `*bufio.Reader`, `*bufio.Scanner`, `*log.Logger`, `*bytes.Buffer`, or `*strings.Builder`: the struct and the memory it owns |
| `Modifies p`, `Modifies p.out`, `Modifies bs[0]` | for a pointer to a struct that holds a `strings.Builder` or a `bytes.Buffer` by value, a path to one, or an element of a slice of them: also the memory the buffer owns; `Modifies bs` does not cover what the elements own |
| `Modifies p` | for a pointer to a struct that declares `@Owns`: also what it owns, the array of an owned slice up to its capacity, an owned map, an owned struct with what it owns, and the footprint and states of an owned interface value |
| `fresh(x)` | in an `Ensures`, the memory `x` refers to on return was allocated by the call; in a body, it was allocated since the function was entered; true for a slice with zero capacity and a nil interface value, false for a nil pointer or map; for an interface value, what it holds was created then, its footprint included |
| `fresh(x, w)` | the same, except that what `x` refers to may also lie in the footprint of `w`, an interface value whose methods write behind it; more than one such value may follow, and `w` may be a variadic parameter of such values, read where a call writes each one out |
| `within(a, b)` | `a` lies inside the memory of `b`; each is a pointer or a slice, and a slice includes its capacity; for an interface value `b`, `a` (also a map) lies in its footprint, and for a value that owns memory, in its struct or in what it owns |
| `apart(a, b)` | the slices `a` and `b`, of one element type, share no memory up to their capacities |

### Order of evaluation

| In a statement | Order |
| --- | --- |
| calls, `&&`, and <code>&#124;&#124;</code> | from left to right |
| an operation | after its operands |
| the right operand of `&&` and <code>&#124;&#124;</code> | after the left one, and only when the left one does not decide the result |
| an assignment | assigns after every operand is evaluated |
| the arguments listed for a variadic parameter | like other arguments; the new slice that holds them is made after them |
| a call of a function literal | like a call, and it may change the variables that the literal assigns |
| a call through a function value or an interface value | like a call; the value is evaluated with the arguments, before the call |
| any other read of memory, or of a variable that a function literal assigns | not fixed; `vego` proves that every order gives the same value |
| `append` and other built-in functions | after their operands, and not ordered like calls |
| the entries of a map literal | not fixed; keys that are not both constants must be proved different |

### Flags

| Flag | Effect |
| --- | --- |
| `-vego` | run only the verifier |
| `-vego.audit` | also report contracts that trivial implementations satisfy |
| `-vego.rlimit=n` | Z3's resource limit for one proof obligation, 4000000 by default |
| `-vego.cost` | print what verifying each function asked of Z3, on standard error |
| `-vego.z3=path` | the Z3 5.4.1 binary to use, instead of the `z3` on `PATH` |
| `-vego.cache=dir` | keep the answers of Z3 in this directory between runs |
| `-vego.speculate=false` | do not verify functions ahead on idle Z3 processes, which saves memory |
| `-vego.trusted=path` | use this trust file instead of the one next to `go.mod` |
| `-vego.other-tags=A,B` | words that another tool reads after `// @`; any other unknown word there is an error |
| `-vego.trust` | print the trust report |
| `-test=false` | leave out test files |
| `-exclude-packages=regexp` | skip packages whose import path matches |
