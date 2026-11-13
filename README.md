# laas

`laas` is a home for linters, development helpers, and reusable agent skills that help coding agents write better, more idiomatic Go.

## Why laas?

*Laas* (Ancient Greek: λᾶας) means stone. The word evokes the enormous stones and boulders of Greek mythology: those thrown by heroes and the one Sisyphus was condemned to push uphill.

A Sisyphean task is grueling, uphill, and seemingly endless. Code quality can feel similar. Lint violations, structural details, and idiomatic conventions demand sustained attention, but coding agents are intelligent, tireless, and particularly good at hill climbing.

`laas` gives agents a boulder to push. By expressing Go code-quality expectations as tools and skills, the project aims to turn that persistence into consistently better code.

## Scope

The project will contain:

- Linters and checks for idiomatic Go and sound code structure.
- A deductive verifier that proves annotated functions correct.
- Helpers that make code-quality constraints easier for agents to apply.
- Agent skills that capture reusable guidance for writing and reviewing Go.

## Skills

### setup-laas-pre-commit

[`setup-laas-pre-commit`](skills/setup-laas-pre-commit/SKILL.md) teaches an agent to pin `laas` as a Go tool and integrate `go tool laas ./...` into a repository's existing pre-commit workflow. When no hook system exists, it creates a tracked `.githooks/pre-commit` hook without silently replacing local hooks.

Install the skill with a GitHub CLI version that supports Agent Skills:

```sh
gh skill install spachava753/laas setup-laas-pre-commit --scope user
```

Pass `--agent` when installing it for a specific agent.

## funcdoc

`funcdoc` reports a function or method when both of these conditions hold:

- Its cyclomatic complexity is greater than the configured limit, which defaults to 10.
- It does not have a doc comment immediately above its declaration whose first word exactly matches the function or method name and explains the implementation's plan.

The score follows [`gocyclo`](https://github.com/fzipp/gocyclo): every function starts at 1, then each `if`, `for`, `range`, non-default `case`, `&&`, and `||` adds 1. Following Go's documentation convention, a comment for `reconcile` must begin with `reconcile`. `funcdoc` reads the declaration's `Doc` field, the same association used by Go's parser and documentation tooling. A detached comment or a comment inside the function body does not satisfy the rule.

Files ending in `_test.go` are excluded by default.

Install and run the analyzer across a module:

```sh
go install github.com/spachava753/laas/cmd/laas@latest
laas ./...
```

Set a different limit with the analyzer-specific flag:

```sh
laas -funcdoc.limit=15 ./...
```

Include test files explicitly when they should be checked too:

```sh
laas -funcdoc.include-tests ./...
```

## teststructure

`teststructure` reports groups of standard `TestXxx(*testing.T)` functions whose names share a prefix at Go identifier-word boundaries. For example, `TestParseValidInput` and `TestParseInvalidInput` share `TestParse` and should be consolidated into one `TestParse` using either a table or `t.Run` subtests.

Name grouping does not inspect test bodies or attempt to recognize tables and subtests. Unique flat tests are allowed; only same-prefix groups produce a naming diagnostic. CamelCase, initialisms, digits, and underscores are recognized when comparing names. Benchmarks, fuzz targets, examples, test helpers, and `TestMain` are not grouped.

`teststructure` also requires every `testing.T.Run` callback to be an inline function literal. Passing a named function, method value, or function variable separates the subtest name from its implementation and produces a diagnostic:

```go
t.Run("valid input", func(t *testing.T) {
	// Test logic stays next to the scenario name.
})
```

This callback rule applies only to the real `testing.T.Run` method in `_test.go` files; unrelated methods named `Run` are ignored.

The analyzer runs as part of the standard command:

```sh
laas ./...
```

## inlinehelper

`inlinehelper` reports an unexported function or method when it has at most four statements and exactly one reference, which is also a direct call. The diagnostic recommends considering whether the helper should be folded into its only call site; it does not provide an autofix.

Statement count is based on the Go syntax tree rather than physical lines. Exported declarations are excluded because calls from other packages are not visible. Unused functions, recursive functions, function values, and helpers with multiple references are also excluded.

Change the size threshold with:

```sh
laas -inlinehelper.max-statements=3 ./...
```

## vego

`vego` is a deductive verifier for Go. You state what a function must do in `//@` comments, and `vego` proves that the code does it for every input, or tells you which obligation it could not prove. It implements the approach of the VeGo paper ([Masoudi and Dutchyn, arXiv:2608.22630](https://arxiv.org/abs/2608.22630)): specifications live in comments, so annotated files stay ordinary Go that builds, runs, and formats with the standard toolchain.

```go
// Divide computes quotient and remainder by repeated subtraction.
//
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

//@ Ensures n = d*q + r And 0 <= r And r < d
```

A function opts in by carrying at least one annotation; everything else is left alone. The analyzer runs as part of the standard command:

```sh
laas ./...
```

Change the loop condition above to `d < r` and the run fails with `vego: postcondition may not hold: r < d`.

### What is proved

For every annotated function, `vego` proves that from any state satisfying `Requires`:

- every `return` establishes each `Ensures` clause, and every `//@ Assert` holds;
- every loop invariant holds on entry and is preserved by the body;
- every loop terminates (its `Variant` is non-negative and decreases) and every recursive call decreases the `Measure`;
- no slice index is out of range, no nil pointer is followed, no divisor is zero, no `make` length is negative, and no `panic` is reachable;
- the function writes nothing a caller can see except what its `Modifies` clauses list. An entry that no write needs is reported; that is judged by a quick proof attempt for each write, and an entry counts as needed when the attempt is inconclusive;
- no integer arithmetic or conversion overflows. Go would wrap silently; verified code may not;
- every call goes to a function with a contract and satisfies its `Requires`. Callers then rely on the callee's `Ensures` and `Modifies` only, never on its body;
- a function that returns an error does not have a contract it could meet by failing every time.

There is no external solver. Proof obligations are generated by symbolic execution over single-assignment values and discharged by a deduction engine written in Go: case splitting, linear integer arithmetic by Fourier–Motzkin elimination, bounds on products obtained by multiplying known inequalities, read-over-write reasoning for slices and for memory, quantifier instantiation, and bounded unfolding of predicates. The engine is sound and deliberately incomplete: when it cannot prove a true fact, add an `//@ Assert` with an intermediate step or strengthen an invariant.

### Annotations

| Annotation | Where | Meaning |
| --- | --- | --- |
| `Requires P` | doc comment of a function | Precondition: callers must establish `P`. |
| `Ensures P` | doc comment, or a comment after the closing brace | Postcondition. A parameter, and anything reached from it, denotes the state on entry; a prime asks for the state on return, as in `A'` for the contents of slice `A` and `c.count'` for a field. Result names denote the returned values. An unnamed single result is called `result`; several are `result1`, `result2`, and so on. |
| `Modifies a, b` | doc comment of a function | What the function may write that a caller can see. Everything else is unchanged for the caller. |
| `Invariant P` | directly above a `for` loop | Holds before every evaluation of the loop condition. |
| `Invariant P` | doc comment of a struct type | Holds of every value of the type where it crosses a function boundary; see below. |
| `Variant e` | directly above a `for` loop | Integer that is non-negative while the loop runs and decreases every iteration. `range` loops need none. |
| `Measure e` | doc comment of a recursive function | Integer over the parameters that is non-negative and decreases at every recursive call, including mutual recursion. |
| `Assert P` | anywhere in a body | Must hold at that point; later proofs may use it. |
| `Predicate name(params) ::= P` | top level | A named, possibly recursive formula. Recursion must not pass through negation. |

Formulas use `And`, `Or`, `~`, `->`, `<->`, `True`, `False`, the comparisons `=`, `!=`, `<`, `<=`, `>`, `>=` (which chain, as in `0 <= i < |A|`), and integer arithmetic with Go's `/` and `%`. Integers in formulas are mathematical and never overflow; the limits of the Go types are available as `MaxInt`, `MinInt`, `MaxInt8` to `MaxInt64`, `MinInt8` to `MinInt64`, and `MaxUint` to `MaxUint64`. `MaxAlloc` is the largest number of bytes a single allocation can have on the platform, which is what limits the length of a string. `|A|` is the length of a slice or string and `A[i]` an element or byte. Strings compare with `=` and can be written as literals, as in `role = "admin"`. An error can be compared with `nil`, as in `err = nil -> value = A[i]`. Quantifiers range over the integers or an interval: `Forall k in [0, |A|) : A[k] >= 0`, `Exists t in Z : ...`. A slice range used as a comparison operand stands for all its elements: `A[0:i) <= A[i]`. Fields are selected with a dot, through pointers too: `c.count`, `s.items[i]`, `|s.items|`. A pointer can be compared with `nil` and with another pointer. Inside a body a name denotes the current value of the variable and `old(x)` what parameter `x`, or something reached from it such as `old(c.count)`, was on entry. Boolean variables are compared with constants as in the paper (`found = True`) or used directly. A `//` inside an annotation starts an ordinary comment, and a line that does not begin with a keyword continues the previous annotation. An annotation inside a body must stand between statements on a line of its own, and an unknown word after `@ ` is an error, so a misspelt keyword cannot silently switch a check off.

`gofmt` rewrites `//@` to `// @` inside doc comments; both spellings are accepted, with any amount of space before the `@`. Annotations are read from `//` comments only; one in a `/* */` comment is an error. A word after `@` and a space that is not a keyword is an error, and so is one directly after `@` that is a keyword but for its case or a letter or two, so a misspelt keyword cannot switch a check off; any other word directly after `@`, as in `// @Summary`, is taken to belong to another tool. A detached `Ensures` comment belongs to the function that ends just above it. A variable whose name means something else in an annotation that uses it and can see it is an error: `True`, `False`, and `nil` for any variable, and `result` for a parameter of a function with an unnamed result.

### Pointers, structs, and slices that share memory

Two pointers may refer to the same struct, and two slices to the same array. `vego` does not forbid that; it reasons about it. A proof has to hold whether or not two pointers are equal, unless the contract says they differ:

```go
// @ Requires a != nil And b != nil And a != b
// @ Modifies a.n, b.n
func Different(a, b *Counter) int {
	a.n = 1
	b.n = 2
	return a.n
}

//@ Ensures result = 1
```

Without `a != b` the postcondition is rejected, because the second assignment may overwrite the first.

The same holds for memory that lies inside other memory. A `*Point` may point at an element of a `[]Point`, or at a `Point` that is a field of a larger struct, and a `*A` may point at the same struct as a `*B` when the two types have the same fields. A write through one is then a write to the other, and a proof has to hold in either case unless the contract rules the overlap out with `~within(p, s)`.

A `Modifies` clause lists what a function may write, starting from its parameters:

- a pointer, as in `Modifies c`, means every field of the struct it points to;
- a slice, as in `Modifies A` or `Modifies s.items`, means its elements, including the capacity beyond its length, which an `append` may write;
- any other path must lead into memory, through a pointer or a slice, and means what it names: `Modifies c.count` is one field, `Modifies ps[0]` one element of a slice of structs, `Modifies s.From` a struct inside the struct `s` points to;
- an element can be selected on the way, as in `Modifies cs[0]` for the struct the first pointer of a slice points to.

The paths are read when the function is entered. A write to anything else that existed at that moment is an error, and so is an entry that no write needs, so the clause says neither less nor more than the body does. What the function creates itself, with `&T{...}`, `new`, `make`, a slice literal, an `append` that had to move the slice, or as a variable of its own, it may write freely.

Two further forms say where a pointer or slice comes from. `fresh(x)` in an `Ensures` states that the call created what `x` refers to, so it cannot be anything the caller already had. A slice without capacity reaches no memory at all and counts as fresh, whichever array it was cut from. `within(a, b)` states that `a` lies inside `b`, where each is a slice, taken with its capacity, or a pointer, taken as the struct it points to. A slice without capacity lies within anything, and a nil pointer within nothing. A method that appends to a slice in a struct typically promises both possibilities:

```go
// @ Requires s != nil And |s.items| < 1000
// @ Modifies s, s.items
func (s *Stack) Push(x int) {
	s.items = append(s.items, x)
}

//@ Ensures |s.items'| = |s.items| + 1 And s.items'[|s.items|] = x
//@ Ensures fresh(s.items) Or within(s.items', s.items)
```

Rules that follow from sharing:

- **A pointer must be known not to be nil where it is followed.** For a parameter or receiver that means `Requires p != nil`; `vego` proves the rest.
- **Slice parameters of one element type must not overlap**, capacities included. A function may assume it, and every call must prove it. `zero(A[:2])` may therefore write all of `A`'s capacity; cut the capacity with `A[:2:2]` to keep the rest.
- **`append` is the whole right-hand side of an assignment or the returned value.** It either writes into the capacity, where other slices of the array see it, or moves the slice to a new array; both outcomes are verified unless one can be ruled out.
- **A pointer points to a struct.** `&T{...}`, `&x`, `&p.field`, and `&s[i]` are all supported when what they point to is a struct, and so is calling a method with a pointer receiver on a variable, a field, or an element. A pointer to anything else, such as `*int`, is rejected.

### Invariants of structs

An invariant in the doc comment of a struct type names the fields directly and says what every value of the type satisfies:

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
```

`Top` may index with `s.n-1` because the invariant bounds `n`. An invariant is short for clauses at every boundary of every verified function:

- it is assumed on entry for each parameter and receiver of the type, or of a pointer to it that is not nil;
- it must be proved on return for each of them and for each result of the type. A struct passed by value is checked too, as it was on entry against memory as it is on return, because what it points to is shared with the caller;
- it must be proved at a call for each argument, and is known again afterwards for what a verified function hands back.

Inside a function the invariant may be broken and restored. There is no way to switch it off for a function: a helper that has to run while the invariant is broken takes the fields it needs instead of the struct. After a call to a trusted function that may modify a struct, its invariant is not assumed, since nobody proved it. The invariant is not applied to structs reached in other ways, such as the elements of a slice or the target of a pointer field.

### Maps

A map is a reference, like a pointer: two map variables may be the same map, and `Modifies m` allows writing it. In annotations `m[k]` is the value of a key, which is the zero value when the key is absent, as in Go; `has(m, k)` says whether the key is present; and `|m|` is the number of keys.

```go
func Get(m map[string]int, k string) (v int, err error) {
	v, ok := m[k]
	if !ok {
		return 0, errMissing
	}
	return v, nil
}

//@ Ensures err = nil <-> has(m, k)
//@ Ensures err = nil -> v = m[k]
```

Keys are integers or strings; values are any supported type. Writing to a map needs a proof that it is not nil; `delete` does not, since removing a key from a nil map does nothing. A `range` over a map visits some key the map has in each iteration, as many times as the map has keys; that the keys differ from one iteration to the next is not known to the verifier, an invariant has no name for how many iterations have run, and the loop must not change a map of that type. A loop can therefore check each value of a map, but cannot yet add the values up.

### Auditing specifications

A function can verify against a contract that says almost nothing. With `-vego.audit`, `vego` also probes each postcondition with degenerate implementations, the adversarial archetypes of the paper's Anti-VeGo: return zero values, return constants, return an argument unchanged, fill slices with zeros or with `0, 1, 2, ...`. Each one that provably satisfies the contract is reported as a hole:

```sh
laas -vego.audit ./...
```

```text
vego: specification of Sort has a hole [OBLIVIOUS]: it also accepts an implementation that fills its slices with 0, 1, 2, ... whatever the input
```

A sort that only ensures sortedness gets this report until its contract also ties the output to the input's elements.

### Calling code that is not verified

Verified code may only call a function that has a contract. A function with `//@` annotations is verified against them, and an exported one can be called from other packages: its contract and the predicates it uses travel with the package, and a function whose verification failed cannot be relied on from elsewhere. Any other function, whether in the standard library, in another module, or in your own code where `vego` cannot follow it, needs a trusted contract: a claim about the function that `vego` uses but does not check. A call to a function with neither is an error:

```text
vego: cannot verify Total: it calls applyDiscount, which has no contract; annotate applyDiscount with //@ so that it is verified, or add a trusted contract for example.com/shop.applyDiscount to vego-trusted.yaml
```

Trusted contracts for a module live in one file, `vego-trusted.yaml`, next to `go.mod`. There is no way to declare trust in source, so every assumption a proof rests on is in that one file:

```yaml
version: 1

trusted:
  example.com/shop/internal/store.load:
    reason: Reads the stock file; reviewed 2026-11-10.
    modifies: []
    ensures:
      - "err = nil -> count >= 0"

  example.com/vendor/ledger.Post:
    reason: Reviewed v1.4.2; appends one entry and keeps the others.
    modifies: [entries]
    requires:
      - "amount > 0"
    ensures:
      - "|entries'| = |entries|"
```

- The key is the function's full name as Go prints it: `sort.Ints`, `example.com/pkg.Func`, `(*bytes.Buffer).Len`.
- `reason` is mandatory. It says why the contract is believed, for whoever audits the file.
- `requires` and `ensures` use the annotation language. Callers must prove every `requires` and may assume every `ensures`. Names are the parameter and result names of the real function; unnamed results are `result`, or `result1`, `result2`, and so on.
- `modifies` lists what the function may write, in the form of a `Modifies` clause: `[x]` for the elements of slice `x`, `[b]` for the struct that pointer or receiver `b` points to, `[b.count]` for one field. Anything not listed is taken to be unchanged. The list is mandatory: a function that writes nothing a caller can see says so with `modifies: []`.
- Quote the formulas. YAML gives a meaning to `: `, to a leading `|`, `!`, `[`, or `-`, and to `#`, all of which formulas use.

`vego` checks what it can about a contract: the function must exist, the names must be parameters or results of the right type, `modifies` must list memory a caller can see, an `ensures` may only describe memory after the call (`x'`) if the path reads memory of a kind that `modifies` lists, since the call can have changed no other, and the contract must not contradict itself. At each call, a contract whose promise contradicts what is known there is reported as well, since everything after such a call would be provable; that check is a quick one and can miss a contradiction that is hard to find. A function cannot have both annotations and a trusted contract. Nothing is known about a pointer or slice that a trusted function returns unless its contract says so, for example with `fresh(result)`.

`vego` ships contracts for a small part of the standard library, such as `sort.Ints`, `sort.SearchInts`, `rand.Intn`, `strings.HasPrefix`, `strings.Index`, and `strconv.Itoa`. They state documented behaviour only, and each is tested against the real function. An entry in your file for the same function replaces the shipped one.

Run `laas` directly, as above. Under `go vet -vettool`, results are cached by a mechanism that does not know about trust files, so a proof could outlive the contract it rests on; `laas` therefore refuses to verify in that mode and says so.

To see everything the proofs of a project take on trust, with reasons and call sites:

```sh
laas -vego.trust ./...
```

The report lists the project contracts in use, the shipped contracts in use, project entries that no proof uses, and which trusted functions may fail unpredictably.

### Supported Go and trusted assumptions

The verified fragment covers functions and methods over the integer types (`int`, `int8` to `int64`, `uint`, `uint8` to `uint64`, with `byte` and `rune`), `bool`, `string`, `error`, the float types, structs, pointers to structs, maps with integer or string keys, and slices of any of these: assignments, `if`, `switch`, `for` and `range` loops with `break` and `continue`, `return`, `defer`, calls to named functions and methods, recursion, `len`, `cap`, `min`, `max`, `new`, `make`, `delete`, struct, slice, and map literals, slicing, and `append`. A struct field of a type outside this list cannot be read or assigned, but it remains part of its struct: assigning the whole struct writes it, so `Modifies` must then list the struct and not only the other fields. The exception is a field that is an array, or a struct holding one: a slice of the array would be a second view of the struct's memory, so a struct with such a field is not supported at all until arrays are. A function that uses anything else (arrays, channels, interfaces other than `error`, closures, goroutines, generics, variadic calls, `append(s, t...)`) is reported as `cannot verify` rather than verified wrongly.

Three kinds of value are followed without being fully understood:

- **Errors are opaque.** The only thing known about an error is whether it is `nil`. `errors.New` and `fmt.Errorf` return a non-nil error, and so does a package-level variable initialised with one of them and never assigned in its package, provided no code of the package can run before the variable is set: a package whose variable initialisers call a function value or an interface method, range over a function, start a goroutine, or put something of the package where another package may find it (as an argument or type argument to its functions, by assigning to anything but a plain variable, by a send, or by `append` or `copy`) gives up that knowledge, and says so where such a variable is read. Comparing two errors with `==` is rejected, because it panics when both hold the same uncomparable type. `fmt.Errorf` may only format numbers, booleans, strings, and slices of them whose types have no methods, and errors whose origin is known, since formatting anything else may run methods the verifier does not see. An error has a known origin when it was made by `errors.New` or `fmt.Errorf`, in the function itself or in a verified function it called, or is such a package-level variable; `fmt.Errorf("load: %w", err)` is accepted for those. An error that came in as a parameter or from a trusted function can be returned and compared with `nil`, but not formatted. Nothing but an error or `nil` can be converted to an error.
- **Floats are opaque.** Arithmetic on floats yields an unknown float and a comparison an unknown boolean, so no fact about a float value can be stated or proved. An integer converted from a float can be anything in its type's range and needs a range check before it is used as an index.
- **Strings are sequences of bytes**: length, indexing, `==`, literals, concatenation, substrings, and conversion to and from `[]byte`. Ordering with `<` is unknown. Ranging over a string yields some character and advances by one to four bytes; which character is not modelled.

A function that returns an error must say when it succeeds. A contract such as `err = nil -> value = A[i]` alone is rejected, because a function that always fails would satisfy it. The contract has to force success for some input, as `0 <= i < |A| -> err = nil` or `err = nil <-> 0 <= i < |A|` does. The verifier looks for a small concrete input that satisfies the precondition and for which the postcondition leaves no outcome with a non-nil error, and rejects the contract if it finds none. The exception is a function whose success hangs on a call to a trusted function whose contract does not say what comes back, such as one that reads a file: it cannot promise success and is not asked to. Its success hangs on the call when the call decides between failure and success: some return of an error and some return without one each depend on what the call returned, by returning the call's error or by a branch on something it returned. A function that ignores what the call returned, or that fails whatever it returned, is not excused. What the call returned is followed through variables, also across loops, through memory the function itself reads, and through later calls it is passed to, but not through memory that a later call reads or that a loop writes. Whether the call is reached is judged generously when the path to it depends on values the verifier does not know, such as the result of an earlier call; only the conditions on the function's own inputs must be satisfiable by a concrete input. A dead call behind such an unknown can therefore keep a weak contract from being reported. The same holds for a call that in fact always succeeds, when seeing that takes facts about memory more than one pointer away from its arguments: what the types guarantee is supplied for the arguments, for the elements of their slices, and for the objects their pointers refer to, but not further.

Proofs hold under these assumptions, which mirror the paper's trusted base:

- **There is memory.** An allocation larger than the runtime permits is an error the verifier reports: `make([]T, n)`, an `append` that has to move its slice, and a string concatenation must be proved to stay under the limit of the platform. That the machine actually has the memory, and that the stack is deep enough for the recursion, is assumed.
- **Bits are numbers.** The verifier computes with whole numbers, not with bits, so shifts and bitwise operators are understood through arithmetic.
  - `x << k` is `x * 2^k` and must not lose bits, like any arithmetic that would leave its type. `x >> k` is `x / 2^k` rounded towards minus infinity, which differs from `/` for a negative `x`. A count that may be negative is an error, since Go panics on one.
  - `x & m` is known exactly when `m` is a constant mask of low bits (`x & 0xFF` is `x % 256`) or of a single bit. Of any other `x & y` only what always holds is known: it is at most either operand when they are not negative, and so on.
  - `x | y`, `x ^ y`, and `x &^ y` are computed from `x & y`, so they are known exactly whenever it is. `hi<<8 | lo` is `256*hi + lo` when `lo` is below 256.
  - `^x` is `-x - 1`, or for an unsigned type the largest value minus `x`.
  - Annotations have no bit operators; say what you mean with `*`, `/`, and `%`.
- **Overflow is an error, not a behaviour.** Every `+`, `-`, `*`, `/`, negation, and conversion must be proved to stay within its type, so `(lo+hi)/2` is rejected and `lo + (hi-lo)/2` verifies. This usually means stating bounds on inputs, for example on the elements a loop adds up. Code that wraps on purpose, such as a hash function, cannot be verified.
- **Callers outside the verified code keep the contract.** A verified function may assume its `Requires`, the invariants of the structs it is handed, and that slice parameters of one element type do not overlap. Verified callers prove all three; code that is not verified is trusted to respect them.
- **Nothing else runs at the same time.** A proof is about one goroutine. No other goroutine writes memory that a verified function reads or writes while it runs.
- **Code that is not verified keeps Go's types.** It does not use `unsafe`, `reflect`, or cgo to make one piece of memory two different types, or to change a string. The memory model relies on what Go's types guarantee.
- **The proof is for the platform it was run for.** The sizes of `int`, `uint`, and pointers, the layout of structs, and the largest allocation are those of the `GOOS` and `GOARCH` that `laas` was run with. A function verified for a 64-bit target is not thereby verified for a 32-bit one.
- **Annotations are not checked for meaning.** `A[i]` in an annotation is not required to be in range and `x / y` not to have a divisor other than zero. Such a term has some value nobody knows, so a clause that depends on it can usually not be proved, but it is not reported either.
- **A deferred call runs at every return.** `defer mu.Unlock()` settles the function, the receiver, and the arguments where it is written, and the call is then verified at each way out of the function, last one first: its `Requires` must hold there, and what it changes is part of what the function's `Ensures` describe. It can change a result through a pointer to a named result, as Go allows. Only a call of a named function or method can be deferred, and not inside a loop.
- **Calls that modify memory stand alone.** A call to a function with a `Modifies` clause must be a statement of its own, the only returned expression, or the whole right-hand side of an assignment to variables or their fields, so that it cannot run between the evaluation of other operands. It is rejected inside a larger expression, as an argument, in a loop condition, or when the assignment's target is reached through a pointer, a slice, or a map.
- **Memory a loop writes is forgotten at the loop.** What a loop changes through a variable it does not reassign, or through a slice it only appends to, is forgotten precisely: everything else stays known. A loop that writes through anything more involved, such as `s.items[i]` or a pointer it advances, forgets every object of that type that the function may modify, and an invariant has to restate what is needed.
- **Exported error variables are not reassigned.** A sentinel such as `var ErrNotFound = errors.New(...)` is taken to be non-nil when its own package never assigns to it. Another package assigning to it would break that; one that `laas` analyses in the same run is reported, one that it does not see is trusted not to.
- **String length stays representable.** Concatenation must be proved not to exceed the largest `int`, which usually means bounding the lengths of the operands.
- **Trusted contracts are true.** A function that is not verified can only be called through a contract in a trust file, and every proof that uses it holds only if that contract does. Such a function is also trusted to return without panicking when its `requires` hold, which includes that it does not call back into the verified function that called it by way of another package. A call back that stays inside the package is seen and reported: by name, or through a function value or an interface method, which are taken to reach any function the package names anywhere other than to call it, to write nothing a caller can see beyond its `modifies`, and not to keep the pointers and slices it is given.

Not implemented yet from the paper: residual runtime checks for unproved obligations (gradual mode), multiset reasoning, the `Preserves`, `Immutable`, `Cost`, and `Library` annotations, and mutation-based audit candidates.

Raise the solver's effort for a hard obligation with `-vego.max-steps`.

## Package filtering

Skip packages for every analyzer with `-exclude-packages`. The value is a Go regular expression matched against the package import path:

```sh
laas -exclude-packages='(^|/)(generated|mocks)($|/)' ./...
```

Regular expressions use substring matching unless anchored. An invalid expression causes argument parsing to fail before analysis starts.

## License

This project is licensed under the [MIT License](LICENSE).
