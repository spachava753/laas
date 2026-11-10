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
- no slice index is out of range, no divisor is zero, no `make` length is negative, and no `panic` is reachable;
- no integer arithmetic or conversion overflows. Go would wrap silently; verified code may not;
- every call satisfies the callee's `Requires`. Callers then rely on the callee's `Ensures` only, never on its body;
- a function that returns an error does not have a contract it could meet by failing every time.

There is no external solver. Proof obligations are generated by symbolic execution over single-assignment values and discharged by a deduction engine written in Go: case splitting, linear integer arithmetic by Fourier–Motzkin elimination, bounds on products obtained by multiplying known inequalities, read-over-write reasoning for slices, quantifier instantiation, and bounded unfolding of predicates. The engine is sound and deliberately incomplete: when it cannot prove a true fact, add an `//@ Assert` with an intermediate step or strengthen an invariant.

### Annotations

| Annotation | Where | Meaning |
| --- | --- | --- |
| `Requires P` | doc comment of a function | Precondition: callers must establish `P`. |
| `Ensures P` | doc comment, or a comment after the closing brace | Postcondition. Parameters denote their values on entry, result names the returned values, and `A'` the contents of slice parameter `A` on return. An unnamed single result is called `result`; several are `result1`, `result2`, and so on. |
| `Invariant P` | directly above a `for` loop | Holds before every evaluation of the loop condition. |
| `Variant e` | directly above a `for` loop | Integer that is non-negative while the loop runs and decreases every iteration. `range` loops need none. |
| `Measure e` | doc comment of a recursive function | Integer over the parameters that is non-negative and decreases at every recursive call, including mutual recursion. |
| `Assert P` | anywhere in a body | Must hold at that point; later proofs may use it. |
| `Predicate name(params) ::= P` | top level | A named, possibly recursive formula. Recursion must not pass through negation. |

Formulas use `And`, `Or`, `~`, `->`, `<->`, `True`, `False`, the comparisons `=`, `!=`, `<`, `<=`, `>`, `>=` (which chain, as in `0 <= i < |A|`), and integer arithmetic with Go's `/` and `%`. Integers in formulas are mathematical and never overflow; the limits of the Go types are available as `MaxInt`, `MinInt`, `MaxInt8` to `MaxInt64`, `MinInt8` to `MinInt64`, and `MaxUint` to `MaxUint64`. `|A|` is the length of a slice or string and `A[i]` an element or byte. Strings compare with `=` and can be written as literals, as in `role = "admin"`. An error can be compared with `nil`, as in `err = nil -> value = A[i]`. Quantifiers range over the integers or an interval: `Forall k in [0, |A|) : A[k] >= 0`, `Exists t in Z : ...`. A slice range used as a comparison operand stands for all its elements: `A[0:i) <= A[i]`. Inside a body a name denotes the current value of the variable and `old(x)` the value parameter `x` had on entry. Boolean variables are compared with constants as in the paper (`found = True`) or used directly. A `//` inside an annotation starts an ordinary comment, and a line that does not begin with a keyword continues the previous annotation. An annotation inside a body must stand between statements on a line of its own, and an unknown word after `@ ` is an error, so a misspelt keyword cannot silently switch a check off.

`gofmt` rewrites `//@` to `// @` inside doc comments; both spellings are accepted. A detached `Ensures` comment belongs to the function that ends just above it.

### Auditing specifications

A function can verify against a contract that says almost nothing. With `-vego.audit`, `vego` also probes each postcondition with degenerate implementations, the adversarial archetypes of the paper's Anti-VeGo: return zero values, return constants, return an argument unchanged, fill slices with zeros or with `0, 1, 2, ...`. Each one that provably satisfies the contract is reported as a hole:

```sh
laas -vego.audit ./...
```

```text
vego: specification of Sort has a hole [OBLIVIOUS]: it also accepts an implementation that fills its slices with 0, 1, 2, ... whatever the input
```

A sort that only ensures sortedness gets this report until its contract also ties the output to the input's elements.

### Supported Go and trusted assumptions

The verified fragment covers functions over the integer types (`int`, `int8` to `int64`, `uint`, `uint8` to `uint64`, with `byte` and `rune`), `bool`, `string`, `error`, the float types, and slices of integers, booleans, and floats: assignments, `if`, `switch`, `for` and `range` loops with `break` and `continue`, `return`, calls to named functions, recursion, `len`, `min`, `max`, `make`, slice literals, and `x = append(x, ...)` on a local slice. A function that uses anything else (structs, pointers, maps, methods, closures, goroutines, generics) is reported as `cannot verify` rather than verified wrongly.

Three kinds of value are followed without being fully understood:

- **Errors are opaque.** The only thing known about an error is whether it is `nil`. `errors.New` and `fmt.Errorf` return a non-nil error, and so does a package-level variable initialised with one of them and never assigned in its package. Comparing two errors, or calling `errors.Is`, gives an unknown answer.
- **Floats are opaque.** Arithmetic on floats yields an unknown float and a comparison an unknown boolean, so no fact about a float value can be stated or proved. An integer converted from a float can be anything in its type's range and needs a range check before it is used as an index.
- **Strings are sequences of bytes**: length, indexing, `==`, literals, concatenation, substrings, and conversion to and from `[]byte`. Ordering with `<` is unknown. Ranging over a string yields some character and advances by one to four bytes; which character is not modelled.

A function that returns an error must say when it succeeds. A contract such as `err = nil -> value = A[i]` alone is rejected, because a function that always fails would satisfy it; add a clause like `0 <= i < |A| -> err = nil`. The exception is a function that calls something whose own failure no contract predicts, such as reading a file: it cannot promise success and is not asked to.

Proofs hold under these assumptions, which mirror the paper's trusted base:

- **Overflow is an error, not a behaviour.** Every `+`, `-`, `*`, `/`, negation, and conversion must be proved to stay within its type, so `(lo+hi)/2` is rejected and `lo + (hi-lo)/2` verifies. This usually means stating bounds on inputs, for example on the elements a loop adds up. Code that wraps on purpose, such as a hash function, cannot be verified. Shifts and bitwise operators are not supported yet.
- **Slices are values.** Operations that would make two variables share a backing array are rejected: assigning one slice variable to another, sub-slicing, returning a slice parameter, or passing one slice twice to a function that writes it. Callers outside the verified code must likewise pass slices that do not overlap.
- **Calls that modify a slice stand alone.** Such a call must be a statement of its own or the whole right-hand side of an assignment to plain variables, so that it cannot run between the evaluation of other operands. It is rejected inside a larger expression, as an argument, in a loop condition, or when the assignment's target is a slice element.
- **Exported error variables are not reassigned.** A sentinel such as `var ErrNotFound = errors.New(...)` is taken to be non-nil when its own package never assigns to it; another package assigning `nil` to it would break that.
- **String length stays representable.** Concatenation must be proved not to exceed the largest `int`, which usually means bounding the lengths of the operands.
- **Unannotated callees are trusted** to return without panicking and not to keep the slices they receive. Nothing is known about their results, and the slices they are passed are assumed to have changed.

Not implemented yet from the paper: residual runtime checks for unproved obligations (gradual mode), structs and pointer structures, multiset reasoning, the `Preserves`, `Immutable`, `Cost`, and `Library` annotations, and mutation-based audit candidates.

Raise the solver's effort for a hard obligation with `-vego.max-steps`.

## Package filtering

Skip packages for every analyzer with `-exclude-packages`. The value is a Go regular expression matched against the package import path:

```sh
laas -exclude-packages='(^|/)(generated|mocks)($|/)' ./...
```

Regular expressions use substring matching unless anchored. An invalid expression causes argument parsing to fail before analysis starts.

## License

This project is licensed under the [MIT License](LICENSE).
