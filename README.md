# laas

`laas` is a command that checks Go code. It runs four analyzers over Go packages:

| Analyzer | What it reports |
| --- | --- |
| [`funcdoc`](#funcdoc) | a complex function whose doc comment does not start with its name |
| [`inlinehelper`](#inlinehelper) | a small unexported helper that is called from one place only |
| [`teststructure`](#teststructure) | tests that share a name prefix, and subtests whose body is not written inline |
| [`vego`](#vego) | an annotated function that it cannot prove correct against its contract |

The first three are linters. `vego` is a verifier. It proves that a function meets a contract written in comments. The repository also has [agent skills](#agent-skills) for setting up `laas` and for writing Go documentation, and [evaluations](#documentation-evals) of the second.

The checks are meant to help coding agents write idiomatic, well-structured Go.

## Install and run

```sh
go install github.com/spachava753/laas/cmd/laas@latest
laas ./...
```

The arguments are package patterns, as for `go vet`. `laas` runs every analyzer and prints one line for each problem it finds. It exits with status 0 if it found nothing, 3 if it reported something, and 1 if it could not load the packages.

The flags of each analyzer start with its name, as in `-funcdoc.limit=15`. `laas -help` lists them all. Test files are analysed too. `-test=false` leaves them out.

Build `laas` with the same Go that you run it with. The `go` command that `laas` finds at run time must not be newer than the Go that built `laas`. If it is, `laas` reports errors about the standard library. Rebuild `laas`, or set `GOTOOLCHAIN` to the version that built it.

### Skipping packages

```sh
laas -exclude-packages='(^|/)(generated|mocks)($|/)' ./...
```

`-exclude-packages` takes a Go regular expression and skips every package whose import path it matches. The expression can match anywhere in the path unless you anchor it. If the expression is not valid, `laas` stops before it analyses anything.

## funcdoc

`funcdoc` reports a function or method whose cyclomatic complexity is above a limit, unless its doc comment starts with its name.

```text
function classify has cyclomatic complexity 12 (limit 10); its doc comment should start with "classify"
```

A function with no doc comment gets a different message: `add a doc comment immediately above it starting with "classify" that explains its logic`.

The complexity is computed as by [`gocyclo`](https://github.com/fzipp/gocyclo). A function starts at 1. Each `if`, `for`, `range`, `case` other than `default`, `&&`, and `||` adds 1.

The doc comment is the one Go attaches to the declaration, directly above it. A comment separated from the declaration by a blank line does not count, and neither does a comment inside the body. `funcdoc` checks only that the first word is the function's name. The rest of the comment should explain how the function works, for a reader who is about to read it.

| Flag | Default | Effect |
| --- | --- | --- |
| `-funcdoc.limit=n` | 10 | the highest complexity allowed without such a comment |
| `-funcdoc.include-tests` | off | also check functions in `_test.go` files |

## inlinehelper

`inlinehelper` reports an unexported function or method that has a few statements and is called from exactly one place.

```go
func double(n int) int {
	return n * 2
}
```

```text
function double has 1 statement and is called once; consider inlining it at its call site
```

Statements are counted in the syntax tree, including those in nested blocks. A block itself does not count, and a statement that spans several lines counts once.

A function is not reported if any of these is true:

- it is exported, because calls from other packages are not visible;
- it is never called, or it is referenced more than once;
- its only reference is not a direct call, as when it is used as a function value;
- it calls itself.

The message is advice. A small helper can be worth keeping for its name. `inlinehelper` offers no automatic fix.

| Flag | Default | Effect |
| --- | --- | --- |
| `-inlinehelper.max-statements=n` | 4 | the largest number of statements a reported helper can have |

## teststructure

`teststructure` checks `_test.go` files for two things.

The first is a group of tests whose names share a prefix:

```go
func TestParseValidInput(t *testing.T)   { ... }
func TestParseInvalidInput(t *testing.T) { ... }
```

```text
tests TestParseValidInput and TestParseInvalidInput share prefix TestParse; consolidate scenarios into one test using a table or t.Run subtests
```

Names are split into words at changes of case, at initialisms, at digits, and at underscores, and then compared word by word. `TestHTTPServer` and `TestHTTPClient` share the prefix `TestHTTP`. `TestParseInput` and `TestParserInput` share no prefix, because `Parse` and `Parser` are different words. Only functions of the form `TestXxx(*testing.T)` are compared, so benchmarks, fuzz tests, examples, helpers, and `TestMain` are left alone. `teststructure` reads only the names. It does not look at whether a test already uses a table or subtests.

The second is a subtest whose body is defined somewhere else:

```go
t.Run("zero", checkZero)
```

```text
testing.T.Run callback must be an inline function literal; move the subtest body into the Run call
```

A named function, a method value, and a function variable are all reported. Write the body as a function literal in the call, so that it stays next to the subtest's name. This check applies only to the `Run` method of `testing.T`. Other methods named `Run` are not checked.

`teststructure` has no flags.

## vego

`vego` is a deductive verifier for Go. You write a function's contract in `// @` comments. `vego` either proves that the function meets the contract for every input, or reports what it could not prove. The comments do not change the program. It builds and runs with the standard Go toolchain as before. `vego` follows the approach of the VeGo paper ([Masoudi and Dutchyn, arXiv:2608.22630](https://arxiv.org/abs/2608.22630)).

```go
// Divide computes quotient and remainder by repeated subtraction.
//
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

`Requires` states what must be true when the function is called, and `Ensures` what is true when it returns. The `Invariant` holds each time the loop tests its condition. The `Variant` is a number that never goes below zero and decreases on each iteration, so the loop ends.

`laas -vego` prints nothing for this function, because every clause is proved. If you change the loop condition to `d < r`, the loop can stop with `r` equal to `d`, and `vego` reports:

```text
vego: postcondition may not hold: 0 <= r < d
```

Apart from the contract, `vego` proves these things about every verified function:

- it does not panic, for example on an index out of range, a nil pointer, or a division by zero;
- no integer arithmetic overflows;
- every loop and every recursion ends;
- it writes only the memory that its contract lists.

`vego` checks only functions that have at least one annotation.

### Status

`vego` is experimental. Its tests check that it does not prove false claims, but it has not yet been used on a large existing codebase.

`vego` supports only part of Go. It verifies functions over integers, booleans, strings, errors, structs, pointers to structs, slices, and maps with integer or string keys. Floats can be used, but nothing is proved about their values. A function that uses other Go is reported as `cannot verify` and is not verified. Examples are interfaces other than `error`, calls of function values whose type has no contract, generics, goroutines, and arrays. A function literal that is called or deferred where it is written is verified at each call, and one handed to a trusted function that calls it, such as `sort.Search`, is verified where it is handed over. [`vego/ROADMAP.md`](vego/ROADMAP.md) lists what is missing, in the order in which it is planned.

### Running it

`vego` proves its obligations with [Z3](https://github.com/Z3Prover/z3) 5.4.1, which runs as a separate program. Install [that release](https://github.com/Z3Prover/z3/releases/tag/z3-5.4.1) and put its `bin/z3` on `PATH`, or pass the path of the binary with `-vego.z3=path`. `laas` refuses any other version of Z3, because another version may prove different things. A package without annotations does not need Z3.

```sh
laas -vego ./...
```

`-vego` runs only the verifier. Plain `laas ./...` runs it together with the other analyzers. Run `laas` directly, not through `go vet -vettool`. The cache of `go vet` does not know about the trust file, so `vego` refuses to verify in that mode.

A verified function can call only functions that have a contract. A function without annotations, such as one in another module, can be given a trusted contract in `vego-trusted.yaml`, next to `go.mod`. `vego` uses a trusted contract without checking it, and ships trusted contracts for a few functions of the standard library. `laas -vego.trust ./...` lists every trusted contract that the proofs use.

### Learning more

[Writing verified Go](docs/verification.md) is the guide to `vego`. It covers the annotations and the formula language, loops, memory, errors, trusted contracts, and the messages `vego` prints. Its [Summary](docs/verification.md#summary) section is a reference for every annotation, formula form, and flag. A proof also rests on assumptions about code that `vego` cannot see, and the guide lists them in [What a proof assumes](docs/verification.md#what-a-proof-assumes).

## Agent skills

### setup-laas-pre-commit

[`setup-laas-pre-commit`](skills/setup-laas-pre-commit/SKILL.md) tells an agent how to run `laas` before every commit in a Go repository. The agent pins `laas` as a Go tool dependency and adds `go tool laas ./...` to the pre-commit hook mechanism that the repository already uses. If the repository has none, the agent creates a tracked `.githooks/pre-commit` hook. It asks before it bypasses a hook that is already installed in `.git/hooks`.

Install the skill with a version of the GitHub CLI that supports agent skills:

```sh
gh skill install spachava753/laas setup-laas-pre-commit --scope user
```

Add `--agent` to install it for one agent only.

### golang-docs

[`golang-docs`](skills/golang-docs/SKILL.md) guides an agent in writing doc comments that state a Go API's contract: preconditions, zero values, ownership, errors, and how fields interact. Its instructions are general. It contains no benchmark repositories, declarations, or answer text.

The skill is experimental. The [Harbor experiment](evals/golang-docs/EXPERIMENT.md) records how agents did with and without it. The revision that was selected showed a small gain on the development tasks, and that gain did not carry over to the holdout tasks.

## Documentation evals

[`evals/golang-docs`](evals/golang-docs/README.md) builds a pilot of 12 Harbor tasks from pinned sources of `jsonschema-go` and the MCP Go SDK. In each task, an agent restores comments that were removed from functions, methods, types, and struct fields. An isolated verifier checks that only the requested comments changed. It then scores how much of the meaning they cover, using OpenAI's Decisions API.

The generator, verifier, runner, and tests use only Go's standard library. Harbor is an external command-line tool, needed only to run the trials in containers. The evals were built before the `golang-docs` skill, and they now provide its baseline and the comparisons for its revisions.

## The name

*Laas* (Ancient Greek: λᾶας) means stone. The name refers to the boulder that Sisyphus pushed uphill without end. Code quality needs the same repeated effort, and `laas` turns it into checks that a coding agent can run until its code passes.

## License

This project is licensed under the [MIT License](LICENSE).
