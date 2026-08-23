# laas

`laas` is a home for linters, development helpers, and reusable agent skills that help coding agents write better, more idiomatic Go.

## Why laas?

*Laas* (Ancient Greek: λᾶας) means stone. The word evokes the enormous stones and boulders of Greek mythology: those thrown by heroes and the one Sisyphus was condemned to push uphill.

A Sisyphean task is grueling, uphill, and seemingly endless. Code quality can feel similar. Lint violations, structural details, and idiomatic conventions demand sustained attention, but coding agents are intelligent, tireless, and particularly good at hill climbing.

`laas` gives agents a boulder to push. By expressing Go code-quality expectations as tools and skills, the project aims to turn that persistence into consistently better code.

## Scope

The project will contain:

- Linters and checks for idiomatic Go and sound code structure.
- Helpers that make code-quality constraints easier for agents to apply.
- Agent skills that capture reusable guidance for writing and reviewing Go.

## funcdoc

`funcdoc` reports a function or method when both of these conditions hold:

- Its cyclomatic complexity is greater than the configured limit, which defaults to 10.
- Its body does not begin with a substantive comment whose first word exactly matches the function or method name and explains the implementation's plan.

The score follows [`gocyclo`](https://github.com/fzipp/gocyclo): every function starts at 1, then each `if`, `for`, `range`, non-default `case`, `&&`, and `||` adds 1. Following Go's documentation convention, an overview for `reconcile` must begin with `reconcile`. A declaration comment describing the API or a local comment later in the body does not replace the leading implementation overview.

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

`teststructure` reports standard `TestXxx(*testing.T)` functions in `_test.go` unless they use one of these forms:

- Nested subtests invoked through `Run` on the test function's own `*testing.T` parameter.
- A range loop over a locally initialized slice, array, or map of test cases.

This encourages related scenarios to live under one outer test, such as `TestParse` with `t.Run("valid input", ...)` and `t.Run("invalid input", ...)`, instead of separate functions such as `TestParseValidInput` and `TestParseInvalidInput`. Benchmarks, fuzz targets, examples, test helpers, and `TestMain` are not checked.

The analyzer runs as part of the standard command:

```sh
laas ./...
```

## License

This project is licensed under the [MIT License](LICENSE).
