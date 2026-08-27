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

## Package filtering

Skip packages for every analyzer with `-exclude-packages`. The value is a Go regular expression matched against the package import path:

```sh
laas -exclude-packages='(^|/)(generated|mocks)($|/)' ./...
```

Regular expressions use substring matching unless anchored. An invalid expression causes argument parsing to fail before analysis starts.

## License

This project is licensed under the [MIT License](LICENSE).
