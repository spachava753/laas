# Project Purpose

`laas` contains Go linters, development helpers, and agent skills that help coding agents produce idiomatic, well-structured Go. The project focuses on enforceable concerns such as lint compliance and code structure. It also contains `vego`, a deductive verifier that proves functions correct against `//@` comment annotations.

## Repository Instructions

`.gitignore` uses an allowlist. Explicitly allow any required non-Go files when adding them.

Before finishing a change, run the tests and run `laas` on itself:

```sh
go test ./...
GOTOOLCHAIN=go1.26.6 go run ./cmd/laas ./...
```

The pinned `golang.org/x/tools` cannot read packages built by Go 1.27 or newer, so the second command needs the toolchain named in `go.mod`.

## vego

The kind of code vego targets, planned work, and settled design decisions are in `vego/ROADMAP.md`. Read it before changing the verifier, and record new decisions there.

- **Never trade soundness for convenience.** The verifier may fail to prove something true; it must never accept something false. Go it cannot model correctly is reported as `cannot verify`, not approximated.
- **Take the loudest path.** When a check could warn, stay silent, or fail, make it fail. Agents loop on this tool's output, so any quiet path gets taken. No hidden or implicit trust.
- **Guard the solver.** `TestProveIsSound` in `vego/internal/solver` checks proved goals against brute-force evaluation. Keep it passing, and when adding a solver rule, confirm the test fails on a deliberately wrong version of that rule.
- **Test both directions.** New verifier behaviour needs a program that verifies and a defective one that is rejected, under `vego/testdata/src`.
