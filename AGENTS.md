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
- **Do the right thing, or narrow the subset. Never take a shortcut.** When a problem turns up, in development or in review, there are exactly two acceptable outcomes. Either solve it properly, even when that means redesigning or rewriting a large part of the verifier end to end; or, after real attempts and thought have shown that there is no known way forward, stop supporting the Go that causes it and report that Go as `cannot verify`. Not acceptable: a patch for the reported case that leaves the cause in place, an assumption added to the README to cover a gap the verifier could close, or a quiet approximation. The goal is the largest subset of Go that can be supported with no compromise; it is not all of Go. Everything inside the subset must be verified without undermining trust in the result.
- **An assumption is a last resort and must be about something the verifier cannot see.** What unverified callers and trusted functions do is outside its view and may be assumed, in the README, in plain words. What a verified function itself does is not.
- **You own this code.** If a design is in the way, of soundness, of speed, or of supporting more Go, redesign it. If something is a paper cut, fix it. Do not wait to be asked, and do not leave a known weakness for later because the change is large.
