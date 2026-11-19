# Project Purpose

`laas` contains Go linters, development helpers, and agent skills that help coding agents produce idiomatic, well-structured Go. The project focuses on enforceable concerns such as lint compliance and code structure. It also contains `vego`, a deductive verifier that proves functions correct against `//@` comment annotations.

## Repository Instructions

`.gitignore` uses an allowlist. Explicitly allow any required non-Go files when adding them.

Before finishing a change, run the tests and run `laas` on itself:

```sh
go test ./...
go run ./cmd/laas ./...
```

`laas` must be built by a Go that is at least as new as the `go` command it finds when it runs. `go run` builds it with that same `go`, so the command above works on any toolchain. A `laas` binary built earlier by an older Go fails with errors about the standard library; rebuild it, or set `GOTOOLCHAIN` to the version that built it.

## Documentation

`docs/AGENTS.md` has the rules for writing documentation: how the text should read, and how its claims are checked. Follow it for anything in `docs/` and for the user-facing sections of the README.

## Heavy work must not take the machine down

Every agent on this machine, and everything any agent starts, runs inside one systemd scope together with the app that hosts the agents. When memory and swap run out, `systemd-oomd` kills that whole scope: every agent thread of every project stops at once and loses whatever it had not saved. This has happened several times, each time during fuzzing or mutation runs that an agent had started without a limit.

So, for anything heavier than the two commands above:

- **At most four processes at a time.** That covers fuzz workers, mutation runs, parallel test suites on copies of the repository, and `xargs -P` or `make -j` of anything that compiles Go or runs the verifier. Each run of the verifier or of a test binary that uses it also starts up to four Z3 processes of up to 1 GB each; count them, or set `GOMAXPROCS` lower to start fewer. The machine has 24 cores and 31 GB of memory; it is the memory that runs out, not the cores.
- **Run it in its own memory-limited scope**, so that if it grows, it alone is killed:

  ```sh
  systemd-run --user --scope --quiet -p MemoryMax=12G -p MemorySwapMax=4G -- <command>
  ```

  Start a driver script this way and its workers inherit the limit. Do not start several such scopes side by side to get around the limit.
- **Give long runs a bound**: a number of cases or a time limit, not "until stopped".
- **When you hand work to another agent**, in a brief or a review request, repeat these limits in the brief. An agent that was only told to "fuzz for as long as practical" will start twenty workers.

## vego

The kind of code vego targets, planned work, and settled design decisions are in `vego/ROADMAP.md`. Read it before changing the verifier, and record new decisions there.

- **Never trade soundness for convenience.** The verifier may fail to prove something true; it must never accept something false. Go it cannot model correctly is reported as `cannot verify`, not approximated.
- **Take the loudest path.** When a check could warn, stay silent, or fail, make it fail. Agents loop on this tool's output, so any quiet path gets taken. No hidden or implicit trust.
- **Guard the translation.** The prover is Z3 5.4.1, pinned in `vego/internal/solver`; it must be on `PATH` for the tests, which fail without it. `TestProveIsSound` checks goals Z3 proved against brute-force evaluation of the logic, and `TestTranslation` and `TestRules` check single rules. Keep them passing, and when adding or changing a rule of the translation to SMT-LIB, confirm the tests fail on a deliberately wrong version of that rule. A `sat` answer is never evidence: the translation describes more states than Go has. A rule that builds a term must not put an operand into it more than once, and every new rule needs a chain in `vego/testdata/src/semantics/chains.go`, which the growth check of the test binary enforces.
- **Test both directions.** New verifier behaviour needs a program that verifies and a defective one that is rejected, under `vego/testdata/src`.
- **Do the right thing, or narrow the subset. Never take a shortcut.** When a problem turns up, in development or in review, there are exactly two acceptable outcomes. Either solve it properly, even when that means redesigning or rewriting a large part of the verifier end to end; or, after real attempts and thought have shown that there is no known way forward, stop supporting the Go that causes it and report that Go as `cannot verify`. Not acceptable: a patch for the reported case that leaves the cause in place, an assumption added to the documentation to cover a gap the verifier could close, or a quiet approximation. The goal is the largest subset of Go that can be supported with no compromise; it is not all of Go. Everything inside the subset must be verified without undermining trust in the result.
- **An assumption is a last resort and must be about something the verifier cannot see.** What unverified callers and trusted functions do is outside its view and may be assumed, in plain words, in the "What a proof assumes" section of `docs/verification.md`. What a verified function itself does is not.
- **You own this code.** If a design is in the way, of soundness, of speed, or of supporting more Go, redesign it. If something is a paper cut, fix it. Do not wait to be asked, and do not leave a known weakness for later because the change is large.
