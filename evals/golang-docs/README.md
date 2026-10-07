# golang-docs evals

A 12-task Harbor pilot for writing Go doc comments. This builds the evals first;
the `golang-docs` skill itself is intentionally not written yet.

Each task removes the associated doc comment from one function, method, or type.
For structs, it also removes all field comments. The agent edits the comments in
place, with the rest of the module available as context. The original upstream
comments are the reference answers, not a requirement to reproduce their wording.

There are three tasks of each kind: function, method, struct, and other type
(function type, interface, defined string type).

| Source | Split | Tasks |
| --- | --- | --- |
| [`google/jsonschema-go`](https://github.com/google/jsonschema-go) | Development | 6 |
| [`modelcontextprotocol/go-sdk`](https://github.com/modelcontextprotocol/go-sdk) | Holdout | 6 |

[`manifest.json`](manifest.json) records the exact commits, archive SHA-256 hashes,
files, symbols, and splits. Both upstreams use MIT licenses; generated snapshots
retain their licenses and copyright notices. No private repositories or GitHub
credentials are required.

## Generate and check the dataset

Run these commands from the repository root. Requirements: Go 1.26.6 or newer
and network access to public GitHub archives. All repository-owned tooling and
tests use Go's standard library; there are no additional module dependencies.
Harbor is needed only for container trials, not generation or local validation.

```sh
go run ./evals/golang-docs generate
go test ./evals/golang-docs
go run ./evals/golang-docs validate
```

Generation checks archive integrity, strips comments with Go's AST byte ranges,
and verifies that no code or unrelated comment tokens changed. It checks for
another verbatim copy of the complete declaration comment in the agent snapshot.
It refuses to overwrite existing tasks. For a new dataset, choose a fresh output:

```sh
go run ./evals/golang-docs generate \
  --split dev --output evals/golang-docs/.cache/dev-tasks
```

`validate` checks task layouts, isolation settings, and shell syntax; restores
each reference in a temporary copy; verifies its structural gate; builds its
judge request; and checks that missing docs produce zero. It does **not** import
Harbor or fully validate its TOML schema. Harbor validates configurations when
running trials. Local checks do not exercise containers, artifact transfer,
networking, or an agent rollout.

Generated tasks, caches, environments, and job results are ignored by Git.
The manifest and generator are the reproducible dataset definition.

```text
evals/golang-docs/
├── manifest.json        # Pinned upstreams and 12 target declarations
├── main.go              # Go CLI entrypoint
├── files.go             # Shared types, file helpers, embedded verifier sources
├── generate.go          # Archive download and Harbor task generation
├── inspect.go           # Go AST inspection and non-doc token fingerprint
├── grade.go             # Deterministic gates and Decisions API grader
├── run.go               # External Harbor runner and scoped Docker DNS shim
├── validate.go          # Local task checks and optional live calibration
├── *_test.go            # Offline regression tests
└── tasks/               # Generated, self-contained Harbor tasks (ignored)
    └── <task>/
        ├── task.toml
        ├── instruction.md
        ├── README.md
        ├── environment/ # Stripped source, fixtures, license, agent Dockerfile
        ├── solution/    # Original source and Oracle restoration script
        └── tests/       # Reference and isolated verifier Dockerfile/scripts
```

## Grading

The agent's module artifact is copied into a **separate verifier container**.
The reference and grader are built only into that container, never into the agent
image. Only `[verifier.env]` requests the judge's `OPENAI_API_KEY` from the host.
There is no key in a task file, Docker build argument, or source snapshot.

Before spending API tokens, the verifier rejects:

- Invalid Go, missing targets, missing declaration/field docs, or detached docs.
- A declaration comment that does not introduce its name (an article is allowed).
- Changed code, unrelated comments, or other files; added files or symlinks.
- Compiler or line directives inserted as documentation.

Whitespace changes in the edited file are allowed; literal and comment contents
outside the requested docs must stay unchanged. The verifier parses but does not
execute candidate Go code.

A valid submission is sent to OpenAI's
[`POST /v1/decisions`](https://developers.openai.com/api/docs/guides/decisions.md)
using `gpt-6-luna`. Each declaration or field comment has an independent `score`
question with ordered levels from 0 (incorrect) to 4 (semantically equivalent or
better). Questions share a request, but each reference defines its own required
scope. Paraphrases are valid; missing contracts and unsupported promises lose
credit. Candidate text and source are treated as untrusted data, not instructions.

The input contains the stripped target declaration and paired comments, not the
whole source file. Whole-file context reduced identical-reference scores in the
initial live calibration; the agent still sees the surrounding module. The judge
can assess extra claims against the declaration, but cannot independently verify
every dependency's behavior. Human reference review remains necessary.

The Decisions score is a **probability-weighted level index**, not a chosen integer
or confidence value. Divide each score by 4, then take the mean over comments:

```json
{"doc_quality": 0.92}
```

The verifier writes that result to `/logs/verifier/reward.json`. It also saves the
request, response (including probabilities, confidence, and usage), per-comment
scores, and structural gate result. Missing docs or forbidden edits produce zero;
API authentication, availability, and malformed-response failures abort without
a reward. Transient API errors are retried at most three times. There is no silent
fallback to Responses or another judge.

## Credentials and live calibration

The repository-root `.env` contains `OPENAI_API_KEY`, is ignored, and should have
permissions `0600`. Do not commit it, copy it into a task, or print its contents.
Use [`.env.example`](.env.example) only as a variable-name reference.

This command makes **six paid requests** using the stored key. It uses only
development examples: reference, paraphrase, superficial description,
contradiction, prompt injection, and a multi-question struct reference.

```sh
go run ./evals/golang-docs validate --live --env-file .env
```

Reports are saved under `.cache/validation/`. Diagnostic ranges are smoke-test
checks, not calibrated pass/fail thresholds for agent submissions. Identical
references need not score exactly 1.0. This is a small initial calibration set;
review more human-labeled paraphrases, omissions, and hallucinations before using
judge scores to decide whether a skill improves documentation.

## Run with Harbor

Docker needs a running daemon accessible to the current user. The Linux runtime
also needs Harbor's nftables egress-control support. Agent setup uses public
network access; during the agent phase only `api.openai.com` and
`api.anthropic.com` are allowed, blocking GitHub/pkg.go.dev answer retrieval.
The separate verifier only permits `api.openai.com`. For another inference
provider, add only its required inference endpoints rather than opening GitHub.

Use the Go `run` command for local Docker runs. It invokes external Harbor
`0.24.0` on `PATH`, or falls back to `uvx --from harbor==0.24.0 harbor`. Harbor
itself is Python; that dependency remains outside the repository's tooling and
the verifier image. There is no project Python environment or lockfile to install.

Harbor 0.24's egress rules blocked Docker's embedded resolver from forwarding to
its configured upstream on this host. The Go runner places an ephemeral Docker
CLI shim in Harbor's child `PATH`. After successful compose startup or allowlist
updates, it locates that eval project's sidecar, reads Docker's `ExtServers`
resolver IPs, and permits only UDP/TCP port 53 to those IPs in the sidecar's
network namespace. All other Docker commands pass through unchanged. Public and
no-network policies remain unchanged, as do host firewall rules and HTTP
allowlists. The original live probe confirmed OpenAI was reachable while GitHub
HTTPS remained blocked. Absolute job paths avoid Compose artifact-copy errors.

If BB still reports socket permission errors after adding your account to the
`docker` group, its background process may have retained its original groups.
A refreshed login process fixes that. With explicit approval, run the Go command
through `sudo -n -u spachava -- /usr/bin/env PATH="$PATH"` to refresh groups while
preserving access to the Go and external Harbor executables as the same user. Do not change socket permissions or run Harbor as root.

The agent image is `golang:1.27.1-bookworm`, with dependencies cached by
`go mod download`. A multi-stage verifier build compiles the entire Go grader
with `CGO_ENABLED=0` in that image, then runs the static binary in
`debian:bookworm-slim` with CA certificates. No Python runs in the verifier.
These are versioned tags, not digest pins.
Tasks request 1 CPU, 2 GiB agent memory, 512 MiB verifier memory, and 300-second
agent/verifier timeouts.

```sh
# Reference restoration followed by real Decisions grading.
go run ./evals/golang-docs run \
  -p evals/golang-docs/tasks -a oracle --env-file .env -n 2 -y

# Missing-doc negative control; the gate should return zero without API calls.
go run ./evals/golang-docs run \
  -p evals/golang-docs/tasks -a nop --env-file .env -n 2 -y

# Development baseline; choose an available OpenAI model.
go run ./evals/golang-docs run \
  -p evals/golang-docs/tasks -i 'jsonschema-*' \
  -a terminus-2 -m 'openai/<model>' --env-file .env -n 2 -y
```

The `-y` flag confirms forwarding the verifier key. Do not add `--upload`,
`--launch`, or sharing flags without authorization. Agent-provider credentials
are separate from the verifier configuration. Future skill comparisons can add
`--skills skills/golang-docs` once that skill exists; use the same model, attempts,
timeouts, and task set in both conditions.

## End-to-end validation

On 2026-10-07, the original implementation's controls ran across all 12 tasks
with Harbor 0.24.0 and Docker 29.7.2:

- Oracle: 12 completed trials, no exceptions, mean `doc_quality` **0.9310**
  (range **0.8575–0.9775**). These restored references are probabilistic positive
  controls, not a model-generated documentation baseline.
- No-op: 12 completed trials, no exceptions, all scores **0**, no Decisions calls.

The Go migration reproduces all 12 reference records, stripped declarations,
token fingerprints, and snapshot file hashes exactly. Go regression tests cover
AST association, structural gates, request/response validation, HTTP retries,
credential-safe errors, archive filtering, generation, and scoped DNS rules.
A Go-verifier Oracle smoke run completed with no exceptions and scored **0.95**
(`jobs/go-oracle-smoke-20261007/`). The Go no-op control then completed all 12
tasks with no exceptions, all scores **0**, and no Decisions calls
(`jobs/go-nop-controls-20261007/`). Repository race tests, `go vet`, and the
`laas` analyzers pass.

Local reports are under `jobs/oracle-controls-20261007-0052/` and
`jobs/nop-dns-controls-20261007-0052/`. No results were uploaded or published.

## Limits and next steps

- Public repositories can still be memorized. Low popularity is not evidence
  of exclusion from a model's training data. Pinning and blocking retrieval only
  address reproducibility and direct answer lookup, not training contamination.
- Nearby comments and examples remain intentional context. Some answers can be
  inferred from them; this is not a blind reconstruction benchmark.
- Upstream comments can be incomplete or inaccurate. For example, `For` was not
  selected because its opening paragraph is detached from the declaration's AST
  doc group. Audit reference facts against code before adding targets.
- Mean struct scores can hide one poor field. Inspect per-comment scores and
  confidence, particularly for security, ownership, and concurrency claims.
- Keep the MCP holdout out of skill/rubric tuning. Expand to more repositories
  and packages before drawing conclusions from this 12-task pilot.
- Container Oracle/no-op controls now pass. Run real model-generated development
  baselines before writing the skill; those have not been run yet.

References: [Harbor task format](https://docs.harborframework.com/core-concepts/tasks/overview),
[separate verifier](https://docs.harborframework.com/core-concepts/tasks/separate-verifier),
[network policy](https://docs.harborframework.com/core-concepts/tasks/network-policies),
[Decisions guide](https://developers.openai.com/api/docs/guides/decisions.md).
The official [`create-task` skill](https://skills.sh/harbor-framework/harbor/create-task)
is installed project-locally under `.agents/skills/create-task/`, with its source
recorded in `skills-lock.json`.
