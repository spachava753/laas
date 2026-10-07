# Go documentation evals

This directory builds and runs the Harbor dataset used to evaluate the general
`golang-docs` skill. Read `README.md` for tooling and `EXPERIMENT.md` for the fixed
comparison protocol and refinement history.

- `manifest.json` pins public upstream commits and archive hashes. Keep development and holdout examples separated by repository.
- Repository-owned tooling and tests are Go, using the standard library. Harbor is an external CLI dependency, not an imported Python API.
- Use Go's parser, not regexes, to identify declarations and associated comments. AST inspection is in `inspect.go`.
- Generated `tasks/`, `.cache/`, `.venv/`, and `jobs/` are intentionally ignored. Do not allowlist upstream Go snapshots or reference comments.
- Ground truth and credentials belong only in the separate verifier, never in the agent image. Keep Oracle answers under `solution/`.
- Use `go run ./evals/golang-docs run` from the repository root for local Docker trials. `run.go` supplies absolute job paths and an ephemeral Docker CLI shim for Harbor 0.24's embedded DNS workaround. Keep it scoped to eval task sidecars and configured resolver IPs on UDP/TCP port 53; never fix connectivity by opening the agent's HTTP allowlist or editing installed Harbor code.
- API errors are infrastructure failures, not zero-quality documentation. Never replace the Decisions API with another grader silently.
- Keep model, effort, harness version, source snapshots, rubric, and timeouts fixed across skill comparisons. Snapshot every skill revision before launch, record its commit, and keep holdout results out of tuning.
- Commit only sanitized result aggregates and general observations. Do not put task identifiers, literal paths, reference text, or judge-specific instructions in the skill.
- Do not read or print secret-bearing `.env` files. Live grading requires the user's authorization to use the OpenAI credential.
- The public upstream docs are reference answers, not proof against memorization or an infallible specification. Review suspicious examples before expanding the dataset.
