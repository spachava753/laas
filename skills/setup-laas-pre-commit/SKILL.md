---
name: setup-laas-pre-commit
description: Set up or integrate a Git pre-commit hook that runs all laas Go analyzers. Use when adding laas linting before commits, creating tracked Git hooks, or wiring laas into an existing hook manager.
license: MIT
compatibility: Requires Git, a Go module, and a Go toolchain with go get -tool and go tool support. A POSIX-compatible shell is needed for a direct Git hook.
metadata:
  author: spachava753
---

# Set up laas pre-commit linting

Configure the target Go repository so every commit runs `laas` across the module. Preserve existing hook behavior and pin the tool through the module whenever possible.

## Guardrails

- Read the target repository's `AGENTS.md` and relevant instructions before editing.
- Inspect existing worktree changes and never overwrite or revert unrelated work.
- Extend an existing hook or hook manager instead of installing a competing mechanism.
- Run all analyzers with `go tool laas ./...`; do not select individual analyzers unless the user asks.
- Do not add exclusions, weaken limits, or fix reported code merely to make the new hook pass.
- Do not commit the setup unless the user asks for a commit.

## Inspect the repository

Confirm that the working directory is a Git repository with a Go module:

```sh
git rev-parse --show-toplevel
git status --short
go env GOMOD
git config --get core.hooksPath
```

Stop and explain the missing prerequisite if Git reports no worktree or `go env GOMOD` returns `/dev/null`.

Look for existing hook mechanisms before changing anything:

- `.pre-commit-config.yaml` or `.pre-commit-config.yml`
- `.githooks/`, `.git-hooks/`, or another path from `core.hooksPath`
- `.husky/pre-commit`
- `lefthook.yml` or `.lefthook.yml`
- `.git/hooks/pre-commit`
- Bootstrap scripts, Make targets, or development setup documentation that activate hooks

Read any discovered configuration and preserve every existing command.

## Pin laas

Prefer a Go tool directive so the hook does not depend on a globally installed binary. If `go.mod` already declares `github.com/spachava753/laas/cmd/laas` as a tool, retain its current version unless the user requests an update.

Otherwise run:

```sh
go get -tool github.com/spachava753/laas/cmd/laas@latest
```

Inspect the resulting `go.mod` and `go.sum` diff. Do not silently retain unrelated dependency changes or an unexpected Go or toolchain version change. Explain such a change and ask the user before proceeding if it alters the project's stated compatibility.

If the project's Go version does not support tool directives, ask before choosing a fallback such as a version-pinned `go run` command or a global installation. Never put an unpinned `@latest` invocation in the hook.

## Integrate the hook

Use the repository's existing hook manager when one exists. Add this command at the appropriate pre-commit stage:

```sh
go tool laas ./...
```

For an existing `pre-commit` configuration, add an equivalent local hook while preserving all current entries:

```yaml
- repo: local
  hooks:
    - id: laas
      name: laas
      entry: go tool laas
      args: [./...]
      language: system
      pass_filenames: false
      always_run: true
```

Run `pre-commit install` after editing that configuration if the command is available and the repository does not already install it through a bootstrap process.

When no hook mechanism exists, create a tracked `.githooks/pre-commit` file:

```sh
#!/bin/sh
set -eu

root=$(git rev-parse --show-toplevel)
cd "$root"

go tool laas ./...
```

Make it executable and activate the tracked hooks directory locally:

```sh
chmod +x .githooks/pre-commit
git config --local core.hooksPath .githooks
```

If `.git/hooks/pre-commit` already exists, do not switch `core.hooksPath` and bypass it. Ask before migrating its contents or modify the existing mechanism when the user explicitly wants a local-only hook.

Because `core.hooksPath` is local Git configuration, add a short setup step to the repository's existing bootstrap process or development documentation:

```sh
git config --local core.hooksPath .githooks
```

## Verify the setup

Run the pinned analyzer directly:

```sh
go tool laas ./...
```

Then run the configured pre-commit entry point. Use `pre-commit run laas --all-files` for the `pre-commit` framework or execute the active hook script directly for a plain Git hook.

A lint diagnostic proves the hook invoked `laas`, but it also means commits will be blocked until the code is corrected. Report those diagnostics without introducing exclusions or unrelated code changes.

Finally verify:

- The hook retains all checks that existed before this task.
- A tracked hook has executable mode in Git.
- `go.mod`, `go.sum`, hook configuration, and setup documentation contain only intended changes.
- `git diff --check` passes.
- The final response states how the hook is activated and whether current code passes it.
