# AGENTS.md

## Project Overview

- This repository contains the Go module `github.com/spachava753/laas`.
- The project is greenfield. Keep changes focused and avoid adding architecture or dependencies before they are needed.
- Go source files may live at the repository root or in conventional `cmd`, `internal`, and `pkg` directories as the project develops.

## Development Commands

Run these checks before considering a change complete:

```sh
go fmt ./...
go vet ./...
go test ./...
```

Run `go mod tidy` after changing imports or dependencies, and include the resulting `go.mod` and `go.sum` changes.

## Coding Conventions

- Follow standard Go conventions and keep code compatible with the Go version declared in `go.mod`.
- Prefer the standard library unless an external dependency materially simplifies the implementation.
- Keep packages cohesive, package names short, and exported APIs documented.
- Place tests alongside the code they cover in `_test.go` files. Prefer table-driven tests when multiple cases share the same setup.
- Return errors with enough context to identify the failed operation; avoid logging and returning the same error at the same layer.
- Use `gofmt` rather than hand-formatting Go code.

## Repository Hygiene

- `.gitignore` is an allowlist: files are ignored unless an explicit negation pattern includes them.
- When adding a required non-Go file type, update `.gitignore` in the same change so the file can be tracked.
- Do not commit generated binaries, local secrets, editor state, coverage output, or temporary files.
- Keep the README current when setup steps or user-facing behavior changes.
