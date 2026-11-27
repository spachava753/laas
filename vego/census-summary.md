# The census of vego (F41)

The output of `vegocensus summary` on the census files of the run recorded in vego/ROADMAP.md, "What stops vego on real code" (laas at 8df7903, and 7a4f7d2 for std; 2026-11-27). The corpora: laas, without its vego package, whose functions are counted not looked at; the trial at 7746bd0 without findings/; the standard library of go1.27.3 without cmd, runtime, internal, vendor, syscall, unsafe, and text/template; and the 33 modules of vego/census.list. The last section weighs each module equally and leaves laas out, as the orchestrator ruled.

A function that gets through met no refusal of vego on the weakest contract, `// @Ensures True`; it is not verified. The census ran as a project that declares `sizes` and `inputs` in its trust file, and proved nothing.

## Corpus laas

- functions with a body: 2019, of which not loaded: 1632
- get through: 170 (8.4%), of which 0 only past refusals made when a proof fails
- not looked at in full (a statement no attempt entered, or the census stopped): 1, with 5 statements not entered
- reach what only a declaration of the trust file allows: 23
- assume a callee, method, or function type of the module with the weakest contract: 254

### Refusals by class

| class | functions stopped | stopped alone | first cause | not looked at in full | top details (stopped, alone) |
| --- | --- | --- | --- | --- | --- |
| `package:not-loaded` | 1632 | 0 | 1632 | 1632 |  |
| `no-entry:std` | 129 | 42 | 92 | 0 | `(*go/types.object).Type` (18, 0); `(*go/types.object).Name` (14, 0); `go/ast.Unparen` (9, 0) |
| `recursion:through-call` | 63 | 9 | 18 | 0 | `(*strings.Replacer).Replace` (12, 6); `(*go/types.object).Type` (9, 0); `(*sync/atomic.Pointer[T]).Load` (8, 1) |
| `recursion:through-method` | 28 | 10 | 20 | 0 | `(github.com/spachava753/laas/vego/internal/logic.Env).Qualified` (23, 7); `(github.com/spachava753/laas/vego/internal/logic.Env).Path` (4, 0); `(github.com/spachava753/laas/vego/internal/logic.Typer).PathType` (3, 0) |
| `expr:index` | 26 | 0 | 8 | 0 | `map[*go/ast.Ident]go/types.Object` (9, 0); `map[*go/ast.SelectorExpr]*go/types.Selection` (3, 0); `map[*go/types.Func]*github.com/spachava753/laas/vego.funcInfo` (3, 0) |
| `type:map-key` | 25 | 2 | 19 | 0 | `map[*github.com/spachava753/laas/cmd/vegocensus.fn]float64` (9, 2); `map[go/types.Type]bool` (6, 0); `map[*go/types.Var][]go/types.Type` (2, 0) |
| `assign:target` | 24 | 0 | 3 | 0 |  |
| `error:unknown-origin` | 24 | 4 | 5 | 0 | `formatted` (14, 3); `errors.Is` (7, 0); `Error called` (4, 1) |
| `iface-method:no-contract` | 19 | 1 | 1 | 0 | `(go/types.Type).Underlying` (8, 0); `(go/ast.Node).Pos` (6, 1); `(go/ast.Node).End` (3, 0) |
| `func-value:no-contract` | 18 | 1 | 1 | 0 | `func(*golang.org/x/tools/go/analysis.Pass) (any, error)` (4, 0); `func()` (3, 1); `func(fact golang.org/x/tools/go/analysis.Fact)` (2, 0) |
| `recursion:through-value` | 18 | 0 | 4 | 0 | `paused` (7, 0); `range over kinds` (4, 0); `read` (2, 0) |
| `global:read` | 15 | 1 | 5 | 0 |  |
| `handover:unknown-code` | 12 | 0 | 1 | 0 |  |
| `append:in-expression` | 11 | 0 | 2 | 0 |  |
| `channel:use` | 10 | 0 | 1 | 0 | `<-chan struct{}` (8, 0); `<-chan time.Time` (3, 0); `chan struct{}` (3, 0) |
| `format:runs-code` | 10 | 1 | 1 | 0 |  |
| `generic:iterator` | 9 | 0 | 1 | 0 |  |
| `dyntype:assert` | 8 | 0 | 3 | 0 |  |
| `generic:type-args` | 7 | 1 | 3 | 0 |  |
| `convert:to-error` | 6 | 0 | 0 | 0 |  |
| `generic:method-call` | 6 | 0 | 1 | 0 |  |
| `no-entry:other` | 6 | 0 | 2 | 0 | `(*golang.org/x/tools/go/analysis.Pass).ReportRangef` (4, 0); `github.com/fzipp/gocyclo.Complexity` (1, 0); `golang.org/x/tools/go/analysis/checker.Analyze` (1, 0) |
| `recover:call` | 5 | 1 | 1 | 0 |  |
| `select:statement` | 5 | 0 | 1 | 0 |  |
| `stmt:range-other` | 5 | 0 | 0 | 0 | `map[string][2]float64` (2, 0); `map[*go/ast.Ident]go/types.Object` (1, 0); `map[*go/types.Var][]go/types.Type` (1, 0) |
| `assign:multi-value` | 4 | 0 | 2 | 0 |  |
| `contract:unusable` | 4 | 0 | 3 | 0 |  |
| `type:array-elem` | 4 | 1 | 1 | 0 | `[2]float64` (2, 0); `[2]int` (2, 1) |
| `call:builtin` | 3 | 0 | 0 | 0 | `close` (3, 0) |
| `convert:value` | 3 | 2 | 2 | 0 | `string to []rune` (3, 1); `[]rune to string` (1, 0) |
| `dyntype:errors-as` | 3 | 0 | 1 | 0 |  |
| `generic:called` | 3 | 0 | 1 | 0 | `github.com/spachava753/laas/evals/golang-docs.sortedKeys` (3, 0) |
| `json:decode` | 3 | 2 | 2 | 0 |  |
| `pointer:to-non-struct` | 3 | 1 | 2 | 0 | `**regexp.Regexp` (1, 0); `*[]string` (1, 0); `*map[string]float64` (1, 1) |
| `call:initialiser-only` | 2 | 0 | 0 | 0 |  |
| `closure:recursive` | 2 | 0 | 2 | 0 |  |
| `convert:iface-array` | 2 | 0 | 0 | 0 |  |
| `convert:iface-no-contract` | 2 | 0 | 0 | 0 | `(go/types.Object).Exported` (2, 0) |
| `func-literal:signature` | 2 | 0 | 2 | 0 |  |
| `goroutine:go` | 2 | 0 | 0 | 0 |  |
| `json:encode` | 2 | 0 | 2 | 0 |  |
| `json:form` | 2 | 0 | 0 | 0 |  |
| `stmt:expression` | 2 | 0 | 0 | 0 |  |
| `type:array` | 2 | 2 | 2 | 0 | `[5]string` (1, 1); `[6]string` (1, 1) |
| `type:array-in-struct` | 2 | 0 | 1 | 0 | `*syscall.Stat_t` (1, 0); `github.com/spachava753/laas/evals/golang-docs.calibrationResult` (1, 0) |
| `convert:iface-foreign-impl` | 1 | 0 | 0 | 0 |  |
| `convert:iface-no-contract-other` | 1 | 0 | 0 | 0 | `(golang.org/x/tools/go/analysis.Fact).AFact` (1, 0) |
| `copy:elements` | 1 | 0 | 0 | 0 |  |
| `format:slice-pack` | 1 | 0 | 0 | 0 |  |
| `func-value:calls-values` | 1 | 0 | 0 | 0 |  |
| `generic:declared` | 1 | 0 | 1 | 1 |  |
| `no-entry:impossible` | 1 | 0 | 0 | 0 | `io.Copy` (1, 0) |

### Refusals by group

| group | functions stopped | stopped alone | first cause | not looked at in full | top details (stopped, alone) |
| --- | --- | --- | --- | --- | --- |
| `package` | 1632 | 0 | 1632 | 1632 |  |
| `no-entry` | 129 | 44 | 94 | 0 |  |
| `recursion` | 94 | 21 | 42 | 0 |  |
| `type` | 30 | 5 | 23 | 0 |  |
| `expr` | 26 | 0 | 8 | 0 |  |
| `assign` | 25 | 1 | 5 | 0 |  |
| `error` | 24 | 4 | 5 | 0 |  |
| `generic` | 24 | 1 | 7 | 1 |  |
| `func-value` | 19 | 1 | 1 | 0 |  |
| `iface-method` | 19 | 1 | 1 | 0 |  |
| `global` | 15 | 1 | 5 | 0 |  |
| `convert` | 14 | 2 | 2 | 0 |  |
| `handover` | 12 | 0 | 1 | 0 |  |
| `append` | 11 | 0 | 2 | 0 |  |
| `dyntype` | 11 | 0 | 4 | 0 |  |
| `format` | 11 | 1 | 1 | 0 |  |
| `channel` | 10 | 0 | 1 | 0 |  |
| `stmt` | 7 | 0 | 0 | 0 |  |
| `json` | 6 | 2 | 4 | 0 |  |
| `call` | 5 | 0 | 0 | 0 |  |
| `recover` | 5 | 1 | 1 | 0 |  |
| `select` | 5 | 0 | 1 | 0 |  |
| `contract` | 4 | 0 | 3 | 0 |  |
| `pointer` | 3 | 1 | 2 | 0 |  |
| `closure` | 2 | 0 | 2 | 0 |  |
| `func-literal` | 2 | 0 | 2 | 0 |  |
| `goroutine` | 2 | 0 | 0 | 0 |  |
| `copy` | 1 | 0 | 0 | 0 |  |

### Greedy order of classes

Get through with nothing fixed: 170.

| step | fixed | let through by it | let through in all |
| --- | --- | --- | --- |
| 1 | `no-entry:std` | 42 | 212 |
| 2 | `recursion:through-call` | 15 | 227 |
| 3 | `recursion:through-method` | 10 | 237 |
| 4 | `error:unknown-origin` | 9 | 246 |
| 5 | `expr:index` | 6 | 252 |
| 6 | `type:map-key` | 7 | 259 |
| 7 | `func-value:no-contract` | 6 | 265 |
| 8 | `global:read` | 7 | 272 |
| 9 | `recursion:through-value` | 6 | 278 |
| 10 | `assign:target` | 5 | 283 |
| 11 | `append:in-expression` | 4 | 287 |
| 12 | `handover:unknown-code` | 5 | 292 |
| 13 | `dyntype:assert` | 7 | 299 |
| 14 | `contract:unusable` | 4 | 303 |
| 15 | `generic:type-args` | 4 | 307 |
| 16 | `iface-method:no-contract` | 5 | 312 |
| 17 | `format:runs-code` | 6 | 318 |
| 18 | `generic:iterator` | 6 | 324 |
| 19 | `no-entry:other` | 5 | 329 |
| 20 | `assign:multi-value` | 3 | 332 |

### Greedy order of groups

Get through with nothing fixed: 170.

| step | fixed | let through by it | let through in all |
| --- | --- | --- | --- |
| 1 | `no-entry` | 44 | 214 |
| 2 | `recursion` | 29 | 243 |
| 3 | `type` | 10 | 253 |
| 4 | `error` | 9 | 262 |
| 5 | `expr` | 8 | 270 |
| 6 | `assign` | 8 | 278 |
| 7 | `global` | 7 | 285 |
| 8 | `func-value` | 8 | 293 |
| 9 | `generic` | 7 | 300 |
| 10 | `iface-method` | 12 | 312 |
| 11 | `convert` | 7 | 319 |
| 12 | `format` | 9 | 328 |
| 13 | `json` | 5 | 333 |
| 14 | `append` | 5 | 338 |
| 15 | `handover` | 6 | 344 |
| 16 | `dyntype` | 9 | 353 |
| 17 | `stmt` | 5 | 358 |
| 18 | `channel` | 4 | 362 |
| 19 | `contract` | 4 | 366 |
| 20 | `call` | 3 | 369 |

### Greedy order of classes, with what the project writes for other modules (no-entry:other and the classes ending in -other) left out of the causes

Get through with nothing fixed: 170.

| step | fixed | let through by it | let through in all |
| --- | --- | --- | --- |
| 1 | `no-entry:std` | 44 | 214 |
| 2 | `recursion:through-call` | 16 | 230 |
| 3 | `recursion:through-method` | 10 | 240 |
| 4 | `error:unknown-origin` | 9 | 249 |
| 5 | `expr:index` | 6 | 255 |
| 6 | `type:map-key` | 7 | 262 |
| 7 | `func-value:no-contract` | 6 | 268 |
| 8 | `global:read` | 7 | 275 |
| 9 | `recursion:through-value` | 6 | 281 |
| 10 | `assign:target` | 5 | 286 |
| 11 | `iface-method:no-contract` | 5 | 291 |
| 12 | `generic:iterator` | 7 | 298 |
| 13 | `format:runs-code` | 6 | 304 |
| 14 | `append:in-expression` | 4 | 308 |
| 15 | `handover:unknown-code` | 5 | 313 |
| 16 | `dyntype:assert` | 7 | 320 |
| 17 | `generic:type-args` | 5 | 325 |
| 18 | `contract:unusable` | 4 | 329 |
| 19 | `type:array-elem` | 4 | 333 |
| 20 | `assign:multi-value` | 3 | 336 |

### Greedy order of groups, with what the project writes for other modules (no-entry:other and the classes ending in -other) left out of the causes

Get through with nothing fixed: 170.

| step | fixed | let through by it | let through in all |
| --- | --- | --- | --- |
| 1 | `no-entry` | 44 | 214 |
| 2 | `recursion` | 29 | 243 |
| 3 | `type` | 10 | 253 |
| 4 | `error` | 9 | 262 |
| 5 | `expr` | 8 | 270 |
| 6 | `assign` | 11 | 281 |
| 7 | `global` | 7 | 288 |
| 8 | `func-value` | 8 | 296 |
| 9 | `generic` | 8 | 304 |
| 10 | `iface-method` | 12 | 316 |
| 11 | `convert` | 8 | 324 |
| 12 | `format` | 9 | 333 |
| 13 | `json` | 5 | 338 |
| 14 | `append` | 5 | 343 |
| 15 | `handover` | 6 | 349 |
| 16 | `dyntype` | 9 | 358 |
| 17 | `contract` | 4 | 362 |
| 18 | `call` | 3 | 365 |
| 19 | `channel` | 3 | 368 |
| 20 | `pointer` | 3 | 371 |

### Callees without an entry

| callee | class | functions stopped | stopped alone |
| --- | --- | --- | --- |
| `(*go/types.object).Type` | `no-entry:std` | 18 | 0 |
| `(*go/types.object).Name` | `no-entry:std` | 14 | 0 |
| `go/ast.Unparen` | `no-entry:std` | 9 | 0 |
| `(*go/types.Info).TypeOf` | `no-entry:std` | 8 | 1 |
| `os.Stat` | `no-entry:std` | 8 | 0 |
| `(*go/token.FileSet).Position` | `no-entry:std` | 6 | 0 |
| `(*go/types.Package).Path` | `no-entry:std` | 6 | 0 |
| `(*sync.Cond).Broadcast` | `no-entry:std` | 6 | 1 |
| `go/ast.Inspect` | `no-entry:std` | 6 | 0 |
| `(*go/types.Package).Scope` | `no-entry:std` | 5 | 0 |
| `go/types.ExprString` | `no-entry:std` | 5 | 0 |
| `os.Lstat` | `no-entry:std` | 5 | 1 |
| `(*golang.org/x/tools/go/analysis.Pass).ReportRangef` | `no-entry:other` | 4 | 0 |
| `(*go/ast.FuncDecl).Pos` | `no-entry:std` | 4 | 0 |
| `(*go/ast.Ident).Pos` | `no-entry:std` | 4 | 0 |
| `(*go/types.Func).Pkg` | `no-entry:std` | 4 | 0 |
| `(*go/types.object).Pkg` | `no-entry:std` | 4 | 0 |
| `(*os/exec.Cmd).Run` | `no-entry:std` | 4 | 0 |
| `(*sync/atomic.Bool).Load` | `no-entry:std` | 4 | 0 |
| `go/types.Identical` | `no-entry:std` | 4 | 0 |
| `os.MkdirTemp` | `no-entry:std` | 4 | 0 |
| `os.RemoveAll` | `no-entry:std` | 4 | 0 |
| `os/exec.CommandContext` | `no-entry:std` | 4 | 0 |
| `path/filepath.FromSlash` | `no-entry:std` | 4 | 1 |
| `(*bytes.Reader).Read` | `no-entry:std` | 3 | 0 |
| `(*flag.FlagSet).IntVar` | `no-entry:std` | 3 | 0 |
| `(*flag.FlagSet).Parse` | `no-entry:std` | 3 | 0 |
| `(*flag.FlagSet).String` | `no-entry:std` | 3 | 0 |
| `(*go/ast.CommentGroup).Pos` | `no-entry:std` | 3 | 0 |
| `(*go/ast.File).Pos` | `no-entry:std` | 3 | 0 |
| `(*go/ast.FuncDecl).End` | `no-entry:std` | 3 | 0 |
| `(*go/types.Array).Elem` | `no-entry:std` | 3 | 0 |
| `(*go/types.Pointer).Elem` | `no-entry:std` | 3 | 0 |
| `(*go/types.Selection).Obj` | `no-entry:std` | 3 | 0 |
| `(*go/types.Signature).Params` | `no-entry:std` | 3 | 0 |
| `(*go/types.Signature).Recv` | `no-entry:std` | 3 | 0 |
| `(*go/types.Signature).Results` | `no-entry:std` | 3 | 0 |
| `(*go/types.Tuple).At` | `no-entry:std` | 3 | 0 |
| `(*go/types.Tuple).Len` | `no-entry:std` | 3 | 0 |
| `(*math/big.Int).Int64` | `no-entry:std` | 3 | 0 |
| `(*math/big.Int).IsInt64` | `no-entry:std` | 3 | 0 |
| `(*math/big.Int).String` | `no-entry:std` | 3 | 2 |
| `(*os.Process).Kill` | `no-entry:std` | 3 | 0 |
| `(*os/exec.Cmd).Output` | `no-entry:std` | 3 | 0 |
| `(*sync/atomic.Bool).Store` | `no-entry:std` | 3 | 0 |
| `(*sync/atomic.Int64).Load` | `no-entry:std` | 3 | 1 |
| `bytes.NewReader` | `no-entry:std` | 3 | 0 |
| `flag.NewFlagSet` | `no-entry:std` | 3 | 0 |
| `go/token.NewFileSet` | `no-entry:std` | 3 | 0 |
| `os/exec.Command` | `no-entry:std` | 3 | 0 |

## Corpus trial

- functions with a body: 154, of which not loaded: 0
- get through: 126 (81.8%), of which 1 only past refusals made when a proof fails
- not looked at in full (a statement no attempt entered, or the census stopped): 1, with 5 statements not entered
- reach what only a declaration of the trust file allows: 7
- assume a callee, method, or function type of the module with the weakest contract: 0

### Refusals by class

| class | functions stopped | stopped alone | first cause | not looked at in full | top details (stopped, alone) |
| --- | --- | --- | --- | --- | --- |
| `no-entry:std` | 9 | 1 | 5 | 0 | `flag.Parse` (2, 0); `(*bufio.Scanner).Buffer` (1, 0); `(*encoding/json.Decoder).DisallowUnknownFields` (1, 0) |
| `iface-method:no-contract` | 8 | 6 | 6 | 0 | `(sort.Interface).Len` (5, 2); `(sort.Interface).Swap` (4, 0); `(sort.Interface).Less` (2, 0) |
| `error:unknown-origin` | 7 | 1 | 1 | 0 | `formatted` (6, 1); `Error called` (1, 0) |
| `convert:iface-array` | 3 | 3 | 3 | 0 |  |
| `global:read` | 3 | 0 | 0 | 0 |  |
| `no-entry:other` | 3 | 0 | 1 | 0 | `(*github.com/modelcontextprotocol/go-sdk/mcp.Server).Run` (1, 0); `github.com/modelcontextprotocol/go-sdk/mcp.AddTool` (1, 0); `github.com/modelcontextprotocol/go-sdk/mcp.NewServer` (1, 0) |
| `recursion:through-method` | 3 | 3 | 3 | 0 | `(io.Writer).Write` (2, 2); `(io.Reader).Read` (1, 1) |
| `json:encode` | 2 | 0 | 2 | 0 |  |
| `json:form` | 2 | 0 | 1 | 0 |  |
| `append:in-expression` | 1 | 0 | 0 | 0 |  |
| `call:initialiser-only` | 1 | 0 | 0 | 0 |  |
| `convert:iface-foreign-impl` | 1 | 0 | 0 | 0 |  |
| `format:runs-code` | 1 | 0 | 0 | 0 |  |
| `func-value:no-contract` | 1 | 0 | 0 | 0 | `func(*golang.org/x/tools/go/analysis.Pass) (any, error)` (1, 0) |
| `generic:called` | 1 | 0 | 0 | 0 |  |
| `generic:declared` | 1 | 0 | 1 | 1 |  |
| `generic:iterator` | 1 | 0 | 0 | 0 |  |
| `global:type` | 1 | 0 | 1 | 0 |  |
| `handover:apart` | 1 | 0 | 0 | 0 |  |
| `handover:unknown-code` | 1 | 0 | 1 | 0 |  |
| `json:decode` | 1 | 1 | 1 | 0 |  |
| `pointer:to-non-struct` | 1 | 1 | 1 | 0 | `*map[string]float64` (1, 1) |
| `scoped:kept` | 1 | 0 | 1 | 0 |  |

### Refusals by group

| group | functions stopped | stopped alone | first cause | not looked at in full | top details (stopped, alone) |
| --- | --- | --- | --- | --- | --- |
| `no-entry` | 9 | 1 | 6 | 0 |  |
| `iface-method` | 8 | 6 | 6 | 0 |  |
| `error` | 7 | 1 | 1 | 0 |  |
| `convert` | 4 | 3 | 3 | 0 |  |
| `global` | 4 | 0 | 1 | 0 |  |
| `json` | 4 | 1 | 4 | 0 |  |
| `generic` | 3 | 0 | 1 | 1 |  |
| `recursion` | 3 | 3 | 3 | 0 |  |
| `handover` | 2 | 0 | 1 | 0 |  |
| `append` | 1 | 0 | 0 | 0 |  |
| `call` | 1 | 0 | 0 | 0 |  |
| `format` | 1 | 0 | 0 | 0 |  |
| `func-value` | 1 | 0 | 0 | 0 |  |
| `pointer` | 1 | 1 | 1 | 0 |  |
| `scoped` | 1 | 0 | 1 | 0 |  |

### Greedy order of classes

Get through with nothing fixed: 126.

| step | fixed | let through by it | let through in all |
| --- | --- | --- | --- |
| 1 | `iface-method:no-contract` | 6 | 132 |
| 2 | `convert:iface-array` | 3 | 135 |
| 3 | `recursion:through-method` | 3 | 138 |
| 4 | `error:unknown-origin` | 1 | 139 |
| 5 | `no-entry:std` | 2 | 141 |
| 6 | `global:read` | 1 | 142 |
| 7 | `handover:unknown-code` | 1 | 143 |
| 8 | `json:decode` | 1 | 144 |
| 9 | `json:form` | 1 | 145 |
| 10 | `pointer:to-non-struct` | 1 | 146 |

### Greedy order of groups

Get through with nothing fixed: 126.

| step | fixed | let through by it | let through in all |
| --- | --- | --- | --- |
| 1 | `iface-method` | 6 | 132 |
| 2 | `convert` | 3 | 135 |
| 3 | `recursion` | 3 | 138 |
| 4 | `error` | 1 | 139 |
| 5 | `no-entry` | 2 | 141 |
| 6 | `json` | 2 | 143 |
| 7 | `append` | 1 | 144 |
| 8 | `generic` | 1 | 145 |
| 9 | `global` | 2 | 147 |
| 10 | `handover` | 2 | 149 |
| 11 | `func-value` | 1 | 150 |
| 12 | `pointer` | 1 | 151 |
| 13 | `scoped` | 1 | 152 |

### Greedy order of classes, with what the project writes for other modules (no-entry:other and the classes ending in -other) left out of the causes

Get through with nothing fixed: 126.

| step | fixed | let through by it | let through in all |
| --- | --- | --- | --- |
| 1 | `iface-method:no-contract` | 6 | 132 |
| 2 | `convert:iface-array` | 3 | 135 |
| 3 | `recursion:through-method` | 3 | 138 |
| 4 | `error:unknown-origin` | 1 | 139 |
| 5 | `no-entry:std` | 2 | 141 |
| 6 | `global:read` | 1 | 142 |
| 7 | `func-value:no-contract` | 1 | 143 |
| 8 | `generic:iterator` | 1 | 144 |
| 9 | `handover:unknown-code` | 1 | 145 |
| 10 | `json:decode` | 1 | 146 |
| 11 | `json:form` | 1 | 147 |
| 12 | `pointer:to-non-struct` | 1 | 148 |

### Greedy order of groups, with what the project writes for other modules (no-entry:other and the classes ending in -other) left out of the causes

Get through with nothing fixed: 126.

| step | fixed | let through by it | let through in all |
| --- | --- | --- | --- |
| 1 | `iface-method` | 6 | 132 |
| 2 | `convert` | 3 | 135 |
| 3 | `recursion` | 3 | 138 |
| 4 | `error` | 1 | 139 |
| 5 | `no-entry` | 2 | 141 |
| 6 | `json` | 2 | 143 |
| 7 | `append` | 1 | 144 |
| 8 | `generic` | 1 | 145 |
| 9 | `global` | 2 | 147 |
| 10 | `handover` | 2 | 149 |
| 11 | `func-value` | 1 | 150 |
| 12 | `pointer` | 1 | 151 |
| 13 | `scoped` | 1 | 152 |

### Callees without an entry

| callee | class | functions stopped | stopped alone |
| --- | --- | --- | --- |
| `flag.Parse` | `no-entry:std` | 2 | 0 |
| `(*github.com/modelcontextprotocol/go-sdk/mcp.Server).Run` | `no-entry:other` | 1 | 0 |
| `github.com/modelcontextprotocol/go-sdk/mcp.AddTool` | `no-entry:other` | 1 | 0 |
| `github.com/modelcontextprotocol/go-sdk/mcp.NewServer` | `no-entry:other` | 1 | 0 |
| `github.com/modelcontextprotocol/go-sdk/mcp.NewStreamableHTTPHandler` | `no-entry:other` | 1 | 0 |
| `github.com/spachava753/laas/vego.RefuseCachedRuns` | `no-entry:other` | 1 | 0 |
| `github.com/spachava753/laas/vego.TrustReport` | `no-entry:other` | 1 | 0 |
| `golang.org/x/tools/go/analysis/checker.Analyze` | `no-entry:other` | 1 | 0 |
| `golang.org/x/tools/go/analysis/multichecker.Main` | `no-entry:other` | 1 | 0 |
| `golang.org/x/tools/go/packages.Load` | `no-entry:other` | 1 | 0 |
| `golang.org/x/tools/go/packages.PrintErrors` | `no-entry:other` | 1 | 0 |
| `(*bufio.Scanner).Buffer` | `no-entry:std` | 1 | 0 |
| `(*encoding/json.Decoder).DisallowUnknownFields` | `no-entry:std` | 1 | 0 |
| `(*flag.FlagSet).Output` | `no-entry:std` | 1 | 0 |
| `(*flag.FlagSet).Set` | `no-entry:std` | 1 | 0 |
| `(*go/ast.CommentGroup).Pos` | `no-entry:std` | 1 | 0 |
| `(*go/ast.FuncDecl).End` | `no-entry:std` | 1 | 0 |
| `(*go/ast.FuncDecl).Pos` | `no-entry:std` | 1 | 0 |
| `(*go/token.FileSet).Position` | `no-entry:std` | 1 | 0 |
| `(*go/types.Package).Path` | `no-entry:std` | 1 | 0 |
| `(*net/http.ServeMux).HandleFunc` | `no-entry:std` | 1 | 0 |
| `(reflect.Value).Interface` | `no-entry:std` | 1 | 0 |
| `context.Background` | `no-entry:std` | 1 | 0 |
| `flag.Args` | `no-entry:std` | 1 | 0 |
| `flag.PrintDefaults` | `no-entry:std` | 1 | 0 |
| `flag.Var` | `no-entry:std` | 1 | 0 |
| `go/parser.ParseFile` | `no-entry:std` | 1 | 0 |
| `go/token.NewFileSet` | `no-entry:std` | 1 | 0 |
| `net/http.ListenAndServe` | `no-entry:std` | 1 | 0 |
| `os.Stat` | `no-entry:std` | 1 | 0 |
| `path/filepath.WalkDir` | `no-entry:std` | 1 | 1 |
| `reflect.Zero` | `no-entry:std` | 1 | 0 |

### Refusals made only when a proof fails

A census proves nothing, so it makes these wherever they are reached; the prover would often prove what they ask.

| class | functions met in | the only thing met | top details |
| --- | --- | --- | --- |
| `handover:apart-unproved` | 1 | 1 |  |

## Corpus std

- functions with a body: 10825, of which not loaded: 116
- get through: 4743 (43.8%), of which 1 only past refusals made when a proof fails
- not looked at in full (a statement no attempt entered, or the census stopped): 270, with 3129 statements not entered
- reach what only a declaration of the trust file allows: 51
- assume a callee, method, or function type of the module with the weakest contract: 7186

### Refusals by class

| class | functions stopped | stopped alone | first cause | not looked at in full | top details (stopped, alone) |
| --- | --- | --- | --- | --- | --- |
| `recursion:through-call` | 2354 | 909 | 1492 | 50 | `(*sync.Pool).Put` (174, 92); `(*sync.Pool).Get` (159, 39); `os.NewSyscallError` (121, 18) |
| `recursion:through-method` | 794 | 330 | 460 | 15 | `(io.Writer).Write` (108, 47); `(io.Reader).Read` (57, 29); `(io.Closer).Close` (44, 20) |
| `func-value:calls-values` | 753 | 179 | 299 | 22 |  |
| `global:read` | 681 | 170 | 381 | 20 |  |
| `type:array-in-struct` | 594 | 295 | 526 | 11 | `*text/template/parse.Tree` (136, 76); `*regexp/syntax.Regexp` (46, 20); `*crypto/tls.quicState` (41, 9) |
| `recursion:through-value` | 411 | 108 | 174 | 10 | `fn` (78, 24); `f` (74, 26); `s.Error` (14, 10) |
| `type:uintptr` | 388 | 74 | 268 | 11 | `uintptr` (168, 28); `reflect.flag` (134, 28); `syscall.Errno` (115, 15) |
| `dyntype:assert` | 357 | 49 | 168 | 8 |  |
| `func-value:no-contract` | 337 | 60 | 122 | 16 | `func()` (50, 3); `encoding/json/v2.marshaler` (18, 0); `encoding/json/v2.unmarshaler` (17, 0) |
| `assign:target` | 331 | 73 | 143 | 7 |  |
| `pointer:to-non-struct` | 319 | 110 | 194 | 9 | `*vendor/golang.org/x/crypto/cryptobyte.String` (42, 23); `*fmt.buffer` (29, 12); `*[]byte` (26, 7) |
| `convert:to-error` | 263 | 43 | 73 | 9 |  |
| `expr:index` | 210 | 3 | 19 | 3 | `*archive/tar.headerGNU` (10, 0); `*archive/tar.headerSTAR` (10, 0); `*archive/tar.headerV7` (9, 0) |
| `type:unsafe-pointer` | 195 | 12 | 74 | 8 | `unsafe.Pointer` (195, 12) |
| `error:unknown-origin` | 184 | 36 | 58 | 10 | `formatted` (86, 12); `Error called` (73, 18); `errors.Is` (19, 4) |
| `pointer:to-array` | 179 | 54 | 152 | 0 | `*archive/tar.block` (19, 1); `*archive/tar.headerV7` (19, 0); `*hash/crc32.Table` (19, 7) |
| `convert:value` | 170 | 5 | 5 | 7 | `uintptr to int` (20, 0); `unsafe.Pointer to *internal/unsafeheader.Slice` (17, 0); `unsafe.Pointer to *reflect.structType` (15, 0) |
| `generic:called` | 164 | 45 | 81 | 6 | `os.doInRoot` (15, 0); `reflect.TypeAssert` (13, 2); `encoding/json/internal/jsonwire.NewInvalidCharacterError` (11, 2) |
| `generic:declared` | 163 | 0 | 163 | 163 |  |
| `channel:use` | 146 | 21 | 62 | 4 | `<-chan struct{}` (56, 3); `chan struct{}` (44, 2); `chan bool` (20, 1) |
| `dyntype:switch` | 142 | 31 | 67 | 3 |  |
| `error:sentinel` | 135 | 16 | 72 | 5 |  |
| `call:builtin` | 134 | 39 | 45 | 1 | `clear` (37, 12); `imag` (29, 0); `real` (28, 0) |
| `convert:iface-no-contract` | 127 | 13 | 36 | 1 | `(text/template/parse.Node).Position` (23, 1); `(go/types.Object).Exported` (20, 1); `(sync.Locker).Lock` (12, 0) |
| `package:not-loaded` | 116 | 0 | 116 | 116 |  |
| `type:map-key` | 116 | 11 | 58 | 3 | `go/ast.CommentMap` (6, 0); `map[*crypto/x509.policyGraphNode]bool` (5, 0); `map[*encoding/gob.typeInfo]bool` (5, 0) |
| `handover:unknown-code` | 105 | 17 | 27 | 5 |  |
| `address-of:field` | 95 | 47 | 58 | 5 | `x.v` (32, 32); `xe.Tokens.Last` (10, 0); `m.Last` (5, 4) |
| `type:array` | 86 | 14 | 31 | 0 | `[4]image/jpeg.component` (8, 0); `[16]unicode/utf8.acceptRange` (6, 4); `[1]uintptr` (6, 0) |
| `address-of:global` | 80 | 0 | 0 | 0 | `lookupCache` (4, 0); `mimeTypes` (4, 0); `running` (4, 0) |
| `format:runs-code` | 74 | 23 | 26 | 2 |  |
| `recursion:through-format` | 70 | 26 | 34 | 1 | `fmt.Sprintf` (46, 14); `fmt.Errorf` (14, 7); `fmt.Fprintf` (11, 5) |
| `convert:iface-array` | 69 | 19 | 25 | 4 |  |
| `global:assign` | 63 | 8 | 27 | 0 |  |
| `select:statement` | 62 | 3 | 16 | 2 |  |
| `generic:method-call` | 60 | 22 | 38 | 2 |  |
| `expr:value-shape` | 54 | 11 | 41 | 2 |  |
| `type:complex` | 52 | 9 | 40 | 3 | `complex128` (52, 9); `complex64` (1, 0) |
| `goroutine:go` | 51 | 4 | 7 | 2 |  |
| `assign:multi-value` | 48 | 12 | 28 | 0 | `+=` (4, 2); `|=` (4, 4); `^=` (2, 2) |
| `recursion:through-trusted` | 48 | 20 | 22 | 1 |  |
| `contract:unusable` | 42 | 7 | 17 | 3 |  |
| `format:slice-pack` | 40 | 23 | 35 | 0 |  |
| `append:in-expression` | 39 | 15 | 22 | 2 |  |
| `generic:type-args` | 36 | 8 | 13 | 0 |  |
| `recover:call` | 35 | 10 | 14 | 1 |  |
| `limit:paths` | 34 | 0 | 5 | 34 |  |
| `stmt:goto` | 33 | 8 | 16 | 10 |  |
| `address-of:element` | 32 | 6 | 6 | 0 | `buf[0]` (5, 0); `x[0]` (3, 0); `b[0]` (2, 0) |
| `convert:iface-by-contract` | 32 | 0 | 5 | 3 |  |
| `scoped:kept` | 31 | 1 | 25 | 3 |  |
| `func-value:trusted-callee` | 30 | 0 | 6 | 3 |  |
| `copy:elements` | 29 | 7 | 10 | 2 |  |
| `convert:multi-value` | 28 | 1 | 6 | 1 |  |
| `generic:iterator` | 27 | 12 | 13 | 1 |  |
| `scoped:written` | 27 | 1 | 22 | 3 |  |
| `stmt:range-other` | 27 | 0 | 5 | 0 | `map[*crypto/x509.policyGraphNode]bool` (3, 0); `map[net.Conn]net/http.ConnState` (3, 0); `go/ast.CommentMap` (2, 0) |
| `stmt:expression` | 25 | 0 | 7 | 1 |  |
| `convert:iface-states` | 23 | 1 | 6 | 1 |  |
| `func-literal:signature` | 22 | 0 | 22 | 1 |  |
| `convert:unplaced` | 20 | 0 | 0 | 0 |  |
| `operator:nil-compare` | 18 | 0 | 0 | 0 | `*regexp/syntax.Regexp` (4, 0); `*compress/flate.Writer` (2, 0); `*crypto/mldsa.PrivateKey` (2, 0) |
| `convert:iface-wraps-writer` | 13 | 0 | 2 | 2 |  |
| `func-value:made-from` | 13 | 0 | 7 | 0 |  |
| `limit:internal` | 13 | 0 | 8 | 13 |  |
| `scoped:hidden` | 12 | 3 | 12 | 1 |  |
| `type:iface-literal` | 11 | 2 | 5 | 0 | `net.Error` (10, 2); `testing.fuzzCrashError` (1, 0) |
| `call:multi-value-args` | 10 | 1 | 2 | 0 |  |
| `global:followed-code` | 10 | 0 | 0 | 2 |  |
| `defer:in-loop` | 8 | 1 | 2 | 0 |  |
| `func-literal:captures` | 8 | 6 | 7 | 0 |  |
| `global:type` | 8 | 1 | 5 | 0 |  |
| `limit:facts` | 8 | 0 | 1 | 8 |  |
| `type:array-elem` | 8 | 6 | 6 | 0 | `[2]uint64` (4, 4); `[2]uint16` (1, 1); `[32]byte` (1, 1) |
| `iface-method:form` | 7 | 2 | 7 | 0 |  |
| `json:form` | 7 | 0 | 2 | 0 |  |
| `copy:value-with-state` | 6 | 1 | 6 | 0 |  |
| `exit:context` | 6 | 0 | 0 | 0 |  |
| `defer:form` | 5 | 0 | 1 | 0 |  |
| `stmt:range-form` | 5 | 1 | 3 | 0 |  |
| `func-value:method-value` | 3 | 0 | 1 | 0 |  |
| `json:encode` | 3 | 1 | 2 | 0 |  |
| `closure:recursive` | 2 | 0 | 2 | 0 |  |
| `func-value:method-expr` | 2 | 1 | 1 | 0 |  |
| `json:decode` | 2 | 0 | 0 | 0 |  |
| `limit:attempts` | 2 | 0 | 0 | 2 |  |
| `annotation:unreadable` | 1 | 0 | 0 | 1 |  |
| `call:form` | 1 | 0 | 0 | 0 |  |
| `call:initialiser-only` | 1 | 1 | 1 | 0 |  |
| `func-literal:value` | 1 | 0 | 0 | 0 |  |
| `handover:footprint` | 1 | 0 | 1 | 0 |  |
| `handover:sort` | 1 | 0 | 0 | 0 |  |
| `operator:pointer` | 1 | 0 | 1 | 0 |  |

### Refusals by group

| group | functions stopped | stopped alone | first cause | not looked at in full | top details (stopped, alone) |
| --- | --- | --- | --- | --- | --- |
| `recursion` | 3153 | 1508 | 2182 | 52 |  |
| `type` | 1260 | 454 | 1008 | 23 |  |
| `func-value` | 1024 | 254 | 436 | 29 |  |
| `global` | 710 | 193 | 413 | 22 |  |
| `convert` | 689 | 86 | 158 | 23 |  |
| `pointer` | 495 | 164 | 346 | 9 |  |
| `dyntype` | 459 | 82 | 235 | 11 |  |
| `generic` | 441 | 87 | 308 | 172 |  |
| `assign` | 355 | 90 | 171 | 7 |  |
| `error` | 299 | 54 | 130 | 13 |  |
| `expr` | 263 | 14 | 60 | 5 |  |
| `address-of` | 200 | 55 | 64 | 5 |  |
| `call` | 146 | 41 | 48 | 1 |  |
| `channel` | 146 | 21 | 62 | 4 |  |
| `package` | 116 | 0 | 116 | 116 |  |
| `format` | 114 | 46 | 61 | 2 |  |
| `handover` | 107 | 17 | 28 | 5 |  |
| `stmt` | 90 | 9 | 31 | 11 |  |
| `select` | 62 | 3 | 16 | 2 |  |
| `scoped` | 61 | 5 | 59 | 5 |  |
| `limit` | 57 | 0 | 14 | 57 |  |
| `goroutine` | 51 | 4 | 7 | 2 |  |
| `contract` | 42 | 7 | 17 | 3 |  |
| `append` | 39 | 15 | 22 | 2 |  |
| `copy` | 35 | 8 | 16 | 2 |  |
| `recover` | 35 | 10 | 14 | 1 |  |
| `func-literal` | 31 | 6 | 29 | 1 |  |
| `operator` | 19 | 0 | 1 | 0 |  |
| `json` | 12 | 1 | 4 | 0 |  |
| `defer` | 11 | 1 | 3 | 0 |  |
| `iface-method` | 7 | 2 | 7 | 0 |  |
| `exit` | 6 | 0 | 0 | 0 |  |
| `closure` | 2 | 0 | 2 | 0 |  |
| `annotation` | 1 | 0 | 0 | 1 |  |

### Greedy order of classes

Get through with nothing fixed: 4743.

| step | fixed | let through by it | let through in all |
| --- | --- | --- | --- |
| 1 | `recursion:through-call` | 909 | 5652 |
| 2 | `recursion:through-method` | 386 | 6038 |
| 3 | `func-value:calls-values` | 320 | 6358 |
| 4 | `type:array-in-struct` | 335 | 6693 |
| 5 | `global:read` | 264 | 6957 |
| 6 | `recursion:through-value` | 192 | 7149 |
| 7 | `pointer:to-non-struct` | 158 | 7307 |
| 8 | `func-value:no-contract` | 150 | 7457 |
| 9 | `dyntype:assert` | 153 | 7610 |
| 10 | `type:uintptr` | 141 | 7751 |
| 11 | `convert:to-error` | 148 | 7899 |
| 12 | `assign:target` | 140 | 8039 |
| 13 | `generic:called` | 104 | 8143 |
| 14 | `error:unknown-origin` | 95 | 8238 |
| 15 | `convert:iface-no-contract` | 90 | 8328 |
| 16 | `error:sentinel` | 90 | 8418 |
| 17 | `dyntype:switch` | 84 | 8502 |
| 18 | `pointer:to-array` | 74 | 8576 |
| 19 | `expr:index` | 130 | 8706 |
| 20 | `call:builtin` | 76 | 8782 |

### Greedy order of groups

Get through with nothing fixed: 4743.

| step | fixed | let through by it | let through in all |
| --- | --- | --- | --- |
| 1 | `recursion` | 1508 | 6251 |
| 2 | `type` | 547 | 6798 |
| 3 | `func-value` | 526 | 7324 |
| 4 | `convert` | 389 | 7713 |
| 5 | `global` | 374 | 8087 |
| 6 | `pointer` | 275 | 8362 |
| 7 | `dyntype` | 264 | 8626 |
| 8 | `assign` | 233 | 8859 |
| 9 | `expr` | 208 | 9067 |
| 10 | `generic` | 216 | 9283 |
| 11 | `error` | 218 | 9501 |
| 12 | `address-of` | 180 | 9681 |
| 13 | `call` | 129 | 9810 |
| 14 | `format` | 95 | 9905 |
| 15 | `handover` | 71 | 9976 |
| 16 | `stmt` | 51 | 10027 |
| 17 | `channel` | 61 | 10088 |
| 18 | `scoped` | 42 | 10130 |
| 19 | `select` | 41 | 10171 |
| 20 | `goroutine` | 43 | 10214 |

### Greedy order of classes, with what the project writes for other modules (no-entry:other and the classes ending in -other) left out of the causes

Get through with nothing fixed: 4743.

| step | fixed | let through by it | let through in all |
| --- | --- | --- | --- |
| 1 | `recursion:through-call` | 909 | 5652 |
| 2 | `recursion:through-method` | 386 | 6038 |
| 3 | `func-value:calls-values` | 320 | 6358 |
| 4 | `type:array-in-struct` | 335 | 6693 |
| 5 | `global:read` | 264 | 6957 |
| 6 | `recursion:through-value` | 192 | 7149 |
| 7 | `pointer:to-non-struct` | 159 | 7308 |
| 8 | `dyntype:assert` | 150 | 7458 |
| 9 | `func-value:no-contract` | 154 | 7612 |
| 10 | `type:uintptr` | 141 | 7753 |
| 11 | `convert:to-error` | 148 | 7901 |
| 12 | `assign:target` | 140 | 8041 |
| 13 | `generic:called` | 104 | 8145 |
| 14 | `error:unknown-origin` | 95 | 8240 |
| 15 | `convert:iface-no-contract` | 90 | 8330 |
| 16 | `error:sentinel` | 90 | 8420 |
| 17 | `dyntype:switch` | 84 | 8504 |
| 18 | `pointer:to-array` | 77 | 8581 |
| 19 | `expr:index` | 131 | 8712 |
| 20 | `call:builtin` | 76 | 8788 |

### Greedy order of groups, with what the project writes for other modules (no-entry:other and the classes ending in -other) left out of the causes

Get through with nothing fixed: 4743.

| step | fixed | let through by it | let through in all |
| --- | --- | --- | --- |
| 1 | `recursion` | 1508 | 6251 |
| 2 | `type` | 551 | 6802 |
| 3 | `func-value` | 526 | 7328 |
| 4 | `convert` | 390 | 7718 |
| 5 | `global` | 376 | 8094 |
| 6 | `pointer` | 279 | 8373 |
| 7 | `dyntype` | 266 | 8639 |
| 8 | `assign` | 235 | 8874 |
| 9 | `expr` | 212 | 9086 |
| 10 | `generic` | 219 | 9305 |
| 11 | `error` | 218 | 9523 |
| 12 | `address-of` | 180 | 9703 |
| 13 | `call` | 129 | 9832 |
| 14 | `format` | 97 | 9929 |
| 15 | `handover` | 71 | 10000 |
| 16 | `channel` | 47 | 10047 |
| 17 | `scoped` | 42 | 10089 |
| 18 | `select` | 41 | 10130 |
| 19 | `stmt` | 41 | 10171 |
| 20 | `goroutine` | 43 | 10214 |

### Callees without an entry

| callee | class | functions stopped | stopped alone |
| --- | --- | --- | --- |

### Refusals made only when a proof fails

A census proves nothing, so it makes these wherever they are reached; the prover would often prove what they ask.

| class | functions met in | the only thing met | top details |
| --- | --- | --- | --- |
| `error:compare-unproved` | 39 | 0 |  |
| `format:length-unknown` | 2 | 1 |  |

### Panics of the verifier (limit:internal)

- `compress/flate.(*compressor).fillWindow`: interface conversion: types.Type is *types.Pointer, not *types.Struct; at hopsPointer({0x11c3d68, 0x1bd4f6371ab0}, {0x1bd4f65fc680, 0x2, 0x2}) < (*fnVerifier).assignedLocal < (*fnVerifier).eval < (*fnVerifier).expr < (*fnVerifier).binaryExpr < (*fnVerifier).eval < (*fnVerifier).expr < (*fnVerifier).ifStmt.func2()
- `compress/flate.(*compressor).findMatch`: interface conversion: types.Type is *types.Pointer, not *types.Struct; at hopsPointer({0x11c3d68, 0x1bd4f6371ad0}, {0x1bd4f65fc800, 0x2, 0x2}) < (*fnVerifier).assignedLocal < (*fnVerifier).eval < (*fnVerifier).expr < (*fnVerifier).callExpr < (*fnVerifier).eval < (*fnVerifier).evalAs < (*fnVerifier).assign
- `compress/flate.(*compressor).skipLiterals`: interface conversion: types.Type is *types.Pointer, not *types.Struct; at hopsPointer({0x11c3d68, 0x1bd4f6371c10}, {0x1bd4f65fcc80, 0x2, 0x2}) < (*fnVerifier).assignedLocal < (*fnVerifier).eval < (*fnVerifier).expr < (*fnVerifier).binaryExpr < (*fnVerifier).eval < (*fnVerifier).evalAs < (*fnVerifier).assign
- `compress/flate.(*compressor).deflateLazy`: interface conversion: types.Type is *types.Pointer, not *types.Struct; at hopsPointer({0x11c3d68, 0x1bd4f6371c20}, {0x1bd4f65fcf60, 0x2, 0x2}) < (*fnVerifier).assignedLocal < (*fnVerifier).eval < (*fnVerifier).expr < (*fnVerifier).binaryExpr < (*fnVerifier).eval < (*fnVerifier).expr < (*fnVerifier).binaryExpr
- `compress/flate.(*compressor).init`: interface conversion: types.Type is *types.Pointer, not *types.Struct; at (*fnVerifier).checkNotWritten.func1 < (*fnVerifier).checkNotWritten.func4({0x11c40d8?, 0x1bd4f43de640}) < (*fnVerifier).checkNotWritten < (*fnVerifier).verify.func6() < (*fnVerifier).censusCheck < (*fnVerifier).verify < (*pkgVerifier).censusLook < (*pkgVerifier).runCensus
- `compress/flate.(*fastEncL1).encode`: interface conversion: types.Type is *types.Pointer, not *types.Struct; at (*fnVerifier).checkNotWritten.func1 < (*fnVerifier).checkNotWritten.func4({0x11c40d8?, 0x1bd4f445d640}) < (*fnVerifier).checkNotWritten < (*fnVerifier).verify.func6() < (*fnVerifier).censusCheck < (*fnVerifier).verify < (*pkgVerifier).censusLook < (*pkgVerifier).runCensus
- `compress/flate.(*fastEncL2).encode`: interface conversion: types.Type is *types.Pointer, not *types.Struct; at (*fnVerifier).checkNotWritten.func1 < (*fnVerifier).checkNotWritten.func4({0x11c40d8?, 0x1bd4f4584200}) < (*fnVerifier).checkNotWritten < (*fnVerifier).verify.func6() < (*fnVerifier).censusCheck < (*fnVerifier).verify < (*pkgVerifier).censusLook < (*pkgVerifier).runCensus
- `compress/flate.(*fastEncL3).encode`: interface conversion: types.Type is *types.Pointer, not *types.Struct; at (*fnVerifier).checkNotWritten.func1 < (*fnVerifier).checkNotWritten.func4({0x11c40d8?, 0x1bd4f458ce00}) < (*fnVerifier).checkNotWritten < (*fnVerifier).verify.func6() < (*fnVerifier).censusCheck < (*fnVerifier).verify < (*pkgVerifier).censusLook < (*pkgVerifier).runCensus
- `compress/flate.(*fastEncL4).encode`: interface conversion: types.Type is *types.Pointer, not *types.Struct; at (*fnVerifier).checkNotWritten.func1 < (*fnVerifier).checkNotWritten.func4({0x11c40d8?, 0x1bd4f4553500}) < (*fnVerifier).checkNotWritten < (*fnVerifier).verify.func6() < (*fnVerifier).censusCheck < (*fnVerifier).verify < (*pkgVerifier).censusLook < (*pkgVerifier).runCensus
- `compress/flate.(*fastEncL5).encode`: interface conversion: types.Type is *types.Pointer, not *types.Struct; at (*fnVerifier).checkNotWritten.func1 < (*fnVerifier).checkNotWritten.func4({0x11c40d8?, 0x1bd4f4597c40}) < (*fnVerifier).checkNotWritten < (*fnVerifier).verify.func6() < (*fnVerifier).censusCheck < (*fnVerifier).verify < (*pkgVerifier).censusLook < (*pkgVerifier).runCensus
- `compress/flate.(*fastEncL6).encode`: interface conversion: types.Type is *types.Pointer, not *types.Struct; at (*fnVerifier).checkNotWritten.func1 < (*fnVerifier).checkNotWritten.func4({0x11c40d8?, 0x1bd4f4578780}) < (*fnVerifier).checkNotWritten < (*fnVerifier).verify.func6() < (*fnVerifier).censusCheck < (*fnVerifier).verify < (*pkgVerifier).censusLook < (*pkgVerifier).runCensus
- `crypto/tls.(*permanentError).Unwrap`: internal error: e.err at /home/spachava/.local/share/mise/installs/go/1.27.3/src/crypto/tls/conn.go:192:52 is checked as a conversion to error, which the list of conversions does not have there; at (*fnVerifier).evalConverted < (*fnVerifier).evalAs < (*fnVerifier).returnStmt < (*fnVerifier).stmt < (*fnVerifier).seq.func2 < (*fnVerifier).censusStmt < (*fnVerifier).seq < (*fnVerifier).verify
- `os.Getwd`: runtime error: slice bounds out of range [58:57]; at (*fnVerifier).loop < (*fnVerifier).forStmt < (*fnVerifier).seq.func2 < (*fnVerifier).censusStmt < (*fnVerifier).seq < (*fnVerifier).seq.func1 < (*fnVerifier).censusStmt.func2 < (*fnVerifier).logging.func1

Functions of generated files, left out of every count above: 802.

## Corpus modules

- functions with a body: 5015, of which not loaded: 0
- get through: 2160 (43.1%), of which 2 only past refusals made when a proof fails
- not looked at in full (a statement no attempt entered, or the census stopped): 181, with 1314 statements not entered
- reach what only a declaration of the trust file allows: 50
- assume a callee, method, or function type of the module with the weakest contract: 2743

### Refusals by class

| class | functions stopped | stopped alone | first cause | not looked at in full | top details (stopped, alone) |
| --- | --- | --- | --- | --- | --- |
| `recursion:through-call` | 900 | 411 | 549 | 13 | `reflect.ValueOf` (49, 10); `(*strings.Replacer).Replace` (46, 14); `(*sync/atomic.Value).Load` (44, 13) |
| `no-entry:std` | 828 | 252 | 553 | 18 | `reflect.ValueOf` (89, 0); `(reflect.Value).Type` (85, 0); `(reflect.Value).Kind` (69, 1) |
| `recursion:through-value` | 268 | 119 | 186 | 2 | `cb` (62, 51); `ErrorHandler` (44, 22); `tree.Comparator` (30, 23) |
| `func-value:calls-values` | 250 | 73 | 110 | 8 |  |
| `error:unknown-origin` | 221 | 19 | 35 | 7 | `formatted` (177, 10); `Error called` (27, 5); `errors.Is` (20, 0) |
| `iface-method:no-contract` | 198 | 28 | 65 | 9 | `(reflect.Type).Kind` (71, 9); `(reflect.Type).Elem` (56, 0); `(reflect.Type).Field` (18, 0) |
| `global:read` | 197 | 39 | 76 | 8 |  |
| `format:runs-code` | 181 | 58 | 67 | 4 |  |
| `recursion:through-method` | 163 | 27 | 50 | 7 | `(io.Closer).Close` (25, 0); `(github.com/modelcontextprotocol/go-sdk/mcp.Params).SetMeta` (24, 0); `(github.com/go-sql-driver/mysql.Logger).Print` (23, 1) |
| `func-value:no-contract` | 158 | 22 | 55 | 8 | `func()` (15, 1); `func() *github.com/dlclark/regexp2/syntax.CharSet` (10, 9); `context.CancelCauseFunc` (7, 0) |
| `generic:declared` | 150 | 0 | 150 | 150 |  |
| `channel:use` | 114 | 14 | 36 | 1 | `chan struct{}` (48, 2); `<-chan struct{}` (40, 3); `<-chan time.Time` (10, 0) |
| `assign:target` | 110 | 23 | 40 | 3 |  |
| `type:array-in-struct` | 101 | 50 | 94 | 2 | `*github.com/BurntSushi/toml.lexer` (62, 29); `*github.com/emirpasic/gods/trees/avltree.Node` (32, 19); `github.com/BurntSushi/toml.lexer` (7, 1) |
| `generic:called` | 96 | 31 | 55 | 2 | `github.com/modelcontextprotocol/go-sdk/mcp.orZero` (23, 0); `github.com/modelcontextprotocol/go-sdk/mcp.handleSend` (19, 0); `github.com/modelcontextprotocol/go-sdk/mcp.AddTool` (17, 1) |
| `handover:unknown-code` | 96 | 17 | 27 | 4 |  |
| `pointer:to-non-struct` | 96 | 26 | 71 | 4 | `*error` (12, 0); `*any` (11, 1); `*[]byte` (9, 2) |
| `convert:iface-no-contract` | 82 | 29 | 56 | 1 | `(github.com/modelcontextprotocol/go-sdk/mcp.Params).GetMeta` (50, 23); `(net/http.Handler).ServeHTTP` (5, 0); `(context.Context).Deadline` (3, 1) |
| `type:map-key` | 66 | 14 | 36 | 1 | `map[interface{}]interface{}` (9, 5); `map[*github.com/modelcontextprotocol/go-sdk/mcp.ServerSession]github.com/modelcontextprotocol/go-sdk/jsonrpc.ID` (8, 0); `map[interface{}]struct{}` (8, 4) |
| `convert:to-error` | 63 | 18 | 22 | 1 |  |
| `recursion:through-format` | 63 | 14 | 40 | 1 | `fmt.Sprintf` (53, 10); `fmt.Errorf` (10, 4); `fmt.Fprintf` (3, 0) |
| `dyntype:assert` | 61 | 5 | 28 | 2 |  |
| `json:encode` | 59 | 21 | 37 | 1 |  |
| `scoped:kept` | 57 | 1 | 54 | 1 |  |
| `convert:value` | 47 | 27 | 35 | 1 | `[]rune to string` (30, 15); `string to []rune` (15, 8); `unsafe.Pointer to *string` (3, 0) |
| `select:statement` | 47 | 0 | 16 | 0 |  |
| `error:sentinel` | 42 | 9 | 19 | 2 |  |
| `json:decode` | 38 | 13 | 23 | 0 |  |
| `goroutine:go` | 37 | 1 | 2 | 0 |  |
| `expr:index` | 36 | 4 | 7 | 1 | `map[*github.com/google/jsonschema-go/jsonschema.Schema]*github.com/google/jsonschema-go/jsonschema.resolvedInfo` (9, 2); `[6]byte` (4, 0); `map[reflect.Type]bool` (4, 0) |
| `no-entry:other` | 36 | 6 | 15 | 0 | `(*golang.org/x/oauth2.Config).Exchange` (7, 0); `(*golang.org/x/oauth2.Token).Extra` (6, 1); `golang.org/x/oauth2.SetAuthURLParam` (6, 1) |
| `assign:multi-value` | 31 | 7 | 13 | 1 | `+=` (3, 0) |
| `call:multi-value-args` | 30 | 28 | 30 | 0 |  |
| `generic:method-call` | 27 | 1 | 6 | 0 |  |
| `convert:multi-value` | 26 | 0 | 7 | 1 |  |
| `copy:elements` | 25 | 15 | 19 | 0 |  |
| `stmt:range-other` | 25 | 4 | 10 | 1 | `map[interface{}]struct{}` (9, 2); `map[interface{}]interface{}` (3, 2); `map[float64]string` (2, 0) |
| `call:builtin` | 24 | 5 | 6 | 1 | `close` (19, 4); `copy` (4, 1); `imag` (1, 0) |
| `convert:unplaced` | 24 | 0 | 0 | 0 |  |
| `dyntype:switch` | 24 | 0 | 6 | 1 |  |
| `json:form` | 21 | 0 | 3 | 0 |  |
| `append:in-expression` | 20 | 6 | 7 | 0 |  |
| `format:slice-pack` | 19 | 9 | 10 | 0 |  |
| `func-literal:signature` | 19 | 0 | 19 | 2 |  |
| `generic:type-args` | 18 | 1 | 6 | 0 |  |
| `expr:value-shape` | 16 | 6 | 6 | 0 |  |
| `global:assign` | 15 | 1 | 7 | 1 |  |
| `func-value:made-from` | 13 | 2 | 2 | 1 |  |
| `type:array` | 13 | 7 | 8 | 0 | `[2]github.com/google/go-cmp/cmp/internal/value.Pointer` (5, 0); `[6][2]float64` (3, 2); `[12]sync.Pool` (1, 0) |
| `address-of:field` | 12 | 8 | 8 | 0 | `x.Cursor` (4, 4); `x.NextCursor` (4, 4); `b.attempt` (2, 0) |
| `global:type` | 12 | 0 | 4 | 0 |  |
| `limit:paths` | 12 | 0 | 1 | 12 |  |
| `call:initialiser-only` | 11 | 5 | 6 | 0 |  |
| `generic:iterator` | 11 | 1 | 4 | 1 |  |
| `stmt:expression` | 11 | 0 | 2 | 0 |  |
| `stmt:goto` | 10 | 3 | 7 | 4 |  |
| `type:uintptr` | 10 | 1 | 4 | 0 | `uintptr` (10, 1); `syscall.Errno` (1, 0) |
| `convert:iface-array` | 9 | 0 | 0 | 2 |  |
| `convert:iface-foreign-impl` | 9 | 0 | 0 | 0 |  |
| `func-literal:value` | 8 | 1 | 8 | 0 |  |
| `no-entry:impossible` | 8 | 0 | 4 | 1 | `io.Copy` (6, 0); `(*bytes.Buffer).ReadFrom` (1, 0); `io.CopyN` (1, 0) |
| `recover:call` | 8 | 0 | 1 | 1 |  |
| `expr:other` | 7 | 0 | 5 | 0 |  |
| `operator:nil-compare` | 7 | 0 | 0 | 0 | `*github.com/emirpasic/gods/trees/avltree.Node` (4, 0); `<-chan struct{}` (2, 0); `chan struct{}` (1, 0) |
| `type:unsafe-pointer` | 7 | 1 | 3 | 0 | `unsafe.Pointer` (7, 1) |
| `address-of:global` | 6 | 0 | 0 | 0 | `upgrader` (5, 0); `fieldCache` (1, 0) |
| `convert:iface-states` | 5 | 0 | 0 | 0 |  |
| `iface-method:no-contract-other` | 5 | 0 | 2 | 0 | `(golang.org/x/oauth2.TokenSource).Token` (4, 0); `(github.com/go-jose/go-jose/v4.Signer).Sign` (1, 0) |
| `pointer:to-array` | 5 | 3 | 5 | 0 | `*github.com/google/uuid.UUID` (5, 3) |
| `convert:iface-optional` | 4 | 0 | 0 | 1 |  |
| `defer:in-loop` | 4 | 1 | 1 | 0 |  |
| `func-value:method-value` | 4 | 0 | 0 | 0 |  |
| `scoped:written` | 4 | 0 | 4 | 1 |  |
| `type:complex` | 4 | 0 | 0 | 1 | `complex128` (4, 0) |
| `type:iface-literal` | 4 | 1 | 1 | 2 | `net.Error` (2, 1); `github.com/modelcontextprotocol/go-sdk/mcp.binder[*github.com/modelcontextprotocol/go-sdk/mcp.ClientSession, *github.com/modelcontextprotocol/go-sdk/mcp.clientSessionState]` (1, 0); `github.com/modelcontextprotocol/go-sdk/mcp.binder[*github.com/modelcontextprotocol/go-sdk/mcp.ServerSession, *github.com/modelcontextprotocol/go-sdk/mcp.ServerSessionState]` (1, 0) |
| `defer:form` | 3 | 0 | 0 | 0 |  |
| `stmt:range-form` | 3 | 1 | 2 | 0 |  |
| `type:array-elem` | 3 | 1 | 1 | 0 | `[2]github.com/google/go-cmp/cmp/internal/value.Pointer` (1, 0); `github.com/google/uuid.UUID` (1, 1); `github.com/lucasb-eyer/go-colorful.edgeIdxs` (1, 0) |
| `address-of:element` | 2 | 1 | 1 | 0 | `b[0]` (1, 0); `oldText[0]` (1, 1) |
| `closure:recursive` | 2 | 0 | 2 | 0 |  |
| `contract:unusable` | 2 | 0 | 0 | 0 |  |
| `convert:iface-wraps-writer` | 2 | 0 | 0 | 1 |  |
| `func-literal:captures` | 2 | 0 | 0 | 0 |  |
| `generic:as-value` | 2 | 0 | 0 | 0 |  |
| `handover:footprint` | 2 | 0 | 0 | 0 |  |
| `handover:sort` | 2 | 0 | 0 | 0 |  |
| `iface-method:form` | 2 | 1 | 1 | 0 |  |
| `limit:internal` | 2 | 0 | 0 | 2 |  |
| `annotation:unreadable` | 1 | 1 | 1 | 0 |  |
| `assign:in-place` | 1 | 0 | 0 | 0 |  |
| `copy:value-with-state` | 1 | 1 | 1 | 0 |  |
| `dyntype:errors-as` | 1 | 0 | 0 | 0 |  |
| `exit:context` | 1 | 1 | 1 | 0 |  |
| `limit:attempts` | 1 | 0 | 0 | 1 |  |

### Refusals by group

| group | functions stopped | stopped alone | first cause | not looked at in full | top details (stopped, alone) |
| --- | --- | --- | --- | --- | --- |
| `recursion` | 1256 | 600 | 825 | 14 |  |
| `no-entry` | 851 | 259 | 572 | 18 |  |
| `func-value` | 390 | 102 | 167 | 13 |  |
| `generic` | 290 | 42 | 221 | 153 |  |
| `error` | 254 | 28 | 54 | 8 |  |
| `convert` | 242 | 77 | 120 | 7 |  |
| `global` | 212 | 46 | 87 | 8 |  |
| `iface-method` | 204 | 29 | 68 | 9 |  |
| `type` | 201 | 75 | 147 | 6 |  |
| `format` | 200 | 67 | 77 | 4 |  |
| `assign` | 129 | 30 | 53 | 4 |  |
| `channel` | 114 | 14 | 36 | 1 |  |
| `json` | 107 | 39 | 63 | 1 |  |
| `pointer` | 101 | 29 | 76 | 4 |  |
| `handover` | 100 | 17 | 27 | 4 |  |
| `dyntype` | 80 | 6 | 34 | 3 |  |
| `call` | 65 | 38 | 42 | 1 |  |
| `scoped` | 59 | 1 | 58 | 2 |  |
| `expr` | 56 | 10 | 18 | 1 |  |
| `stmt` | 49 | 8 | 21 | 5 |  |
| `select` | 47 | 0 | 16 | 0 |  |
| `goroutine` | 37 | 1 | 2 | 0 |  |
| `func-literal` | 29 | 1 | 27 | 2 |  |
| `copy` | 26 | 16 | 20 | 0 |  |
| `address-of` | 20 | 9 | 9 | 0 |  |
| `append` | 20 | 6 | 7 | 0 |  |
| `limit` | 15 | 0 | 1 | 15 |  |
| `recover` | 8 | 0 | 1 | 1 |  |
| `defer` | 7 | 1 | 1 | 0 |  |
| `operator` | 7 | 0 | 0 | 0 |  |
| `closure` | 2 | 0 | 2 | 0 |  |
| `contract` | 2 | 0 | 0 | 0 |  |
| `annotation` | 1 | 1 | 1 | 0 |  |
| `exit` | 1 | 1 | 1 | 0 |  |

### Greedy order of classes

Get through with nothing fixed: 2160.

| step | fixed | let through by it | let through in all |
| --- | --- | --- | --- |
| 1 | `recursion:through-call` | 411 | 2571 |
| 2 | `no-entry:std` | 299 | 2870 |
| 3 | `recursion:through-value` | 136 | 3006 |
| 4 | `func-value:calls-values` | 91 | 3097 |
| 5 | `format:runs-code` | 90 | 3187 |
| 6 | `iface-method:no-contract` | 89 | 3276 |
| 7 | `global:read` | 92 | 3368 |
| 8 | `type:array-in-struct` | 73 | 3441 |
| 9 | `error:unknown-origin` | 72 | 3513 |
| 10 | `recursion:through-method` | 65 | 3578 |
| 11 | `convert:iface-no-contract` | 63 | 3641 |
| 12 | `generic:called` | 53 | 3694 |
| 13 | `func-value:no-contract` | 51 | 3745 |
| 14 | `pointer:to-non-struct` | 51 | 3796 |
| 15 | `handover:unknown-code` | 49 | 3845 |
| 16 | `recursion:through-format` | 50 | 3895 |
| 17 | `assign:target` | 49 | 3944 |
| 18 | `convert:to-error` | 40 | 3984 |
| 19 | `json:encode` | 41 | 4025 |
| 20 | `convert:value` | 38 | 4063 |

### Greedy order of groups

Get through with nothing fixed: 2160.

| step | fixed | let through by it | let through in all |
| --- | --- | --- | --- |
| 1 | `recursion` | 600 | 2760 |
| 2 | `no-entry` | 329 | 3089 |
| 3 | `func-value` | 164 | 3253 |
| 4 | `convert` | 143 | 3396 |
| 5 | `format` | 112 | 3508 |
| 6 | `type` | 112 | 3620 |
| 7 | `global` | 110 | 3730 |
| 8 | `iface-method` | 122 | 3852 |
| 9 | `error` | 129 | 3981 |
| 10 | `generic` | 95 | 4076 |
| 11 | `json` | 83 | 4159 |
| 12 | `assign` | 71 | 4230 |
| 13 | `pointer` | 76 | 4306 |
| 14 | `handover` | 65 | 4371 |
| 15 | `dyntype` | 63 | 4434 |
| 16 | `call` | 54 | 4488 |
| 17 | `expr` | 48 | 4536 |
| 18 | `scoped` | 39 | 4575 |
| 19 | `channel` | 42 | 4617 |
| 20 | `stmt` | 34 | 4651 |

### Greedy order of classes, with what the project writes for other modules (no-entry:other and the classes ending in -other) left out of the causes

Get through with nothing fixed: 2170.

| step | fixed | let through by it | let through in all |
| --- | --- | --- | --- |
| 1 | `recursion:through-call` | 415 | 2585 |
| 2 | `no-entry:std` | 299 | 2884 |
| 3 | `recursion:through-value` | 136 | 3020 |
| 4 | `func-value:calls-values` | 92 | 3112 |
| 5 | `format:runs-code` | 91 | 3203 |
| 6 | `iface-method:no-contract` | 89 | 3292 |
| 7 | `global:read` | 94 | 3386 |
| 8 | `error:unknown-origin` | 84 | 3470 |
| 9 | `type:array-in-struct` | 74 | 3544 |
| 10 | `recursion:through-method` | 65 | 3609 |
| 11 | `convert:iface-no-contract` | 63 | 3672 |
| 12 | `generic:called` | 55 | 3727 |
| 13 | `func-value:no-contract` | 52 | 3779 |
| 14 | `pointer:to-non-struct` | 51 | 3830 |
| 15 | `handover:unknown-code` | 52 | 3882 |
| 16 | `recursion:through-format` | 50 | 3932 |
| 17 | `assign:target` | 49 | 3981 |
| 18 | `json:encode` | 42 | 4023 |
| 19 | `convert:to-error` | 44 | 4067 |
| 20 | `convert:value` | 38 | 4105 |

### Greedy order of groups, with what the project writes for other modules (no-entry:other and the classes ending in -other) left out of the causes

Get through with nothing fixed: 2170.

| step | fixed | let through by it | let through in all |
| --- | --- | --- | --- |
| 1 | `recursion` | 604 | 2774 |
| 2 | `no-entry` | 323 | 3097 |
| 3 | `func-value` | 167 | 3264 |
| 4 | `convert` | 143 | 3407 |
| 5 | `format` | 113 | 3520 |
| 6 | `type` | 114 | 3634 |
| 7 | `global` | 110 | 3744 |
| 8 | `error` | 122 | 3866 |
| 9 | `iface-method` | 128 | 3994 |
| 10 | `generic` | 97 | 4091 |
| 11 | `json` | 84 | 4175 |
| 12 | `assign` | 77 | 4252 |
| 13 | `pointer` | 76 | 4328 |
| 14 | `handover` | 67 | 4395 |
| 15 | `dyntype` | 64 | 4459 |
| 16 | `call` | 56 | 4515 |
| 17 | `expr` | 43 | 4558 |
| 18 | `scoped` | 39 | 4597 |
| 19 | `channel` | 42 | 4639 |
| 20 | `select` | 34 | 4673 |

### Callees without an entry

| callee | class | functions stopped | stopped alone |
| --- | --- | --- | --- |
| `reflect.ValueOf` | `no-entry:std` | 89 | 0 |
| `(reflect.Value).Type` | `no-entry:std` | 85 | 0 |
| `(reflect.Value).Kind` | `no-entry:std` | 69 | 1 |
| `(reflect.Value).Interface` | `no-entry:std` | 57 | 0 |
| `(reflect.Value).Elem` | `no-entry:std` | 45 | 0 |
| `(reflect.Value).Len` | `no-entry:std` | 44 | 0 |
| `(reflect.Value).IsNil` | `no-entry:std` | 42 | 0 |
| `(reflect.Value).Set` | `no-entry:std` | 41 | 1 |
| `context.Background` | `no-entry:std` | 41 | 0 |
| `(reflect.Value).IsValid` | `no-entry:std` | 36 | 1 |
| `(reflect.Value).Index` | `no-entry:std` | 30 | 0 |
| `flag.Parse` | `no-entry:std` | 28 | 1 |
| `net/url.Parse` | `no-entry:std` | 25 | 6 |
| `reflect.Indirect` | `no-entry:std` | 25 | 0 |
| `reflect.New` | `no-entry:std` | 24 | 0 |
| `reflect.TypeOf` | `no-entry:std` | 24 | 3 |
| `(reflect.Value).String` | `no-entry:std` | 23 | 0 |
| `(reflect.Value).Bool` | `no-entry:std` | 20 | 0 |
| `(*sync/atomic.Bool).Load` | `no-entry:std` | 15 | 1 |
| `(*encoding/base64.Encoding).EncodeToString` | `no-entry:std` | 14 | 3 |
| `(*log/slog.Logger).Error` | `no-entry:std` | 14 | 0 |
| `(*net/http.Request).Context` | `no-entry:std` | 14 | 0 |
| `(*net/url.URL).String` | `no-entry:std` | 14 | 0 |
| `(reflect.Value).Int` | `no-entry:std` | 14 | 0 |
| `(reflect.Value).MapIndex` | `no-entry:std` | 14 | 0 |
| `context.WithValue` | `no-entry:std` | 14 | 2 |
| `errors.Join` | `no-entry:std` | 14 | 2 |
| `(reflect.Value).Field` | `no-entry:std` | 13 | 0 |
| `strconv.ParseFloat` | `no-entry:std` | 13 | 4 |
| `(reflect.Value).Float` | `no-entry:std` | 12 | 0 |
| `strings.ContainsRune` | `no-entry:std` | 12 | 9 |
| `(*log/slog.Logger).Info` | `no-entry:std` | 11 | 1 |
| `(*strings.Replacer).Replace` | `no-entry:std` | 11 | 0 |
| `(reflect.Value).FieldByIndex` | `no-entry:std` | 11 | 0 |
| `context.WithTimeout` | `no-entry:std` | 11 | 0 |
| `unicode.ToLower` | `no-entry:std` | 11 | 11 |
| `(reflect.Value).MapKeys` | `no-entry:std` | 10 | 0 |
| `(reflect.Value).Uint` | `no-entry:std` | 10 | 0 |
| `flag.Args` | `no-entry:std` | 10 | 0 |
| `strconv.FormatFloat` | `no-entry:std` | 10 | 3 |
| `(*bytes.Reader).Read` | `no-entry:std` | 9 | 0 |
| `(*net/http.Client).Do` | `no-entry:std` | 9 | 0 |
| `(reflect.Value).CanSet` | `no-entry:std` | 9 | 0 |
| `(reflect.Value).SetMapIndex` | `no-entry:std` | 9 | 0 |
| `bytes.NewReader` | `no-entry:std` | 9 | 0 |
| `io.ReadFull` | `no-entry:std` | 9 | 2 |
| `net/http.ListenAndServe` | `no-entry:std` | 9 | 0 |
| `reflect.MakeSlice` | `no-entry:std` | 9 | 0 |
| `(*strings.Reader).Read` | `no-entry:std` | 8 | 0 |
| `(crypto.Hash).Available` | `no-entry:std` | 8 | 0 |

### Refusals made only when a proof fails

A census proves nothing, so it makes these wherever they are reached; the prover would often prove what they ask.

| class | functions met in | the only thing met | top details |
| --- | --- | --- | --- |
| `error:compare-unproved` | 3 | 0 |  |
| `format:length-unknown` | 1 | 1 |  |
| `global:unreliable` | 2 | 1 |  |

### Panics of the verifier (limit:internal)

- `github.com/modelcontextprotocol/go-sdk/mcp.(*streamableServerConn).Write`: runtime error: slice bounds out of range [:-1]; at (*fnVerifier).rangeStmt.func8() < (*fnVerifier).unsupported < (*fnVerifier).branch < (*fnVerifier).appendTo < (*fnVerifier).assign < (*fnVerifier).stmt < (*fnVerifier).seq.func2 < (*fnVerifier).censusStmt
- `github.com/coder/acp-go-sdk/example/gemini.main`: runtime error: slice bounds out of range [984:983]; at (*fnVerifier).loop < (*fnVerifier).forStmt < (*fnVerifier).seq.func2 < (*fnVerifier).censusStmt < (*fnVerifier).seq < (*fnVerifier).seq.func1 < (*fnVerifier).censusStmt.func2 < (*fnVerifier).logging.func1

Functions of generated files, left out of every count above: 4853.

### Modules of modules

| module | functions | get through | not looked at in full | first three classes (functions stopped) |
| --- | --- | --- | --- | --- |
| `github.com/BurntSushi/toml` | 271 | 73 | 4 | `recursion:through-call` (73), `no-entry:std` (70), `type:array-in-struct` (63) |
| `github.com/Masterminds/semver/v3` | 61 | 53 | 0 | `no-entry:std` (4), `call:initialiser-only` (2), `format:runs-code` (1) |
| `github.com/anmitsu/go-shlex` | 11 | 5 | 0 | `no-entry:std` (3), `recursion:through-call` (2), `func-value:calls-values` (1) |
| `github.com/aymanbagabas/go-udiff` | 79 | 55 | 4 | `generic:called` (8), `recursion:through-value` (5), `no-entry:std` (4) |
| `github.com/buger/jsonparser` | 137 | 65 | 0 | `recursion:through-value` (62), `pointer:to-non-struct` (11), `convert:value` (4) |
| `github.com/coder/acp-go-sdk` | 151 | 61 | 3 | `no-entry:std` (32), `convert:to-error` (19), `format:runs-code` (19) |
| `github.com/coreos/go-oidc/v3` | 59 | 11 | 0 | `no-entry:std` (23), `error:unknown-origin` (12), `recursion:through-call` (12) |
| `github.com/dlclark/regexp2` | 300 | 232 | 2 | `no-entry:std` (24), `convert:value` (12), `global:read` (12) |
| `github.com/dustin/go-humanize` | 36 | 19 | 0 | `no-entry:std` (14), `stmt:range-other` (2), `call:initialiser-only` (1) |
| `github.com/emirpasic/gods` | 739 | 288 | 0 | `recursion:through-call` (312), `format:runs-code` (37), `recursion:through-value` (32) |
| `github.com/fatih/structtag` | 16 | 16 | 0 |  |
| `github.com/felixge/httpsnoop` | 18 | 11 | 0 | `scoped:kept` (3), `format:slice-pack` (2), `recursion:through-value` (2) |
| `github.com/fzipp/gocyclo` | 29 | 15 | 0 | `no-entry:std` (8), `recursion:through-call` (6), `format:runs-code` (3) |
| `github.com/go-openapi/jsonpointer` | 39 | 13 | 0 | `no-entry:std` (16), `recursion:through-call` (14), `global:read` (6) |
| `github.com/go-sql-driver/mysql` | 192 | 66 | 4 | `no-entry:std` (63), `recursion:through-call` (56), `recursion:through-method` (33) |
| `github.com/golang-jwt/jwt/v5` | 124 | 61 | 1 | `no-entry:std` (30), `func-value:calls-values` (11), `iface-method:no-contract` (9) |
| `github.com/google/go-cmp` | 339 | 191 | 4 | `recursion:through-call` (60), `no-entry:std` (57), `iface-method:no-contract` (40) |
| `github.com/google/jsonschema-go` | 65 | 11 | 7 | `no-entry:std` (33), `recursion:through-call` (19), `expr:index` (10) |
| `github.com/google/shlex` | 10 | 5 | 0 | `recursion:through-call` (3), `no-entry:std` (2), `convert:value` (1) |
| `github.com/google/uuid` | 71 | 29 | 0 | `no-entry:std` (17), `recursion:through-call` (17), `global:read` (10) |
| `github.com/gorilla/websocket` | 132 | 36 | 3 | `no-entry:std` (44), `recursion:through-call` (34), `recursion:through-method` (23) |
| `github.com/hashicorp/go-version` | 53 | 47 | 0 | `call:initialiser-only` (3), `call:multi-value-args` (1), `copy:elements` (1) |
| `github.com/hashicorp/golang-lru/v2` | 77 | 0 | 77 | `generic:declared` (77) |
| `github.com/hashicorp/hcl` | 181 | 106 | 0 | `recursion:through-call` (34), `no-entry:std` (30), `format:runs-code` (16) |
| `github.com/jpillora/backoff` | 5 | 1 | 0 | `no-entry:std` (4), `address-of:field` (2) |
| `github.com/kevinburke/ssh_config` | 80 | 53 | 1 | `channel:use` (4), `func-value:calls-values` (4), `global:read` (4) |
| `github.com/kisielk/errcheck` | 48 | 9 | 0 | `no-entry:std` (27), `recursion:through-call` (14), `global:read` (7) |
| `github.com/lucasb-eyer/go-colorful` | 169 | 106 | 1 | `call:multi-value-args` (21), `no-entry:std` (20), `assign:target` (10) |
| `github.com/magiconair/properties` | 141 | 40 | 0 | `recursion:through-value` (45), `no-entry:std` (24), `global:read` (17) |
| `github.com/mitchellh/mapstructure` | 42 | 2 | 1 | `no-entry:std` (33), `recursion:through-call` (23), `iface-method:no-contract` (21) |
| `github.com/modelcontextprotocol/go-sdk` | 955 | 292 | 65 | `no-entry:std` (177), `recursion:through-call` (157), `error:unknown-origin` (123) |
| `github.com/pelletier/go-toml` | 322 | 154 | 4 | `no-entry:std` (47), `recursion:through-call` (39), `func-value:calls-values` (32) |
| `github.com/sergi/go-diff` | 63 | 34 | 0 | `convert:value` (16), `no-entry:std` (7), `append:in-expression` (2) |

## Corpus modules, each module weighted equally

- functions with a body: 33.0, of which not loaded: 0.0
- get through: 15.1 (45.6%), of which 0.0 only past refusals made when a proof fails
- not looked at in full (a statement no attempt entered, or the census stopped): 1.4, with 9.7 statements not entered
- reach what only a declaration of the trust file allows: 0.3
- assume a callee, method, or function type of the module with the weakest contract: 16.8

### Refusals by class

| class | functions stopped | stopped alone | first cause | not looked at in full | top details (stopped, alone) |
| --- | --- | --- | --- | --- | --- |
| `no-entry:std` | 7.6 | 2.7 | 5.8 | 0.1 | `reflect.ValueOf` (1.0, 0.0); `(reflect.Value).Type` (0.9, 0.0); `(reflect.Value).Kind` (0.8, 0.0) |
| `recursion:through-call` | 4.7 | 1.6 | 2.4 | 0.1 | `reflect.ValueOf` (0.6, 0.0); `(*bufio.Reader).ReadRune` (0.5, 0.4); `(reflect.Value).Kind` (0.4, 0.0) |
| `iface-method:no-contract` | 1.6 | 0.2 | 0.3 | 0.1 | `(reflect.Type).Kind` (0.6, 0.1); `(reflect.Type).Elem` (0.5, 0.0); `(reflect.Type).Key` (0.2, 0.0) |
| `recursion:through-value` | 1.5 | 0.7 | 1.1 | 0.0 | `cb` (0.5, 0.4); `ErrorHandler` (0.3, 0.2); `apply` (0.1, 0.0) |
| `format:runs-code` | 1.4 | 0.3 | 0.4 | 0.1 |  |
| `global:read` | 1.3 | 0.2 | 0.5 | 0.0 |  |
| `generic:declared` | 1.2 | 0.0 | 1.2 | 1.2 |  |
| `error:unknown-origin` | 1.1 | 0.1 | 0.2 | 0.0 | `formatted` (0.9, 0.1); `Error called` (0.2, 0.0); `errors.Is` (0.1, 0.0) |
| `func-value:calls-values` | 0.9 | 0.3 | 0.4 | 0.0 |  |
| `func-value:no-contract` | 0.8 | 0.1 | 0.3 | 0.0 | `func() time.Time` (0.1, 0.0); `func(github.com/felixge/httpsnoop.WriteHeaderFunc) github.com/felixge/httpsnoop.WriteHeaderFunc` (0.1, 0.0); `func(mapKey string, fieldName string) bool` (0.0, 0.0) |
| `recursion:through-method` | 0.7 | 0.1 | 0.2 | 0.0 | `(github.com/go-sql-driver/mysql.Logger).Print` (0.1, 0.0); `(io.Closer).Close` (0.1, 0.0); `(net.Conn).Write` (0.1, 0.0) |
| `assign:target` | 0.6 | 0.1 | 0.2 | 0.0 |  |
| `convert:value` | 0.5 | 0.3 | 0.4 | 0.0 | `[]rune to string` (0.3, 0.1); `string to []rune` (0.2, 0.1); `unsafe.Pointer to *string` (0.0, 0.0) |
| `pointer:to-non-struct` | 0.5 | 0.1 | 0.4 | 0.0 | `*error` (0.1, 0.0); `*[]byte` (0.1, 0.0); `*any` (0.1, 0.0) |
| `channel:use` | 0.5 | 0.1 | 0.2 | 0.0 | `chan struct{}` (0.2, 0.0); `<-chan struct{}` (0.2, 0.0); `<-chan time.Time` (0.0, 0.0) |
| `address-of:field` | 0.4 | 0.0 | 0.0 | 0.0 | `b.attempt` (0.4, 0.0); `x.Cursor` (0.0, 0.0); `x.NextCursor` (0.0, 0.0) |
| `handover:unknown-code` | 0.4 | 0.1 | 0.1 | 0.0 |  |
| `expr:index` | 0.4 | 0.1 | 0.1 | 0.0 | `map[*github.com/google/jsonschema-go/jsonschema.Schema]*github.com/google/jsonschema-go/jsonschema.resolvedInfo` (0.1, 0.0); `[6]byte` (0.1, 0.0); `map[*go/ast.Ident]go/types.Object` (0.0, 0.0) |
| `scoped:kept` | 0.4 | 0.0 | 0.4 | 0.0 |  |
| `convert:to-error` | 0.3 | 0.1 | 0.1 | 0.0 |  |
| `type:array-in-struct` | 0.3 | 0.1 | 0.3 | 0.0 | `*github.com/BurntSushi/toml.lexer` (0.2, 0.1); `*github.com/emirpasic/gods/trees/avltree.Node` (0.0, 0.0); `github.com/BurntSushi/toml.lexer` (0.0, 0.0) |
| `generic:called` | 0.3 | 0.2 | 0.2 | 0.0 | `github.com/aymanbagabas/go-udiff/lcs.commonPrefixLen` (0.0, 0.0); `github.com/aymanbagabas/go-udiff/lcs.commonSuffixLen` (0.0, 0.0); `github.com/google/jsonschema-go/jsonschema.Ptr` (0.0, 0.0) |
| `dyntype:assert` | 0.3 | 0.0 | 0.1 | 0.0 |  |
| `type:map-key` | 0.3 | 0.0 | 0.2 | 0.0 | `map[*github.com/google/jsonschema-go/jsonschema.Schema]*github.com/google/jsonschema-go/jsonschema.resolvedInfo` (0.1, 0.0); `map[reflect.Type]bool` (0.0, 0.0); `map[interface{}]interface{}` (0.0, 0.0) |
| `json:decode` | 0.3 | 0.1 | 0.1 | 0.0 |  |
| `format:slice-pack` | 0.2 | 0.2 | 0.2 | 0.0 |  |
| `convert:iface-no-contract` | 0.2 | 0.1 | 0.1 | 0.0 | `(go/ast.Visitor).Visit` (0.1, 0.0); `(github.com/modelcontextprotocol/go-sdk/mcp.Params).GetMeta` (0.1, 0.0); `(encoding/json/v2.Marshaler).MarshalJSON` (0.0, 0.0) |
| `recursion:through-format` | 0.2 | 0.0 | 0.1 | 0.0 | `fmt.Sprintf` (0.2, 0.0); `fmt.Errorf` (0.0, 0.0); `fmt.Fprintf` (0.0, 0.0) |
| `no-entry:other` | 0.2 | 0.0 | 0.1 | 0.0 | `(*golang.org/x/oauth2.Config).Exchange` (0.1, 0.0); `github.com/go-jose/go-jose/v4.ParseSigned` (0.1, 0.0); `(*golang.org/x/oauth2.Token).Extra` (0.0, 0.0) |
| `call:multi-value-args` | 0.2 | 0.2 | 0.2 | 0.0 |  |
| `json:encode` | 0.2 | 0.1 | 0.1 | 0.0 |  |
| `error:sentinel` | 0.2 | 0.1 | 0.1 | 0.0 |  |
| `func-literal:value` | 0.2 | 0.0 | 0.2 | 0.0 |  |
| `convert:multi-value` | 0.2 | 0.0 | 0.0 | 0.0 |  |
| `convert:unplaced` | 0.2 | 0.0 | 0.0 | 0.0 |  |
| `select:statement` | 0.2 | 0.0 | 0.0 | 0.0 |  |
| `copy:elements` | 0.2 | 0.1 | 0.1 | 0.0 |  |
| `goroutine:go` | 0.2 | 0.0 | 0.0 | 0.0 |  |
| `call:initialiser-only` | 0.2 | 0.1 | 0.1 | 0.0 |  |
| `dyntype:switch` | 0.1 | 0.0 | 0.0 | 0.0 |  |
| `global:assign` | 0.1 | 0.0 | 0.1 | 0.0 |  |
| `stmt:range-other` | 0.1 | 0.0 | 0.0 | 0.0 | `map[float64]string` (0.1, 0.0); `map[interface{}]struct{}` (0.0, 0.0); `map[reflect.Value]struct{}` (0.0, 0.0) |
| `call:builtin` | 0.1 | 0.0 | 0.0 | 0.0 | `close` (0.1, 0.0); `copy` (0.0, 0.0); `imag` (0.0, 0.0) |
| `assign:multi-value` | 0.1 | 0.0 | 0.0 | 0.0 | `+=` (0.0, 0.0) |
| `append:in-expression` | 0.1 | 0.0 | 0.0 | 0.0 |  |
| `copy:value-with-state` | 0.1 | 0.1 | 0.1 | 0.0 |  |
| `generic:iterator` | 0.1 | 0.0 | 0.0 | 0.0 |  |
| `json:form` | 0.1 | 0.0 | 0.0 | 0.0 |  |
| `generic:type-args` | 0.1 | 0.0 | 0.0 | 0.0 |  |
| `expr:value-shape` | 0.1 | 0.0 | 0.0 | 0.0 |  |
| `limit:paths` | 0.1 | 0.0 | 0.0 | 0.1 |  |
| `pointer:to-array` | 0.1 | 0.0 | 0.1 | 0.0 | `*github.com/google/uuid.UUID` (0.1, 0.0) |
| `global:type` | 0.1 | 0.0 | 0.0 | 0.0 |  |
| `func-value:made-from` | 0.1 | 0.0 | 0.0 | 0.0 |  |
| `func-literal:signature` | 0.1 | 0.0 | 0.1 | 0.0 |  |
| `func-literal:captures` | 0.1 | 0.0 | 0.0 | 0.0 |  |
| `type:array` | 0.1 | 0.0 | 0.0 | 0.0 | `[6][2]float64` (0.0, 0.0); `[2]github.com/google/go-cmp/cmp/internal/value.Pointer` (0.0, 0.0); `[12]sync.Pool` (0.0, 0.0) |
| `convert:iface-array` | 0.1 | 0.0 | 0.0 | 0.0 |  |
| `type:unsafe-pointer` | 0.1 | 0.0 | 0.0 | 0.0 | `unsafe.Pointer` (0.1, 0.0) |
| `convert:iface-foreign-impl` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `recover:call` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `address-of:global` | 0.0 | 0.0 | 0.0 | 0.0 | `upgrader` (0.0, 0.0); `fieldCache` (0.0, 0.0) |
| `stmt:expression` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `stmt:goto` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `iface-method:no-contract-other` | 0.0 | 0.0 | 0.0 | 0.0 | `(golang.org/x/oauth2.TokenSource).Token` (0.0, 0.0); `(github.com/go-jose/go-jose/v4.Signer).Sign` (0.0, 0.0) |
| `type:uintptr` | 0.0 | 0.0 | 0.0 | 0.0 | `uintptr` (0.0, 0.0); `syscall.Errno` (0.0, 0.0) |
| `convert:iface-states` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `closure:recursive` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `contract:unusable` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `defer:form` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `generic:method-call` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `no-entry:impossible` | 0.0 | 0.0 | 0.0 | 0.0 | `io.Copy` (0.0, 0.0); `io.CopyN` (0.0, 0.0); `(*bytes.Buffer).ReadFrom` (0.0, 0.0) |
| `type:complex` | 0.0 | 0.0 | 0.0 | 0.0 | `complex128` (0.0, 0.0) |
| `type:array-elem` | 0.0 | 0.0 | 0.0 | 0.0 | `github.com/google/uuid.UUID` (0.0, 0.0); `github.com/lucasb-eyer/go-colorful.edgeIdxs` (0.0, 0.0); `[2]github.com/google/go-cmp/cmp/internal/value.Pointer` (0.0, 0.0) |
| `expr:other` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `stmt:range-form` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `convert:iface-optional` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `type:iface-literal` | 0.0 | 0.0 | 0.0 | 0.0 | `net.Error` (0.0, 0.0); `github.com/modelcontextprotocol/go-sdk/mcp.binder[*github.com/modelcontextprotocol/go-sdk/mcp.ClientSession, *github.com/modelcontextprotocol/go-sdk/mcp.clientSessionState]` (0.0, 0.0); `github.com/modelcontextprotocol/go-sdk/mcp.binder[*github.com/modelcontextprotocol/go-sdk/mcp.ServerSession, *github.com/modelcontextprotocol/go-sdk/mcp.ServerSessionState]` (0.0, 0.0) |
| `address-of:element` | 0.0 | 0.0 | 0.0 | 0.0 | `b[0]` (0.0, 0.0); `oldText[0]` (0.0, 0.0) |
| `exit:context` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `func-value:method-value` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `convert:iface-wraps-writer` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `scoped:written` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `operator:nil-compare` | 0.0 | 0.0 | 0.0 | 0.0 | `*github.com/emirpasic/gods/trees/avltree.Node` (0.0, 0.0); `<-chan struct{}` (0.0, 0.0); `chan struct{}` (0.0, 0.0) |
| `defer:in-loop` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `limit:internal` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `handover:sort` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `iface-method:form` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `assign:in-place` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `limit:attempts` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `generic:as-value` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `handover:footprint` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `annotation:unreadable` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `dyntype:errors-as` | 0.0 | 0.0 | 0.0 | 0.0 |  |

### Refusals by group

| group | functions stopped | stopped alone | first cause | not looked at in full | top details (stopped, alone) |
| --- | --- | --- | --- | --- | --- |
| `no-entry` | 7.8 | 2.8 | 5.9 | 0.1 |  |
| `recursion` | 6.5 | 2.8 | 3.9 | 0.1 |  |
| `generic` | 1.7 | 0.2 | 1.5 | 1.2 |  |
| `iface-method` | 1.7 | 0.2 | 0.3 | 0.1 |  |
| `func-value` | 1.6 | 0.5 | 0.7 | 0.1 |  |
| `format` | 1.6 | 0.5 | 0.5 | 0.1 |  |
| `global` | 1.4 | 0.3 | 0.6 | 0.0 |  |
| `convert` | 1.4 | 0.5 | 0.6 | 0.0 |  |
| `error` | 1.3 | 0.2 | 0.3 | 0.0 |  |
| `type` | 0.8 | 0.2 | 0.6 | 0.0 |  |
| `assign` | 0.7 | 0.1 | 0.2 | 0.0 |  |
| `pointer` | 0.6 | 0.2 | 0.4 | 0.0 |  |
| `json` | 0.5 | 0.2 | 0.3 | 0.0 |  |
| `call` | 0.5 | 0.3 | 0.3 | 0.0 |  |
| `channel` | 0.5 | 0.1 | 0.2 | 0.0 |  |
| `expr` | 0.5 | 0.1 | 0.1 | 0.0 |  |
| `address-of` | 0.5 | 0.0 | 0.0 | 0.0 |  |
| `dyntype` | 0.4 | 0.0 | 0.1 | 0.0 |  |
| `handover` | 0.4 | 0.1 | 0.1 | 0.0 |  |
| `scoped` | 0.4 | 0.0 | 0.4 | 0.0 |  |
| `func-literal` | 0.3 | 0.0 | 0.2 | 0.0 |  |
| `copy` | 0.3 | 0.2 | 0.2 | 0.0 |  |
| `stmt` | 0.2 | 0.0 | 0.1 | 0.0 |  |
| `select` | 0.2 | 0.0 | 0.0 | 0.0 |  |
| `goroutine` | 0.2 | 0.0 | 0.0 | 0.0 |  |
| `append` | 0.1 | 0.0 | 0.0 | 0.0 |  |
| `limit` | 0.1 | 0.0 | 0.0 | 0.1 |  |
| `recover` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `defer` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `closure` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `contract` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `exit` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `operator` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `annotation` | 0.0 | 0.0 | 0.0 | 0.0 |  |

### Greedy order of classes

Get through with nothing fixed: 15.1.

| step | fixed | let through by it | let through in all |
| --- | --- | --- | --- |
| 1 | `no-entry:std` | 2.7 | 17.8 |
| 2 | `recursion:through-call` | 2.2 | 19.9 |
| 3 | `recursion:through-value` | 0.9 | 20.8 |
| 4 | `global:read` | 0.6 | 21.5 |
| 5 | `iface-method:no-contract` | 0.6 | 22.1 |
| 6 | `format:runs-code` | 0.7 | 22.8 |
| 7 | `error:unknown-origin` | 0.5 | 23.3 |
| 8 | `convert:value` | 0.4 | 23.8 |
| 9 | `func-value:calls-values` | 0.4 | 24.2 |
| 10 | `address-of:field` | 0.4 | 24.6 |
| 11 | `recursion:through-method` | 0.3 | 25.0 |
| 12 | `func-value:no-contract` | 0.3 | 25.3 |
| 13 | `scoped:kept` | 0.3 | 25.5 |
| 14 | `type:array-in-struct` | 0.2 | 25.7 |
| 15 | `pointer:to-non-struct` | 0.2 | 26.0 |
| 16 | `assign:target` | 0.2 | 26.2 |
| 17 | `generic:called` | 0.2 | 26.4 |
| 18 | `call:multi-value-args` | 0.2 | 26.6 |
| 19 | `format:slice-pack` | 0.2 | 26.8 |
| 20 | `convert:iface-no-contract` | 0.2 | 27.0 |

### Greedy order of groups

Get through with nothing fixed: 15.1.

| step | fixed | let through by it | let through in all |
| --- | --- | --- | --- |
| 1 | `no-entry` | 2.8 | 17.8 |
| 2 | `recursion` | 3.4 | 21.3 |
| 3 | `convert` | 0.8 | 22.1 |
| 4 | `func-value` | 0.8 | 22.9 |
| 5 | `global` | 0.8 | 23.7 |
| 6 | `format` | 0.8 | 24.5 |
| 7 | `iface-method` | 0.9 | 25.4 |
| 8 | `error` | 0.8 | 26.2 |
| 9 | `address-of` | 0.4 | 26.6 |
| 10 | `type` | 0.4 | 27.0 |
| 11 | `call` | 0.4 | 27.4 |
| 12 | `json` | 0.3 | 27.8 |
| 13 | `assign` | 0.4 | 28.1 |
| 14 | `pointer` | 0.4 | 28.5 |
| 15 | `expr` | 0.4 | 28.9 |
| 16 | `generic` | 0.4 | 29.3 |
| 17 | `scoped` | 0.3 | 29.6 |
| 18 | `func-literal` | 0.3 | 29.9 |
| 19 | `handover` | 0.3 | 30.1 |
| 20 | `dyntype` | 0.4 | 30.5 |

### Greedy order of classes, with what the project writes for other modules (no-entry:other and the classes ending in -other) left out of the causes

Get through with nothing fixed: 15.1.

| step | fixed | let through by it | let through in all |
| --- | --- | --- | --- |
| 1 | `no-entry:std` | 2.7 | 17.8 |
| 2 | `recursion:through-call` | 2.2 | 20.0 |
| 3 | `recursion:through-value` | 0.9 | 20.9 |
| 4 | `global:read` | 0.6 | 21.5 |
| 5 | `iface-method:no-contract` | 0.6 | 22.2 |
| 6 | `format:runs-code` | 0.7 | 22.9 |
| 7 | `error:unknown-origin` | 0.6 | 23.5 |
| 8 | `func-value:calls-values` | 0.4 | 23.9 |
| 9 | `convert:value` | 0.4 | 24.4 |
| 10 | `address-of:field` | 0.4 | 24.8 |
| 11 | `recursion:through-method` | 0.3 | 25.1 |
| 12 | `func-value:no-contract` | 0.3 | 25.4 |
| 13 | `scoped:kept` | 0.3 | 25.7 |
| 14 | `type:array-in-struct` | 0.2 | 25.9 |
| 15 | `pointer:to-non-struct` | 0.2 | 26.1 |
| 16 | `assign:target` | 0.2 | 26.3 |
| 17 | `generic:called` | 0.2 | 26.6 |
| 18 | `call:multi-value-args` | 0.2 | 26.8 |
| 19 | `format:slice-pack` | 0.2 | 27.0 |
| 20 | `convert:iface-no-contract` | 0.2 | 27.2 |

### Greedy order of groups, with what the project writes for other modules (no-entry:other and the classes ending in -other) left out of the causes

Get through with nothing fixed: 15.1.

| step | fixed | let through by it | let through in all |
| --- | --- | --- | --- |
| 1 | `recursion` | 2.8 | 17.9 |
| 2 | `no-entry` | 3.4 | 21.3 |
| 3 | `convert` | 0.8 | 22.1 |
| 4 | `func-value` | 0.8 | 22.9 |
| 5 | `global` | 0.8 | 23.7 |
| 6 | `format` | 0.8 | 24.6 |
| 7 | `iface-method` | 0.9 | 25.4 |
| 8 | `error` | 0.8 | 26.2 |
| 9 | `type` | 0.4 | 26.7 |
| 10 | `call` | 0.4 | 27.1 |
| 11 | `address-of` | 0.4 | 27.5 |
| 12 | `assign` | 0.4 | 27.9 |
| 13 | `json` | 0.4 | 28.3 |
| 14 | `pointer` | 0.4 | 28.6 |
| 15 | `generic` | 0.4 | 29.0 |
| 16 | `expr` | 0.4 | 29.4 |
| 17 | `scoped` | 0.3 | 29.7 |
| 18 | `func-literal` | 0.3 | 30.0 |
| 19 | `handover` | 0.3 | 30.2 |
| 20 | `dyntype` | 0.4 | 30.6 |

### Callees without an entry

| callee | class | functions stopped | stopped alone |
| --- | --- | --- | --- |
| `reflect.ValueOf` | `no-entry:std` | 1.0 | 0.0 |
| `(reflect.Value).Type` | `no-entry:std` | 0.9 | 0.0 |
| `(reflect.Value).Kind` | `no-entry:std` | 0.8 | 0.0 |
| `(reflect.Value).Interface` | `no-entry:std` | 0.6 | 0.0 |
| `reflect.Indirect` | `no-entry:std` | 0.5 | 0.0 |
| `(reflect.Value).Set` | `no-entry:std` | 0.5 | 0.0 |
| `(reflect.Value).Elem` | `no-entry:std` | 0.4 | 0.0 |
| `(reflect.Value).Len` | `no-entry:std` | 0.4 | 0.0 |
| `(reflect.Value).IsValid` | `no-entry:std` | 0.3 | 0.0 |
| `(reflect.Value).IsNil` | `no-entry:std` | 0.3 | 0.0 |
| `(reflect.Value).Index` | `no-entry:std` | 0.3 | 0.0 |
| `(reflect.Value).String` | `no-entry:std` | 0.3 | 0.0 |
| `reflect.New` | `no-entry:std` | 0.2 | 0.0 |
| `(*strings.Reader).Read` | `no-entry:std` | 0.2 | 0.0 |
| `strings.NewReader` | `no-entry:std` | 0.2 | 0.0 |
| `reflect.TypeOf` | `no-entry:std` | 0.2 | 0.0 |
| `(reflect.Value).Bool` | `no-entry:std` | 0.2 | 0.0 |
| `math/rand.Float64` | `no-entry:std` | 0.2 | 0.2 |
| `sync/atomic.AddUint64` | `no-entry:std` | 0.2 | 0.0 |
| `sync/atomic.LoadUint64` | `no-entry:std` | 0.2 | 0.0 |
| `sync/atomic.StoreUint64` | `no-entry:std` | 0.2 | 0.2 |
| `errors.Join` | `no-entry:std` | 0.2 | 0.0 |
| `(*bufio.Reader).ReadRune` | `no-entry:std` | 0.2 | 0.0 |
| `(reflect.Value).MapIndex` | `no-entry:std` | 0.2 | 0.0 |
| `context.Background` | `no-entry:std` | 0.2 | 0.0 |
| `(reflect.Value).FieldByIndex` | `no-entry:std` | 0.2 | 0.0 |
| `flag.Parse` | `no-entry:std` | 0.1 | 0.0 |
| `(reflect.Value).SetMapIndex` | `no-entry:std` | 0.1 | 0.0 |
| `(reflect.Value).CanAddr` | `no-entry:std` | 0.1 | 0.0 |
| `(*strings.Replacer).Replace` | `no-entry:std` | 0.1 | 0.0 |
| `strconv.FormatFloat` | `no-entry:std` | 0.1 | 0.1 |
| `(reflect.Value).FieldByName` | `no-entry:std` | 0.1 | 0.0 |
| `(reflect.Value).Float` | `no-entry:std` | 0.1 | 0.0 |
| `strconv.ParseFloat` | `no-entry:std` | 0.1 | 0.1 |
| `(reflect.Value).CanSet` | `no-entry:std` | 0.1 | 0.0 |
| `(reflect.Value).Int` | `no-entry:std` | 0.1 | 0.0 |
| `io.ReadFull` | `no-entry:std` | 0.1 | 0.0 |
| `net/url.Parse` | `no-entry:std` | 0.1 | 0.0 |
| `(*math/big.Int).Cmp` | `no-entry:std` | 0.1 | 0.0 |
| `reflect.MakeMap` | `no-entry:std` | 0.1 | 0.0 |
| `(reflect.Value).MapKeys` | `no-entry:std` | 0.1 | 0.0 |
| `strings.ContainsRune` | `no-entry:std` | 0.1 | 0.1 |
| `(*encoding/base64.Encoding).EncodeToString` | `no-entry:std` | 0.1 | 0.0 |
| `(*encoding/json.Decoder).Token` | `no-entry:std` | 0.1 | 0.0 |
| `(*net/url.URL).String` | `no-entry:std` | 0.1 | 0.0 |
| `(*bufio.Reader).UnreadRune` | `no-entry:std` | 0.1 | 0.0 |
| `unicode.IsNumber` | `no-entry:std` | 0.1 | 0.1 |
| `(reflect.StructTag).Get` | `no-entry:std` | 0.1 | 0.0 |
| `(reflect.Value).Field` | `no-entry:std` | 0.1 | 0.0 |
| `reflect.Zero` | `no-entry:std` | 0.1 | 0.0 |

### Refusals made only when a proof fails

A census proves nothing, so it makes these wherever they are reached; the prover would often prove what they ask.

| class | functions met in | the only thing met | top details |
| --- | --- | --- | --- |
| `error:compare-unproved` | 0.0 | 0.0 |  |
| `format:length-unknown` | 0.0 | 0.0 |  |
| `global:unreliable` | 0.0 | 0.0 |  |

### Panics of the verifier (limit:internal)

- `github.com/modelcontextprotocol/go-sdk/mcp.(*streamableServerConn).Write`: runtime error: slice bounds out of range [:-1]; at (*fnVerifier).rangeStmt.func8() < (*fnVerifier).unsupported < (*fnVerifier).branch < (*fnVerifier).appendTo < (*fnVerifier).assign < (*fnVerifier).stmt < (*fnVerifier).seq.func2 < (*fnVerifier).censusStmt
- `github.com/coder/acp-go-sdk/example/gemini.main`: runtime error: slice bounds out of range [984:983]; at (*fnVerifier).loop < (*fnVerifier).forStmt < (*fnVerifier).seq.func2 < (*fnVerifier).censusStmt < (*fnVerifier).seq < (*fnVerifier).seq.func1 < (*fnVerifier).censusStmt.func2 < (*fnVerifier).logging.func1

## All corpora

- functions with a body: 18013, of which not loaded: 1748
- get through: 7199 (40.0%), of which 4 only past refusals made when a proof fails
- not looked at in full (a statement no attempt entered, or the census stopped): 453, with 4453 statements not entered
- reach what only a declaration of the trust file allows: 131
- assume a callee, method, or function type of the module with the weakest contract: 10183

### Refusals by class

| class | functions stopped | stopped alone | first cause | not looked at in full | top details (stopped, alone) |
| --- | --- | --- | --- | --- | --- |
| `recursion:through-call` | 3317 | 1329 | 2059 | 63 | `(*sync.Pool).Put` (175, 92); `(*sync.Pool).Get` (164, 39); `reflect.ValueOf` (128, 16) |
| `package:not-loaded` | 1748 | 0 | 1748 | 1748 |  |
| `func-value:calls-values` | 1004 | 252 | 409 | 30 |  |
| `recursion:through-method` | 988 | 370 | 533 | 22 | `(io.Writer).Write` (118, 53); `(io.Closer).Close` (69, 20); `(io.Reader).Read` (65, 33) |
| `no-entry:std` | 966 | 295 | 650 | 18 | `reflect.ValueOf` (89, 0); `(reflect.Value).Type` (85, 0); `(reflect.Value).Kind` (69, 1) |
| `global:read` | 896 | 210 | 462 | 28 |  |
| `recursion:through-value` | 697 | 227 | 364 | 12 | `f` (90, 28); `fn` (82, 25); `cb` (62, 51) |
| `type:array-in-struct` | 697 | 345 | 621 | 13 | `*text/template/parse.Tree` (136, 76); `*github.com/BurntSushi/toml.lexer` (62, 29); `*regexp/syntax.Regexp` (46, 20) |
| `func-value:no-contract` | 514 | 83 | 178 | 24 | `func()` (68, 5); `encoding/json/v2.marshaler` (18, 0); `encoding/json/v2.unmarshaler` (17, 0) |
| `assign:target` | 465 | 96 | 186 | 10 |  |
| `error:unknown-origin` | 436 | 60 | 99 | 17 | `formatted` (283, 26); `Error called` (105, 24); `errors.Is` (46, 4) |
| `dyntype:assert` | 426 | 54 | 199 | 10 |  |
| `pointer:to-non-struct` | 419 | 138 | 268 | 13 | `*vendor/golang.org/x/crypto/cryptobyte.String` (42, 23); `*[]byte` (35, 9); `*fmt.buffer` (29, 12) |
| `type:uintptr` | 398 | 75 | 272 | 11 | `uintptr` (178, 29); `reflect.flag` (134, 28); `syscall.Errno` (116, 15) |
| `convert:to-error` | 332 | 61 | 95 | 10 |  |
| `generic:declared` | 315 | 0 | 315 | 315 |  |
| `expr:index` | 272 | 7 | 34 | 4 | `map[*go/ast.Ident]go/types.Object` (13, 2); `*archive/tar.headerGNU` (10, 0); `*archive/tar.headerSTAR` (10, 0) |
| `channel:use` | 270 | 35 | 99 | 5 | `<-chan struct{}` (104, 6); `chan struct{}` (95, 4); `<-chan time.Time` (31, 1) |
| `format:runs-code` | 266 | 82 | 94 | 6 |  |
| `generic:called` | 264 | 76 | 137 | 8 | `github.com/modelcontextprotocol/go-sdk/mcp.orZero` (23, 0); `github.com/modelcontextprotocol/go-sdk/mcp.handleSend` (19, 0); `github.com/modelcontextprotocol/go-sdk/mcp.AddTool` (17, 1) |
| `iface-method:no-contract` | 225 | 35 | 72 | 9 | `(reflect.Type).Kind` (71, 9); `(reflect.Type).Elem` (56, 0); `(reflect.Type).Field` (18, 0) |
| `convert:value` | 220 | 34 | 42 | 8 | `[]rune to string` (42, 20); `uintptr to int` (22, 0); `string to []rune` (21, 9) |
| `handover:unknown-code` | 214 | 34 | 56 | 9 |  |
| `convert:iface-no-contract` | 211 | 42 | 92 | 2 | `(github.com/modelcontextprotocol/go-sdk/mcp.Params).GetMeta` (50, 23); `(text/template/parse.Node).Position` (23, 1); `(go/types.Object).Exported` (22, 1) |
| `type:map-key` | 207 | 27 | 113 | 4 | `map[*github.com/spachava753/laas/cmd/vegocensus.fn]float64` (9, 2); `map[interface{}]interface{}` (9, 5); `map[*github.com/modelcontextprotocol/go-sdk/mcp.ServerSession]github.com/modelcontextprotocol/go-sdk/jsonrpc.ID` (8, 0) |
| `type:unsafe-pointer` | 202 | 13 | 77 | 8 | `unsafe.Pointer` (202, 13) |
| `pointer:to-array` | 184 | 57 | 157 | 0 | `*archive/tar.block` (19, 1); `*archive/tar.headerV7` (19, 0); `*hash/crc32.Table` (19, 7) |
| `error:sentinel` | 177 | 25 | 91 | 7 |  |
| `dyntype:switch` | 166 | 31 | 73 | 4 |  |
| `call:builtin` | 161 | 44 | 51 | 2 | `close` (42, 7); `clear` (37, 12); `imag` (30, 0) |
| `recursion:through-format` | 133 | 40 | 74 | 2 | `fmt.Sprintf` (99, 24); `fmt.Errorf` (24, 11); `fmt.Fprintf` (14, 5) |
| `select:statement` | 114 | 3 | 33 | 2 |  |
| `address-of:field` | 107 | 55 | 66 | 5 | `x.v` (32, 32); `xe.Tokens.Last` (10, 0); `m.Last` (5, 4) |
| `type:array` | 101 | 23 | 41 | 0 | `[4]image/jpeg.component` (8, 0); `[16]unicode/utf8.acceptRange` (6, 4); `[1]uintptr` (6, 0) |
| `generic:method-call` | 93 | 23 | 45 | 2 |  |
| `goroutine:go` | 90 | 5 | 9 | 2 |  |
| `scoped:kept` | 89 | 2 | 80 | 4 |  |
| `address-of:global` | 86 | 0 | 0 | 0 | `upgrader` (5, 0); `lookupCache` (4, 0); `mimeTypes` (4, 0) |
| `assign:multi-value` | 83 | 19 | 43 | 1 | `+=` (7, 2); `|=` (4, 4); `^=` (2, 2) |
| `convert:iface-array` | 83 | 22 | 28 | 6 |  |
| `global:assign` | 78 | 9 | 34 | 1 |  |
| `append:in-expression` | 71 | 21 | 31 | 2 |  |
| `expr:value-shape` | 70 | 17 | 47 | 2 |  |
| `json:encode` | 66 | 22 | 43 | 1 |  |
| `generic:type-args` | 61 | 10 | 22 | 0 |  |
| `format:slice-pack` | 60 | 32 | 45 | 0 |  |
| `stmt:range-other` | 57 | 4 | 15 | 1 | `map[interface{}]struct{}` (9, 2); `map[*crypto/x509.policyGraphNode]bool` (3, 0); `map[interface{}]interface{}` (3, 2) |
| `type:complex` | 56 | 9 | 40 | 4 | `complex128` (56, 9); `complex64` (1, 0) |
| `copy:elements` | 55 | 22 | 29 | 2 |  |
| `convert:multi-value` | 54 | 1 | 13 | 2 |  |
| `contract:unusable` | 48 | 7 | 20 | 3 |  |
| `generic:iterator` | 48 | 13 | 18 | 2 |  |
| `recover:call` | 48 | 11 | 16 | 2 |  |
| `recursion:through-trusted` | 48 | 20 | 22 | 1 |  |
| `limit:paths` | 46 | 0 | 6 | 46 |  |
| `no-entry:other` | 45 | 6 | 18 | 0 | `(*golang.org/x/oauth2.Config).Exchange` (7, 0); `(*golang.org/x/oauth2.Token).Extra` (6, 1); `golang.org/x/oauth2.SetAuthURLParam` (6, 1) |
| `convert:unplaced` | 44 | 0 | 0 | 0 |  |
| `json:decode` | 44 | 16 | 26 | 0 |  |
| `func-literal:signature` | 43 | 0 | 43 | 3 |  |
| `stmt:goto` | 43 | 11 | 23 | 14 |  |
| `call:multi-value-args` | 40 | 29 | 32 | 0 |  |
| `stmt:expression` | 38 | 0 | 9 | 1 |  |
| `address-of:element` | 34 | 7 | 7 | 0 | `buf[0]` (5, 0); `b[0]` (3, 0); `x[0]` (3, 0) |
| `convert:iface-by-contract` | 32 | 0 | 5 | 3 |  |
| `json:form` | 32 | 0 | 6 | 0 |  |
| `scoped:written` | 31 | 1 | 26 | 4 |  |
| `func-value:trusted-callee` | 30 | 0 | 6 | 3 |  |
| `convert:iface-states` | 28 | 1 | 6 | 1 |  |
| `func-value:made-from` | 26 | 2 | 9 | 1 |  |
| `operator:nil-compare` | 25 | 0 | 0 | 0 | `*github.com/emirpasic/gods/trees/avltree.Node` (4, 0); `*regexp/syntax.Regexp` (4, 0); `<-chan struct{}` (4, 0) |
| `global:type` | 21 | 1 | 10 | 0 |  |
| `call:initialiser-only` | 15 | 6 | 7 | 0 |  |
| `convert:iface-wraps-writer` | 15 | 0 | 2 | 3 |  |
| `limit:internal` | 15 | 0 | 8 | 15 |  |
| `type:array-elem` | 15 | 8 | 8 | 0 | `[2]uint64` (4, 4); `[2]float64` (2, 0); `[2]int` (2, 1) |
| `type:iface-literal` | 15 | 3 | 6 | 2 | `net.Error` (12, 3); `github.com/modelcontextprotocol/go-sdk/mcp.binder[*github.com/modelcontextprotocol/go-sdk/mcp.ClientSession, *github.com/modelcontextprotocol/go-sdk/mcp.clientSessionState]` (1, 0); `github.com/modelcontextprotocol/go-sdk/mcp.binder[*github.com/modelcontextprotocol/go-sdk/mcp.ServerSession, *github.com/modelcontextprotocol/go-sdk/mcp.ServerSessionState]` (1, 0) |
| `defer:in-loop` | 12 | 2 | 3 | 0 |  |
| `scoped:hidden` | 12 | 3 | 12 | 1 |  |
| `convert:iface-foreign-impl` | 11 | 0 | 0 | 0 |  |
| `func-literal:captures` | 10 | 6 | 7 | 0 |  |
| `global:followed-code` | 10 | 0 | 0 | 2 |  |
| `func-literal:value` | 9 | 1 | 8 | 0 |  |
| `iface-method:form` | 9 | 3 | 8 | 0 |  |
| `no-entry:impossible` | 9 | 0 | 4 | 1 | `io.Copy` (7, 0); `(*bytes.Buffer).ReadFrom` (1, 0); `io.CopyN` (1, 0) |
| `defer:form` | 8 | 0 | 1 | 0 |  |
| `limit:facts` | 8 | 0 | 1 | 8 |  |
| `stmt:range-form` | 8 | 2 | 5 | 0 |  |
| `copy:value-with-state` | 7 | 2 | 7 | 0 |  |
| `exit:context` | 7 | 1 | 1 | 0 |  |
| `expr:other` | 7 | 0 | 5 | 0 |  |
| `func-value:method-value` | 7 | 0 | 1 | 0 |  |
| `closure:recursive` | 6 | 0 | 6 | 0 |  |
| `iface-method:no-contract-other` | 5 | 0 | 2 | 0 | `(golang.org/x/oauth2.TokenSource).Token` (4, 0); `(github.com/go-jose/go-jose/v4.Signer).Sign` (1, 0) |
| `convert:iface-optional` | 4 | 0 | 0 | 1 |  |
| `dyntype:errors-as` | 4 | 0 | 1 | 0 |  |
| `handover:footprint` | 3 | 0 | 1 | 0 |  |
| `handover:sort` | 3 | 0 | 0 | 0 |  |
| `limit:attempts` | 3 | 0 | 0 | 3 |  |
| `annotation:unreadable` | 2 | 1 | 1 | 1 |  |
| `func-value:method-expr` | 2 | 1 | 1 | 0 |  |
| `generic:as-value` | 2 | 0 | 0 | 0 |  |
| `assign:in-place` | 1 | 0 | 0 | 0 |  |
| `call:form` | 1 | 0 | 0 | 0 |  |
| `convert:iface-no-contract-other` | 1 | 0 | 0 | 0 | `(golang.org/x/tools/go/analysis.Fact).AFact` (1, 0) |
| `handover:apart` | 1 | 0 | 0 | 0 |  |
| `operator:pointer` | 1 | 0 | 1 | 0 |  |

### Refusals by group

| group | functions stopped | stopped alone | first cause | not looked at in full | top details (stopped, alone) |
| --- | --- | --- | --- | --- | --- |
| `recursion` | 4506 | 2132 | 3052 | 66 |  |
| `package` | 1748 | 0 | 1748 | 1748 |  |
| `type` | 1491 | 534 | 1178 | 29 |  |
| `func-value` | 1434 | 357 | 604 | 42 |  |
| `no-entry` | 989 | 304 | 672 | 18 |  |
| `convert` | 949 | 168 | 283 | 30 |  |
| `global` | 941 | 240 | 506 | 30 |  |
| `generic` | 758 | 130 | 537 | 327 |  |
| `pointer` | 600 | 195 | 425 | 13 |  |
| `error` | 584 | 87 | 190 | 21 |  |
| `dyntype` | 550 | 88 | 273 | 14 |  |
| `assign` | 509 | 121 | 229 | 11 |  |
| `expr` | 345 | 24 | 86 | 6 |  |
| `format` | 326 | 114 | 139 | 6 |  |
| `channel` | 270 | 35 | 99 | 5 |  |
| `iface-method` | 238 | 38 | 82 | 9 |  |
| `handover` | 221 | 34 | 57 | 9 |  |
| `address-of` | 220 | 64 | 73 | 5 |  |
| `call` | 217 | 79 | 90 | 2 |  |
| `stmt` | 146 | 17 | 52 | 16 |  |
| `json` | 129 | 43 | 75 | 1 |  |
| `scoped` | 121 | 6 | 118 | 7 |  |
| `select` | 114 | 3 | 33 | 2 |  |
| `goroutine` | 90 | 5 | 9 | 2 |  |
| `limit` | 72 | 0 | 15 | 72 |  |
| `append` | 71 | 21 | 31 | 2 |  |
| `copy` | 62 | 24 | 36 | 2 |  |
| `func-literal` | 62 | 7 | 58 | 3 |  |
| `contract` | 48 | 7 | 20 | 3 |  |
| `recover` | 48 | 11 | 16 | 2 |  |
| `operator` | 26 | 0 | 1 | 0 |  |
| `defer` | 18 | 2 | 4 | 0 |  |
| `exit` | 7 | 1 | 1 | 0 |  |
| `closure` | 6 | 0 | 6 | 0 |  |
| `annotation` | 2 | 1 | 1 | 1 |  |

### Greedy order of classes

Get through with nothing fixed: 7199.

| step | fixed | let through by it | let through in all |
| --- | --- | --- | --- |
| 1 | `recursion:through-call` | 1329 | 8528 |
| 2 | `recursion:through-method` | 435 | 8963 |
| 3 | `func-value:calls-values` | 410 | 9373 |
| 4 | `type:array-in-struct` | 407 | 9780 |
| 5 | `no-entry:std` | 364 | 10144 |
| 6 | `global:read` | 341 | 10485 |
| 7 | `recursion:through-value` | 348 | 10833 |
| 8 | `pointer:to-non-struct` | 204 | 11037 |
| 9 | `func-value:no-contract` | 200 | 11237 |
| 10 | `dyntype:assert` | 167 | 11404 |
| 11 | `error:unknown-origin` | 173 | 11577 |
| 12 | `assign:target` | 167 | 11744 |
| 13 | `type:uintptr` | 151 | 11895 |
| 14 | `convert:to-error` | 182 | 12077 |
| 15 | `generic:called` | 163 | 12240 |
| 16 | `convert:iface-no-contract` | 156 | 12396 |
| 17 | `format:runs-code` | 151 | 12547 |
| 18 | `iface-method:no-contract` | 139 | 12686 |
| 19 | `error:sentinel` | 120 | 12806 |
| 20 | `handover:unknown-code` | 125 | 12931 |

### Greedy order of groups

Get through with nothing fixed: 7199.

| step | fixed | let through by it | let through in all |
| --- | --- | --- | --- |
| 1 | `recursion` | 2132 | 9331 |
| 2 | `type` | 634 | 9965 |
| 3 | `func-value` | 694 | 10659 |
| 4 | `convert` | 515 | 11174 |
| 5 | `global` | 443 | 11617 |
| 6 | `no-entry` | 488 | 12105 |
| 7 | `pointer` | 330 | 12435 |
| 8 | `error` | 315 | 12750 |
| 9 | `dyntype` | 299 | 13049 |
| 10 | `generic` | 313 | 13362 |
| 11 | `assign` | 318 | 13680 |
| 12 | `expr` | 267 | 13947 |
| 13 | `format` | 244 | 14191 |
| 14 | `address-of` | 195 | 14386 |
| 15 | `iface-method` | 195 | 14581 |
| 16 | `call` | 185 | 14766 |
| 17 | `handover` | 157 | 14923 |
| 18 | `json` | 121 | 15044 |
| 19 | `channel` | 87 | 15131 |
| 20 | `stmt` | 106 | 15237 |

### Greedy order of classes, with what the project writes for other modules (no-entry:other and the classes ending in -other) left out of the causes

Get through with nothing fixed: 7209.

| step | fixed | let through by it | let through in all |
| --- | --- | --- | --- |
| 1 | `recursion:through-call` | 1333 | 8542 |
| 2 | `recursion:through-method` | 435 | 8977 |
| 3 | `func-value:calls-values` | 411 | 9388 |
| 4 | `type:array-in-struct` | 407 | 9795 |
| 5 | `no-entry:std` | 367 | 10162 |
| 6 | `global:read` | 343 | 10505 |
| 7 | `recursion:through-value` | 348 | 10853 |
| 8 | `pointer:to-non-struct` | 205 | 11058 |
| 9 | `func-value:no-contract` | 200 | 11258 |
| 10 | `error:unknown-origin` | 178 | 11436 |
| 11 | `dyntype:assert` | 174 | 11610 |
| 12 | `assign:target` | 168 | 11778 |
| 13 | `type:uintptr` | 151 | 11929 |
| 14 | `convert:to-error` | 183 | 12112 |
| 15 | `generic:called` | 165 | 12277 |
| 16 | `convert:iface-no-contract` | 156 | 12433 |
| 17 | `format:runs-code` | 154 | 12587 |
| 18 | `iface-method:no-contract` | 143 | 12730 |
| 19 | `handover:unknown-code` | 123 | 12853 |
| 20 | `error:sentinel` | 125 | 12978 |

### Greedy order of groups, with what the project writes for other modules (no-entry:other and the classes ending in -other) left out of the causes

Get through with nothing fixed: 7209.

| step | fixed | let through by it | let through in all |
| --- | --- | --- | --- |
| 1 | `recursion` | 2136 | 9345 |
| 2 | `type` | 640 | 9985 |
| 3 | `func-value` | 697 | 10682 |
| 4 | `convert` | 516 | 11198 |
| 5 | `global` | 447 | 11645 |
| 6 | `no-entry` | 480 | 12125 |
| 7 | `pointer` | 334 | 12459 |
| 8 | `error` | 317 | 12776 |
| 9 | `dyntype` | 301 | 13077 |
| 10 | `generic` | 318 | 13395 |
| 11 | `assign` | 328 | 13723 |
| 12 | `expr` | 270 | 13993 |
| 13 | `format` | 247 | 14240 |
| 14 | `address-of` | 195 | 14435 |
| 15 | `iface-method` | 193 | 14628 |
| 16 | `call` | 186 | 14814 |
| 17 | `handover` | 159 | 14973 |
| 18 | `json` | 122 | 15095 |
| 19 | `channel` | 88 | 15183 |
| 20 | `scoped` | 89 | 15272 |

### Callees without an entry

| callee | class | functions stopped | stopped alone |
| --- | --- | --- | --- |
| `reflect.ValueOf` | `no-entry:std` | 89 | 0 |
| `(reflect.Value).Type` | `no-entry:std` | 85 | 0 |
| `(reflect.Value).Kind` | `no-entry:std` | 69 | 1 |
| `(reflect.Value).Interface` | `no-entry:std` | 59 | 0 |
| `(reflect.Value).Elem` | `no-entry:std` | 45 | 0 |
| `(reflect.Value).Len` | `no-entry:std` | 44 | 0 |
| `context.Background` | `no-entry:std` | 43 | 0 |
| `(reflect.Value).IsNil` | `no-entry:std` | 42 | 0 |
| `(reflect.Value).Set` | `no-entry:std` | 41 | 1 |
| `(reflect.Value).IsValid` | `no-entry:std` | 36 | 1 |
| `(reflect.Value).Index` | `no-entry:std` | 30 | 0 |
| `flag.Parse` | `no-entry:std` | 30 | 1 |
| `net/url.Parse` | `no-entry:std` | 25 | 6 |
| `reflect.Indirect` | `no-entry:std` | 25 | 0 |
| `reflect.New` | `no-entry:std` | 24 | 0 |
| `reflect.TypeOf` | `no-entry:std` | 24 | 3 |
| `(reflect.Value).String` | `no-entry:std` | 23 | 0 |
| `(*go/types.object).Type` | `no-entry:std` | 20 | 0 |
| `(reflect.Value).Bool` | `no-entry:std` | 20 | 0 |
| `(*sync/atomic.Bool).Load` | `no-entry:std` | 19 | 1 |
| `(*go/types.object).Name` | `no-entry:std` | 16 | 0 |
| `(*encoding/base64.Encoding).EncodeToString` | `no-entry:std` | 14 | 3 |
| `(*log/slog.Logger).Error` | `no-entry:std` | 14 | 0 |
| `(*net/http.Request).Context` | `no-entry:std` | 14 | 0 |
| `(*net/url.URL).String` | `no-entry:std` | 14 | 0 |
| `(reflect.Value).Int` | `no-entry:std` | 14 | 0 |
| `(reflect.Value).MapIndex` | `no-entry:std` | 14 | 0 |
| `context.WithValue` | `no-entry:std` | 14 | 2 |
| `errors.Join` | `no-entry:std` | 14 | 2 |
| `(reflect.Value).Field` | `no-entry:std` | 13 | 0 |
| `os.Stat` | `no-entry:std` | 13 | 0 |
| `strconv.ParseFloat` | `no-entry:std` | 13 | 4 |
| `(*bytes.Reader).Read` | `no-entry:std` | 12 | 0 |
| `(*strings.Replacer).Replace` | `no-entry:std` | 12 | 1 |
| `(reflect.Value).Float` | `no-entry:std` | 12 | 0 |
| `bytes.NewReader` | `no-entry:std` | 12 | 0 |
| `strings.ContainsRune` | `no-entry:std` | 12 | 9 |
| `(*log/slog.Logger).Info` | `no-entry:std` | 11 | 1 |
| `(*net/http.Client).Do` | `no-entry:std` | 11 | 0 |
| `(reflect.Value).FieldByIndex` | `no-entry:std` | 11 | 0 |
| `context.WithTimeout` | `no-entry:std` | 11 | 0 |
| `flag.Args` | `no-entry:std` | 11 | 0 |
| `unicode.ToLower` | `no-entry:std` | 11 | 11 |
| `(*sync.Cond).Broadcast` | `no-entry:std` | 10 | 1 |
| `(reflect.Value).MapKeys` | `no-entry:std` | 10 | 0 |
| `(reflect.Value).Uint` | `no-entry:std` | 10 | 0 |
| `net/http.ListenAndServe` | `no-entry:std` | 10 | 0 |
| `net/http.NewRequestWithContext` | `no-entry:std` | 10 | 0 |
| `os/exec.CommandContext` | `no-entry:std` | 10 | 0 |
| `strconv.FormatFloat` | `no-entry:std` | 10 | 3 |

### Refusals made only when a proof fails

A census proves nothing, so it makes these wherever they are reached; the prover would often prove what they ask.

| class | functions met in | the only thing met | top details |
| --- | --- | --- | --- |
| `error:compare-unproved` | 42 | 0 |  |
| `format:length-unknown` | 3 | 2 |  |
| `global:unreliable` | 2 | 1 |  |
| `handover:apart-unproved` | 1 | 1 |  |

### Panics of the verifier (limit:internal)

- `compress/flate.(*compressor).fillWindow`: interface conversion: types.Type is *types.Pointer, not *types.Struct; at hopsPointer({0x11c3d68, 0x1bd4f6371ab0}, {0x1bd4f65fc680, 0x2, 0x2}) < (*fnVerifier).assignedLocal < (*fnVerifier).eval < (*fnVerifier).expr < (*fnVerifier).binaryExpr < (*fnVerifier).eval < (*fnVerifier).expr < (*fnVerifier).ifStmt.func2()
- `compress/flate.(*compressor).findMatch`: interface conversion: types.Type is *types.Pointer, not *types.Struct; at hopsPointer({0x11c3d68, 0x1bd4f6371ad0}, {0x1bd4f65fc800, 0x2, 0x2}) < (*fnVerifier).assignedLocal < (*fnVerifier).eval < (*fnVerifier).expr < (*fnVerifier).callExpr < (*fnVerifier).eval < (*fnVerifier).evalAs < (*fnVerifier).assign
- `compress/flate.(*compressor).skipLiterals`: interface conversion: types.Type is *types.Pointer, not *types.Struct; at hopsPointer({0x11c3d68, 0x1bd4f6371c10}, {0x1bd4f65fcc80, 0x2, 0x2}) < (*fnVerifier).assignedLocal < (*fnVerifier).eval < (*fnVerifier).expr < (*fnVerifier).binaryExpr < (*fnVerifier).eval < (*fnVerifier).evalAs < (*fnVerifier).assign
- `compress/flate.(*compressor).deflateLazy`: interface conversion: types.Type is *types.Pointer, not *types.Struct; at hopsPointer({0x11c3d68, 0x1bd4f6371c20}, {0x1bd4f65fcf60, 0x2, 0x2}) < (*fnVerifier).assignedLocal < (*fnVerifier).eval < (*fnVerifier).expr < (*fnVerifier).binaryExpr < (*fnVerifier).eval < (*fnVerifier).expr < (*fnVerifier).binaryExpr
- `compress/flate.(*compressor).init`: interface conversion: types.Type is *types.Pointer, not *types.Struct; at (*fnVerifier).checkNotWritten.func1 < (*fnVerifier).checkNotWritten.func4({0x11c40d8?, 0x1bd4f43de640}) < (*fnVerifier).checkNotWritten < (*fnVerifier).verify.func6() < (*fnVerifier).censusCheck < (*fnVerifier).verify < (*pkgVerifier).censusLook < (*pkgVerifier).runCensus
- `compress/flate.(*fastEncL1).encode`: interface conversion: types.Type is *types.Pointer, not *types.Struct; at (*fnVerifier).checkNotWritten.func1 < (*fnVerifier).checkNotWritten.func4({0x11c40d8?, 0x1bd4f445d640}) < (*fnVerifier).checkNotWritten < (*fnVerifier).verify.func6() < (*fnVerifier).censusCheck < (*fnVerifier).verify < (*pkgVerifier).censusLook < (*pkgVerifier).runCensus
- `compress/flate.(*fastEncL2).encode`: interface conversion: types.Type is *types.Pointer, not *types.Struct; at (*fnVerifier).checkNotWritten.func1 < (*fnVerifier).checkNotWritten.func4({0x11c40d8?, 0x1bd4f4584200}) < (*fnVerifier).checkNotWritten < (*fnVerifier).verify.func6() < (*fnVerifier).censusCheck < (*fnVerifier).verify < (*pkgVerifier).censusLook < (*pkgVerifier).runCensus
- `compress/flate.(*fastEncL3).encode`: interface conversion: types.Type is *types.Pointer, not *types.Struct; at (*fnVerifier).checkNotWritten.func1 < (*fnVerifier).checkNotWritten.func4({0x11c40d8?, 0x1bd4f458ce00}) < (*fnVerifier).checkNotWritten < (*fnVerifier).verify.func6() < (*fnVerifier).censusCheck < (*fnVerifier).verify < (*pkgVerifier).censusLook < (*pkgVerifier).runCensus
- `compress/flate.(*fastEncL4).encode`: interface conversion: types.Type is *types.Pointer, not *types.Struct; at (*fnVerifier).checkNotWritten.func1 < (*fnVerifier).checkNotWritten.func4({0x11c40d8?, 0x1bd4f4553500}) < (*fnVerifier).checkNotWritten < (*fnVerifier).verify.func6() < (*fnVerifier).censusCheck < (*fnVerifier).verify < (*pkgVerifier).censusLook < (*pkgVerifier).runCensus
- `compress/flate.(*fastEncL5).encode`: interface conversion: types.Type is *types.Pointer, not *types.Struct; at (*fnVerifier).checkNotWritten.func1 < (*fnVerifier).checkNotWritten.func4({0x11c40d8?, 0x1bd4f4597c40}) < (*fnVerifier).checkNotWritten < (*fnVerifier).verify.func6() < (*fnVerifier).censusCheck < (*fnVerifier).verify < (*pkgVerifier).censusLook < (*pkgVerifier).runCensus
- `compress/flate.(*fastEncL6).encode`: interface conversion: types.Type is *types.Pointer, not *types.Struct; at (*fnVerifier).checkNotWritten.func1 < (*fnVerifier).checkNotWritten.func4({0x11c40d8?, 0x1bd4f4578780}) < (*fnVerifier).checkNotWritten < (*fnVerifier).verify.func6() < (*fnVerifier).censusCheck < (*fnVerifier).verify < (*pkgVerifier).censusLook < (*pkgVerifier).runCensus
- `crypto/tls.(*permanentError).Unwrap`: internal error: e.err at /home/spachava/.local/share/mise/installs/go/1.27.3/src/crypto/tls/conn.go:192:52 is checked as a conversion to error, which the list of conversions does not have there; at (*fnVerifier).evalConverted < (*fnVerifier).evalAs < (*fnVerifier).returnStmt < (*fnVerifier).stmt < (*fnVerifier).seq.func2 < (*fnVerifier).censusStmt < (*fnVerifier).seq < (*fnVerifier).verify
- `os.Getwd`: runtime error: slice bounds out of range [58:57]; at (*fnVerifier).loop < (*fnVerifier).forStmt < (*fnVerifier).seq.func2 < (*fnVerifier).censusStmt < (*fnVerifier).seq < (*fnVerifier).seq.func1 < (*fnVerifier).censusStmt.func2 < (*fnVerifier).logging.func1
- `github.com/modelcontextprotocol/go-sdk/mcp.(*streamableServerConn).Write`: runtime error: slice bounds out of range [:-1]; at (*fnVerifier).rangeStmt.func8() < (*fnVerifier).unsupported < (*fnVerifier).branch < (*fnVerifier).appendTo < (*fnVerifier).assign < (*fnVerifier).stmt < (*fnVerifier).seq.func2 < (*fnVerifier).censusStmt
- `github.com/coder/acp-go-sdk/example/gemini.main`: runtime error: slice bounds out of range [984:983]; at (*fnVerifier).loop < (*fnVerifier).forStmt < (*fnVerifier).seq.func2 < (*fnVerifier).censusStmt < (*fnVerifier).seq < (*fnVerifier).seq.func1 < (*fnVerifier).censusStmt.func2 < (*fnVerifier).logging.func1

## All corpora but laas, each module weighted equally

- functions with a body: 35.0, of which not loaded: 0.0
- get through: 16.3 (46.6%), of which 0.0 only past refusals made when a proof fails
- not looked at in full (a statement no attempt entered, or the census stopped): 1.4, with 10.0 statements not entered
- reach what only a declaration of the trust file allows: 0.4
- assume a callee, method, or function type of the module with the weakest contract: 17.5

### Refusals by class

| class | functions stopped | stopped alone | first cause | not looked at in full | top details (stopped, alone) |
| --- | --- | --- | --- | --- | --- |
| `no-entry:std` | 7.7 | 2.7 | 5.8 | 0.1 | `reflect.ValueOf` (1.0, 0.0); `(reflect.Value).Type` (0.9, 0.0); `(reflect.Value).Kind` (0.8, 0.0) |
| `recursion:through-call` | 4.9 | 1.7 | 2.5 | 0.1 | `reflect.ValueOf` (0.6, 0.0); `(*bufio.Reader).ReadRune` (0.5, 0.4); `(reflect.Value).Kind` (0.4, 0.0) |
| `iface-method:no-contract` | 1.7 | 0.2 | 0.4 | 0.1 | `(reflect.Type).Kind` (0.6, 0.1); `(reflect.Type).Elem` (0.5, 0.0); `(reflect.Type).Key` (0.2, 0.0) |
| `recursion:through-value` | 1.6 | 0.7 | 1.1 | 0.0 | `cb` (0.5, 0.4); `ErrorHandler` (0.3, 0.2); `fn` (0.1, 0.0) |
| `global:read` | 1.4 | 0.2 | 0.5 | 0.0 |  |
| `format:runs-code` | 1.4 | 0.3 | 0.4 | 0.1 |  |
| `generic:declared` | 1.2 | 0.0 | 1.2 | 1.2 |  |
| `error:unknown-origin` | 1.2 | 0.2 | 0.2 | 0.0 | `formatted` (0.9, 0.1); `Error called` (0.2, 0.0); `errors.Is` (0.1, 0.0) |
| `func-value:calls-values` | 0.9 | 0.3 | 0.5 | 0.0 |  |
| `func-value:no-contract` | 0.8 | 0.1 | 0.3 | 0.0 | `func() time.Time` (0.1, 0.0); `func(github.com/felixge/httpsnoop.WriteHeaderFunc) github.com/felixge/httpsnoop.WriteHeaderFunc` (0.1, 0.0); `func()` (0.1, 0.0) |
| `recursion:through-method` | 0.7 | 0.2 | 0.3 | 0.0 | `(github.com/go-sql-driver/mysql.Logger).Print` (0.1, 0.0); `(io.Closer).Close` (0.1, 0.0); `(net.Conn).Write` (0.1, 0.0) |
| `assign:target` | 0.6 | 0.1 | 0.2 | 0.0 |  |
| `convert:value` | 0.6 | 0.3 | 0.4 | 0.0 | `[]rune to string` (0.3, 0.1); `string to []rune` (0.2, 0.1); `unsafe.Pointer to *string` (0.0, 0.0) |
| `pointer:to-non-struct` | 0.5 | 0.2 | 0.4 | 0.0 | `*error` (0.1, 0.0); `*[]byte` (0.1, 0.0); `*any` (0.1, 0.0) |
| `channel:use` | 0.5 | 0.1 | 0.2 | 0.0 | `chan struct{}` (0.2, 0.0); `<-chan struct{}` (0.2, 0.0); `<-chan time.Time` (0.1, 0.0) |
| `handover:unknown-code` | 0.4 | 0.1 | 0.1 | 0.0 |  |
| `address-of:field` | 0.4 | 0.0 | 0.0 | 0.0 | `b.attempt` (0.4, 0.0); `x.Cursor` (0.0, 0.0); `x.NextCursor` (0.0, 0.0) |
| `expr:index` | 0.4 | 0.1 | 0.1 | 0.0 | `map[*github.com/google/jsonschema-go/jsonschema.Schema]*github.com/google/jsonschema-go/jsonschema.resolvedInfo` (0.1, 0.0); `[6]byte` (0.1, 0.0); `map[*go/ast.Ident]go/types.Object` (0.0, 0.0) |
| `scoped:kept` | 0.4 | 0.0 | 0.4 | 0.0 |  |
| `type:array-in-struct` | 0.4 | 0.2 | 0.3 | 0.0 | `*github.com/BurntSushi/toml.lexer` (0.2, 0.1); `*github.com/emirpasic/gods/trees/avltree.Node` (0.0, 0.0); `github.com/BurntSushi/toml.lexer` (0.0, 0.0) |
| `convert:to-error` | 0.3 | 0.1 | 0.1 | 0.0 |  |
| `dyntype:assert` | 0.3 | 0.0 | 0.1 | 0.0 |  |
| `generic:called` | 0.3 | 0.2 | 0.2 | 0.0 | `github.com/aymanbagabas/go-udiff/lcs.commonPrefixLen` (0.0, 0.0); `github.com/aymanbagabas/go-udiff/lcs.commonSuffixLen` (0.0, 0.0); `github.com/google/jsonschema-go/jsonschema.Ptr` (0.0, 0.0) |
| `type:map-key` | 0.3 | 0.0 | 0.2 | 0.0 | `map[*github.com/google/jsonschema-go/jsonschema.Schema]*github.com/google/jsonschema-go/jsonschema.resolvedInfo` (0.1, 0.0); `map[reflect.Type]bool` (0.0, 0.0); `map[interface{}]interface{}` (0.0, 0.0) |
| `json:decode` | 0.3 | 0.1 | 0.1 | 0.0 |  |
| `convert:iface-no-contract` | 0.2 | 0.1 | 0.1 | 0.0 | `(go/ast.Visitor).Visit` (0.1, 0.0); `(github.com/modelcontextprotocol/go-sdk/mcp.Params).GetMeta` (0.1, 0.0); `(encoding/json/v2.Marshaler).MarshalJSON` (0.0, 0.0) |
| `format:slice-pack` | 0.2 | 0.2 | 0.2 | 0.0 |  |
| `no-entry:other` | 0.2 | 0.0 | 0.1 | 0.0 | `(*golang.org/x/oauth2.Config).Exchange` (0.1, 0.0); `github.com/go-jose/go-jose/v4.ParseSigned` (0.1, 0.0); `(*golang.org/x/oauth2.Token).Extra` (0.0, 0.0) |
| `recursion:through-format` | 0.2 | 0.1 | 0.1 | 0.0 | `fmt.Sprintf` (0.2, 0.0); `fmt.Errorf` (0.0, 0.0); `fmt.Fprintf` (0.0, 0.0) |
| `json:encode` | 0.2 | 0.1 | 0.1 | 0.0 |  |
| `error:sentinel` | 0.2 | 0.1 | 0.1 | 0.0 |  |
| `call:multi-value-args` | 0.2 | 0.2 | 0.2 | 0.0 |  |
| `func-literal:value` | 0.2 | 0.0 | 0.2 | 0.0 |  |
| `convert:multi-value` | 0.2 | 0.0 | 0.0 | 0.0 |  |
| `select:statement` | 0.2 | 0.0 | 0.0 | 0.0 |  |
| `copy:elements` | 0.2 | 0.1 | 0.1 | 0.0 |  |
| `convert:unplaced` | 0.2 | 0.0 | 0.0 | 0.0 |  |
| `goroutine:go` | 0.2 | 0.0 | 0.0 | 0.0 |  |
| `call:initialiser-only` | 0.2 | 0.1 | 0.1 | 0.0 |  |
| `dyntype:switch` | 0.2 | 0.0 | 0.0 | 0.0 |  |
| `global:assign` | 0.1 | 0.0 | 0.1 | 0.0 |  |
| `stmt:range-other` | 0.1 | 0.0 | 0.0 | 0.0 | `map[float64]string` (0.1, 0.0); `map[interface{}]struct{}` (0.0, 0.0); `map[reflect.Value]struct{}` (0.0, 0.0) |
| `call:builtin` | 0.1 | 0.0 | 0.0 | 0.0 | `close` (0.1, 0.0); `copy` (0.0, 0.0); `imag` (0.0, 0.0) |
| `assign:multi-value` | 0.1 | 0.0 | 0.1 | 0.0 | `+=` (0.0, 0.0); `|=` (0.0, 0.0); `^=` (0.0, 0.0) |
| `append:in-expression` | 0.1 | 0.0 | 0.0 | 0.0 |  |
| `json:form` | 0.1 | 0.0 | 0.0 | 0.0 |  |
| `generic:iterator` | 0.1 | 0.0 | 0.0 | 0.0 |  |
| `copy:value-with-state` | 0.1 | 0.1 | 0.1 | 0.0 |  |
| `generic:type-args` | 0.1 | 0.0 | 0.0 | 0.0 |  |
| `pointer:to-array` | 0.1 | 0.0 | 0.1 | 0.0 | `*github.com/google/uuid.UUID` (0.1, 0.0); `*archive/tar.block` (0.0, 0.0); `*archive/tar.headerV7` (0.0, 0.0) |
| `expr:value-shape` | 0.1 | 0.0 | 0.0 | 0.0 |  |
| `convert:iface-array` | 0.1 | 0.0 | 0.0 | 0.0 |  |
| `limit:paths` | 0.1 | 0.0 | 0.0 | 0.1 |  |
| `global:type` | 0.1 | 0.0 | 0.0 | 0.0 |  |
| `type:uintptr` | 0.1 | 0.0 | 0.0 | 0.0 | `uintptr` (0.1, 0.0); `syscall.Errno` (0.0, 0.0); `reflect.flag` (0.0, 0.0) |
| `type:unsafe-pointer` | 0.1 | 0.0 | 0.0 | 0.0 | `unsafe.Pointer` (0.1, 0.0) |
| `func-value:made-from` | 0.1 | 0.0 | 0.0 | 0.0 |  |
| `type:array` | 0.1 | 0.0 | 0.0 | 0.0 | `[6][2]float64` (0.0, 0.0); `[2]github.com/google/go-cmp/cmp/internal/value.Pointer` (0.0, 0.0); `[12]sync.Pool` (0.0, 0.0) |
| `func-literal:signature` | 0.1 | 0.0 | 0.1 | 0.0 |  |
| `func-literal:captures` | 0.1 | 0.0 | 0.0 | 0.0 |  |
| `convert:iface-foreign-impl` | 0.1 | 0.0 | 0.0 | 0.0 |  |
| `address-of:global` | 0.0 | 0.0 | 0.0 | 0.0 | `upgrader` (0.0, 0.0); `fieldCache` (0.0, 0.0); `lookupCache` (0.0, 0.0) |
| `recover:call` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `stmt:goto` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `stmt:expression` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `iface-method:no-contract-other` | 0.0 | 0.0 | 0.0 | 0.0 | `(golang.org/x/oauth2.TokenSource).Token` (0.0, 0.0); `(github.com/go-jose/go-jose/v4.Signer).Sign` (0.0, 0.0) |
| `contract:unusable` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `generic:method-call` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `convert:iface-states` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `closure:recursive` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `defer:form` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `type:complex` | 0.0 | 0.0 | 0.0 | 0.0 | `complex128` (0.0, 0.0); `complex64` (0.0, 0.0) |
| `no-entry:impossible` | 0.0 | 0.0 | 0.0 | 0.0 | `io.Copy` (0.0, 0.0); `io.CopyN` (0.0, 0.0); `(*bytes.Buffer).ReadFrom` (0.0, 0.0) |
| `type:array-elem` | 0.0 | 0.0 | 0.0 | 0.0 | `github.com/google/uuid.UUID` (0.0, 0.0); `github.com/lucasb-eyer/go-colorful.edgeIdxs` (0.0, 0.0); `[2]github.com/google/go-cmp/cmp/internal/value.Pointer` (0.0, 0.0) |
| `expr:other` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `stmt:range-form` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `convert:iface-optional` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `type:iface-literal` | 0.0 | 0.0 | 0.0 | 0.0 | `net.Error` (0.0, 0.0); `github.com/modelcontextprotocol/go-sdk/mcp.binder[*github.com/modelcontextprotocol/go-sdk/mcp.ClientSession, *github.com/modelcontextprotocol/go-sdk/mcp.clientSessionState]` (0.0, 0.0); `github.com/modelcontextprotocol/go-sdk/mcp.binder[*github.com/modelcontextprotocol/go-sdk/mcp.ServerSession, *github.com/modelcontextprotocol/go-sdk/mcp.ServerSessionState]` (0.0, 0.0) |
| `address-of:element` | 0.0 | 0.0 | 0.0 | 0.0 | `b[0]` (0.0, 0.0); `oldText[0]` (0.0, 0.0); `buf[0]` (0.0, 0.0) |
| `exit:context` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `scoped:written` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `convert:iface-wraps-writer` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `func-value:method-value` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `package:not-loaded` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `operator:nil-compare` | 0.0 | 0.0 | 0.0 | 0.0 | `*github.com/emirpasic/gods/trees/avltree.Node` (0.0, 0.0); `<-chan struct{}` (0.0, 0.0); `chan struct{}` (0.0, 0.0) |
| `limit:internal` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `defer:in-loop` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `iface-method:form` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `handover:apart` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `handover:sort` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `recursion:through-trusted` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `assign:in-place` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `limit:attempts` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `convert:iface-by-contract` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `func-value:trusted-callee` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `handover:footprint` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `generic:as-value` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `annotation:unreadable` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `scoped:hidden` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `dyntype:errors-as` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `global:followed-code` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `limit:facts` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `func-value:method-expr` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `call:form` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `operator:pointer` | 0.0 | 0.0 | 0.0 | 0.0 |  |

### Refusals by group

| group | functions stopped | stopped alone | first cause | not looked at in full | top details (stopped, alone) |
| --- | --- | --- | --- | --- | --- |
| `no-entry` | 7.8 | 2.8 | 6.0 | 0.1 |  |
| `recursion` | 6.8 | 2.9 | 4.1 | 0.1 |  |
| `generic` | 1.8 | 0.2 | 1.5 | 1.2 |  |
| `func-value` | 1.7 | 0.5 | 0.8 | 0.1 |  |
| `iface-method` | 1.7 | 0.2 | 0.4 | 0.1 |  |
| `format` | 1.6 | 0.5 | 0.6 | 0.1 |  |
| `global` | 1.5 | 0.3 | 0.6 | 0.0 |  |
| `convert` | 1.5 | 0.5 | 0.7 | 0.0 |  |
| `error` | 1.4 | 0.2 | 0.3 | 0.0 |  |
| `type` | 0.9 | 0.3 | 0.7 | 0.0 |  |
| `assign` | 0.7 | 0.1 | 0.3 | 0.0 |  |
| `pointer` | 0.6 | 0.2 | 0.5 | 0.0 |  |
| `json` | 0.6 | 0.2 | 0.3 | 0.0 |  |
| `call` | 0.5 | 0.3 | 0.3 | 0.0 |  |
| `channel` | 0.5 | 0.1 | 0.2 | 0.0 |  |
| `expr` | 0.5 | 0.1 | 0.2 | 0.0 |  |
| `address-of` | 0.5 | 0.0 | 0.0 | 0.0 |  |
| `dyntype` | 0.5 | 0.0 | 0.1 | 0.0 |  |
| `handover` | 0.4 | 0.1 | 0.1 | 0.0 |  |
| `scoped` | 0.4 | 0.0 | 0.4 | 0.0 |  |
| `func-literal` | 0.3 | 0.0 | 0.3 | 0.0 |  |
| `copy` | 0.3 | 0.2 | 0.2 | 0.0 |  |
| `stmt` | 0.2 | 0.0 | 0.1 | 0.0 |  |
| `select` | 0.2 | 0.0 | 0.0 | 0.0 |  |
| `goroutine` | 0.2 | 0.0 | 0.0 | 0.0 |  |
| `append` | 0.1 | 0.0 | 0.0 | 0.0 |  |
| `limit` | 0.1 | 0.0 | 0.0 | 0.1 |  |
| `recover` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `defer` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `contract` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `closure` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `exit` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `package` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `operator` | 0.0 | 0.0 | 0.0 | 0.0 |  |
| `annotation` | 0.0 | 0.0 | 0.0 | 0.0 |  |

### Greedy order of classes

Get through with nothing fixed: 16.3.

| step | fixed | let through by it | let through in all |
| --- | --- | --- | --- |
| 1 | `no-entry:std` | 2.7 | 19.1 |
| 2 | `recursion:through-call` | 2.2 | 21.3 |
| 3 | `recursion:through-value` | 0.9 | 22.2 |
| 4 | `global:read` | 0.7 | 22.8 |
| 5 | `iface-method:no-contract` | 0.7 | 23.5 |
| 6 | `format:runs-code` | 0.7 | 24.2 |
| 7 | `error:unknown-origin` | 0.5 | 24.8 |
| 8 | `func-value:calls-values` | 0.5 | 25.2 |
| 9 | `convert:value` | 0.4 | 25.7 |
| 10 | `address-of:field` | 0.4 | 26.1 |
| 11 | `recursion:through-method` | 0.4 | 26.5 |
| 12 | `func-value:no-contract` | 0.3 | 26.8 |
| 13 | `type:array-in-struct` | 0.3 | 27.1 |
| 14 | `scoped:kept` | 0.3 | 27.3 |
| 15 | `pointer:to-non-struct` | 0.2 | 27.6 |
| 16 | `assign:target` | 0.2 | 27.8 |
| 17 | `generic:called` | 0.2 | 28.0 |
| 18 | `format:slice-pack` | 0.2 | 28.2 |
| 19 | `call:multi-value-args` | 0.2 | 28.5 |
| 20 | `convert:iface-no-contract` | 0.2 | 28.7 |

### Greedy order of groups

Get through with nothing fixed: 16.3.

| step | fixed | let through by it | let through in all |
| --- | --- | --- | --- |
| 1 | `recursion` | 2.9 | 19.3 |
| 2 | `no-entry` | 3.4 | 22.7 |
| 3 | `convert` | 0.9 | 23.5 |
| 4 | `func-value` | 0.9 | 24.4 |
| 5 | `global` | 0.8 | 25.2 |
| 6 | `format` | 0.8 | 26.1 |
| 7 | `iface-method` | 0.9 | 27.0 |
| 8 | `error` | 0.8 | 27.8 |
| 9 | `type` | 0.5 | 28.3 |
| 10 | `address-of` | 0.4 | 28.7 |
| 11 | `call` | 0.4 | 29.1 |
| 12 | `json` | 0.4 | 29.5 |
| 13 | `pointer` | 0.4 | 29.9 |
| 14 | `assign` | 0.4 | 30.3 |
| 15 | `generic` | 0.4 | 30.7 |
| 16 | `expr` | 0.4 | 31.1 |
| 17 | `scoped` | 0.3 | 31.4 |
| 18 | `func-literal` | 0.3 | 31.7 |
| 19 | `handover` | 0.3 | 32.0 |
| 20 | `dyntype` | 0.4 | 32.4 |

### Greedy order of classes, with what the project writes for other modules (no-entry:other and the classes ending in -other) left out of the causes

Get through with nothing fixed: 16.4.

| step | fixed | let through by it | let through in all |
| --- | --- | --- | --- |
| 1 | `no-entry:std` | 2.7 | 19.1 |
| 2 | `recursion:through-call` | 2.2 | 21.4 |
| 3 | `recursion:through-value` | 0.9 | 22.2 |
| 4 | `global:read` | 0.7 | 22.9 |
| 5 | `iface-method:no-contract` | 0.7 | 23.6 |
| 6 | `format:runs-code` | 0.7 | 24.3 |
| 7 | `error:unknown-origin` | 0.6 | 24.9 |
| 8 | `func-value:calls-values` | 0.5 | 25.4 |
| 9 | `convert:value` | 0.4 | 25.9 |
| 10 | `address-of:field` | 0.4 | 26.3 |
| 11 | `recursion:through-method` | 0.4 | 26.7 |
| 12 | `func-value:no-contract` | 0.3 | 27.0 |
| 13 | `type:array-in-struct` | 0.3 | 27.2 |
| 14 | `scoped:kept` | 0.3 | 27.5 |
| 15 | `pointer:to-non-struct` | 0.2 | 27.7 |
| 16 | `assign:target` | 0.2 | 28.0 |
| 17 | `generic:called` | 0.2 | 28.2 |
| 18 | `format:slice-pack` | 0.2 | 28.4 |
| 19 | `handover:unknown-code` | 0.2 | 28.6 |
| 20 | `call:multi-value-args` | 0.2 | 28.8 |

### Greedy order of groups, with what the project writes for other modules (no-entry:other and the classes ending in -other) left out of the causes

Get through with nothing fixed: 16.4.

| step | fixed | let through by it | let through in all |
| --- | --- | --- | --- |
| 1 | `recursion` | 2.9 | 19.3 |
| 2 | `no-entry` | 3.4 | 22.7 |
| 3 | `convert` | 0.9 | 23.6 |
| 4 | `func-value` | 0.9 | 24.4 |
| 5 | `global` | 0.8 | 25.3 |
| 6 | `format` | 0.8 | 26.1 |
| 7 | `iface-method` | 0.9 | 27.0 |
| 8 | `error` | 0.8 | 27.9 |
| 9 | `type` | 0.5 | 28.4 |
| 10 | `call` | 0.4 | 28.8 |
| 11 | `address-of` | 0.4 | 29.2 |
| 12 | `assign` | 0.4 | 29.6 |
| 13 | `json` | 0.4 | 30.0 |
| 14 | `pointer` | 0.4 | 30.4 |
| 15 | `generic` | 0.4 | 30.8 |
| 16 | `expr` | 0.4 | 31.2 |
| 17 | `scoped` | 0.3 | 31.5 |
| 18 | `func-literal` | 0.3 | 31.8 |
| 19 | `handover` | 0.3 | 32.1 |
| 20 | `dyntype` | 0.4 | 32.5 |

### Callees without an entry

| callee | class | functions stopped | stopped alone |
| --- | --- | --- | --- |
| `reflect.ValueOf` | `no-entry:std` | 1.0 | 0.0 |
| `(reflect.Value).Type` | `no-entry:std` | 0.9 | 0.0 |
| `(reflect.Value).Kind` | `no-entry:std` | 0.8 | 0.0 |
| `(reflect.Value).Interface` | `no-entry:std` | 0.6 | 0.0 |
| `reflect.Indirect` | `no-entry:std` | 0.5 | 0.0 |
| `(reflect.Value).Set` | `no-entry:std` | 0.5 | 0.0 |
| `(reflect.Value).Elem` | `no-entry:std` | 0.4 | 0.0 |
| `(reflect.Value).Len` | `no-entry:std` | 0.4 | 0.0 |
| `(reflect.Value).IsValid` | `no-entry:std` | 0.3 | 0.0 |
| `(reflect.Value).IsNil` | `no-entry:std` | 0.3 | 0.0 |
| `(reflect.Value).Index` | `no-entry:std` | 0.3 | 0.0 |
| `(reflect.Value).String` | `no-entry:std` | 0.3 | 0.0 |
| `reflect.New` | `no-entry:std` | 0.2 | 0.0 |
| `(*strings.Reader).Read` | `no-entry:std` | 0.2 | 0.0 |
| `strings.NewReader` | `no-entry:std` | 0.2 | 0.0 |
| `reflect.TypeOf` | `no-entry:std` | 0.2 | 0.0 |
| `(reflect.Value).Bool` | `no-entry:std` | 0.2 | 0.0 |
| `math/rand.Float64` | `no-entry:std` | 0.2 | 0.2 |
| `sync/atomic.AddUint64` | `no-entry:std` | 0.2 | 0.0 |
| `sync/atomic.LoadUint64` | `no-entry:std` | 0.2 | 0.0 |
| `sync/atomic.StoreUint64` | `no-entry:std` | 0.2 | 0.2 |
| `errors.Join` | `no-entry:std` | 0.2 | 0.0 |
| `(*bufio.Reader).ReadRune` | `no-entry:std` | 0.2 | 0.0 |
| `(reflect.Value).MapIndex` | `no-entry:std` | 0.2 | 0.0 |
| `context.Background` | `no-entry:std` | 0.2 | 0.0 |
| `(reflect.Value).FieldByIndex` | `no-entry:std` | 0.2 | 0.0 |
| `flag.Parse` | `no-entry:std` | 0.2 | 0.0 |
| `(reflect.Value).SetMapIndex` | `no-entry:std` | 0.1 | 0.0 |
| `(reflect.Value).CanAddr` | `no-entry:std` | 0.1 | 0.0 |
| `(*strings.Replacer).Replace` | `no-entry:std` | 0.1 | 0.0 |
| `strconv.FormatFloat` | `no-entry:std` | 0.1 | 0.1 |
| `(reflect.Value).FieldByName` | `no-entry:std` | 0.1 | 0.0 |
| `(reflect.Value).Float` | `no-entry:std` | 0.1 | 0.0 |
| `strconv.ParseFloat` | `no-entry:std` | 0.1 | 0.1 |
| `(reflect.Value).CanSet` | `no-entry:std` | 0.1 | 0.0 |
| `(reflect.Value).Int` | `no-entry:std` | 0.1 | 0.0 |
| `io.ReadFull` | `no-entry:std` | 0.1 | 0.0 |
| `net/url.Parse` | `no-entry:std` | 0.1 | 0.0 |
| `(*math/big.Int).Cmp` | `no-entry:std` | 0.1 | 0.0 |
| `reflect.MakeMap` | `no-entry:std` | 0.1 | 0.0 |
| `(reflect.Value).MapKeys` | `no-entry:std` | 0.1 | 0.0 |
| `strings.ContainsRune` | `no-entry:std` | 0.1 | 0.1 |
| `(*encoding/base64.Encoding).EncodeToString` | `no-entry:std` | 0.1 | 0.0 |
| `(*encoding/json.Decoder).Token` | `no-entry:std` | 0.1 | 0.0 |
| `(*net/url.URL).String` | `no-entry:std` | 0.1 | 0.0 |
| `reflect.Zero` | `no-entry:std` | 0.1 | 0.0 |
| `(*bufio.Reader).UnreadRune` | `no-entry:std` | 0.1 | 0.0 |
| `unicode.IsNumber` | `no-entry:std` | 0.1 | 0.1 |
| `(reflect.StructTag).Get` | `no-entry:std` | 0.1 | 0.0 |
| `(reflect.Value).Field` | `no-entry:std` | 0.1 | 0.0 |

### Refusals made only when a proof fails

A census proves nothing, so it makes these wherever they are reached; the prover would often prove what they ask.

| class | functions met in | the only thing met | top details |
| --- | --- | --- | --- |
| `error:compare-unproved` | 0.0 | 0.0 |  |
| `format:length-unknown` | 0.0 | 0.0 |  |
| `global:unreliable` | 0.0 | 0.0 |  |
| `handover:apart-unproved` | 0.0 | 0.0 |  |

### Panics of the verifier (limit:internal)

- `compress/flate.(*compressor).fillWindow`: interface conversion: types.Type is *types.Pointer, not *types.Struct; at hopsPointer({0x11c3d68, 0x1bd4f6371ab0}, {0x1bd4f65fc680, 0x2, 0x2}) < (*fnVerifier).assignedLocal < (*fnVerifier).eval < (*fnVerifier).expr < (*fnVerifier).binaryExpr < (*fnVerifier).eval < (*fnVerifier).expr < (*fnVerifier).ifStmt.func2()
- `compress/flate.(*compressor).findMatch`: interface conversion: types.Type is *types.Pointer, not *types.Struct; at hopsPointer({0x11c3d68, 0x1bd4f6371ad0}, {0x1bd4f65fc800, 0x2, 0x2}) < (*fnVerifier).assignedLocal < (*fnVerifier).eval < (*fnVerifier).expr < (*fnVerifier).callExpr < (*fnVerifier).eval < (*fnVerifier).evalAs < (*fnVerifier).assign
- `compress/flate.(*compressor).skipLiterals`: interface conversion: types.Type is *types.Pointer, not *types.Struct; at hopsPointer({0x11c3d68, 0x1bd4f6371c10}, {0x1bd4f65fcc80, 0x2, 0x2}) < (*fnVerifier).assignedLocal < (*fnVerifier).eval < (*fnVerifier).expr < (*fnVerifier).binaryExpr < (*fnVerifier).eval < (*fnVerifier).evalAs < (*fnVerifier).assign
- `compress/flate.(*compressor).deflateLazy`: interface conversion: types.Type is *types.Pointer, not *types.Struct; at hopsPointer({0x11c3d68, 0x1bd4f6371c20}, {0x1bd4f65fcf60, 0x2, 0x2}) < (*fnVerifier).assignedLocal < (*fnVerifier).eval < (*fnVerifier).expr < (*fnVerifier).binaryExpr < (*fnVerifier).eval < (*fnVerifier).expr < (*fnVerifier).binaryExpr
- `compress/flate.(*compressor).init`: interface conversion: types.Type is *types.Pointer, not *types.Struct; at (*fnVerifier).checkNotWritten.func1 < (*fnVerifier).checkNotWritten.func4({0x11c40d8?, 0x1bd4f43de640}) < (*fnVerifier).checkNotWritten < (*fnVerifier).verify.func6() < (*fnVerifier).censusCheck < (*fnVerifier).verify < (*pkgVerifier).censusLook < (*pkgVerifier).runCensus
- `compress/flate.(*fastEncL1).encode`: interface conversion: types.Type is *types.Pointer, not *types.Struct; at (*fnVerifier).checkNotWritten.func1 < (*fnVerifier).checkNotWritten.func4({0x11c40d8?, 0x1bd4f445d640}) < (*fnVerifier).checkNotWritten < (*fnVerifier).verify.func6() < (*fnVerifier).censusCheck < (*fnVerifier).verify < (*pkgVerifier).censusLook < (*pkgVerifier).runCensus
- `compress/flate.(*fastEncL2).encode`: interface conversion: types.Type is *types.Pointer, not *types.Struct; at (*fnVerifier).checkNotWritten.func1 < (*fnVerifier).checkNotWritten.func4({0x11c40d8?, 0x1bd4f4584200}) < (*fnVerifier).checkNotWritten < (*fnVerifier).verify.func6() < (*fnVerifier).censusCheck < (*fnVerifier).verify < (*pkgVerifier).censusLook < (*pkgVerifier).runCensus
- `compress/flate.(*fastEncL3).encode`: interface conversion: types.Type is *types.Pointer, not *types.Struct; at (*fnVerifier).checkNotWritten.func1 < (*fnVerifier).checkNotWritten.func4({0x11c40d8?, 0x1bd4f458ce00}) < (*fnVerifier).checkNotWritten < (*fnVerifier).verify.func6() < (*fnVerifier).censusCheck < (*fnVerifier).verify < (*pkgVerifier).censusLook < (*pkgVerifier).runCensus
- `compress/flate.(*fastEncL4).encode`: interface conversion: types.Type is *types.Pointer, not *types.Struct; at (*fnVerifier).checkNotWritten.func1 < (*fnVerifier).checkNotWritten.func4({0x11c40d8?, 0x1bd4f4553500}) < (*fnVerifier).checkNotWritten < (*fnVerifier).verify.func6() < (*fnVerifier).censusCheck < (*fnVerifier).verify < (*pkgVerifier).censusLook < (*pkgVerifier).runCensus
- `compress/flate.(*fastEncL5).encode`: interface conversion: types.Type is *types.Pointer, not *types.Struct; at (*fnVerifier).checkNotWritten.func1 < (*fnVerifier).checkNotWritten.func4({0x11c40d8?, 0x1bd4f4597c40}) < (*fnVerifier).checkNotWritten < (*fnVerifier).verify.func6() < (*fnVerifier).censusCheck < (*fnVerifier).verify < (*pkgVerifier).censusLook < (*pkgVerifier).runCensus
- `compress/flate.(*fastEncL6).encode`: interface conversion: types.Type is *types.Pointer, not *types.Struct; at (*fnVerifier).checkNotWritten.func1 < (*fnVerifier).checkNotWritten.func4({0x11c40d8?, 0x1bd4f4578780}) < (*fnVerifier).checkNotWritten < (*fnVerifier).verify.func6() < (*fnVerifier).censusCheck < (*fnVerifier).verify < (*pkgVerifier).censusLook < (*pkgVerifier).runCensus
- `crypto/tls.(*permanentError).Unwrap`: internal error: e.err at /home/spachava/.local/share/mise/installs/go/1.27.3/src/crypto/tls/conn.go:192:52 is checked as a conversion to error, which the list of conversions does not have there; at (*fnVerifier).evalConverted < (*fnVerifier).evalAs < (*fnVerifier).returnStmt < (*fnVerifier).stmt < (*fnVerifier).seq.func2 < (*fnVerifier).censusStmt < (*fnVerifier).seq < (*fnVerifier).verify
- `os.Getwd`: runtime error: slice bounds out of range [58:57]; at (*fnVerifier).loop < (*fnVerifier).forStmt < (*fnVerifier).seq.func2 < (*fnVerifier).censusStmt < (*fnVerifier).seq < (*fnVerifier).seq.func1 < (*fnVerifier).censusStmt.func2 < (*fnVerifier).logging.func1
- `github.com/modelcontextprotocol/go-sdk/mcp.(*streamableServerConn).Write`: runtime error: slice bounds out of range [:-1]; at (*fnVerifier).rangeStmt.func8() < (*fnVerifier).unsupported < (*fnVerifier).branch < (*fnVerifier).appendTo < (*fnVerifier).assign < (*fnVerifier).stmt < (*fnVerifier).seq.func2 < (*fnVerifier).censusStmt
- `github.com/coder/acp-go-sdk/example/gemini.main`: runtime error: slice bounds out of range [984:983]; at (*fnVerifier).loop < (*fnVerifier).forStmt < (*fnVerifier).seq.func2 < (*fnVerifier).censusStmt < (*fnVerifier).seq < (*fnVerifier).seq.func1 < (*fnVerifier).censusStmt.func2 < (*fnVerifier).logging.func1

