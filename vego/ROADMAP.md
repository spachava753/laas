# vego roadmap

Design notes for work that is planned but not built. The README describes what exists today.

## Target

vego is meant for use on real projects, not only textbook algorithms. The first target is the code found in services, command-line tools, infrastructure, parsers, and data structures: logic over integers, strings used as tokens, slices, structs, and errors, calling into the standard library and third-party modules.

Not a target: numerical, scientific, graphics, and machine-learning code, where floating point is the core logic, and code whose point is formatting or parsing text exactly.

Design choices should be judged against the first group. A feature that only helps the second can wait.

## Next

### Structs and pointers

Built: the memory model, structs as values, pointers to structs, methods, `Modifies` clauses checked in both directions, nil checks, slices that share arrays (assignment, slicing, `append` in place or moving), `fresh` and `within`, trusted contracts for methods and for functions returning pointers and slices, and contracts with `Modifies` across packages.

Decisions:

- **Sharing is reasoned about, not forbidden.** The verifier models memory as a whole. Where two pointers may refer to the same struct it considers both cases, so a contract must hold when they are equal or require that they differ.
- **Memory is split by type and field.** There is one region for each field of each struct type, holding that field for every object of the type, and one for each element type of a slice. Regions cannot overlap, which is sound because no pointer into the middle of an object can be made: the only address that can be taken is that of a new struct.
- **`Modifies` is declared, and checked in both directions.** A function lists what it may write, as paths from its parameters read on entry. A write to anything else that existed on entry is an error, and so is a listed entry that no write needs, so the declaration cannot drift from the body. Callers know that everything unlisted is unchanged. Whether an entry is needed is decided by a quick proof attempt for each write; when that attempt is inconclusive the entry counts as needed.
- **A slice entry covers the capacity.** `Modifies A` allows writing every element up to the capacity of `A`, because an `append` to `A` may write there. Callers lose what they knew about that stretch, and cut the capacity with `A[:n:n]` to keep the rest. A finer entry that stops at the length, for functions that never append, is possible later.
- **Slice parameters of one element type do not overlap**, capacities included: assumed on entry, proved at every call. There is no way yet for a function to say that it tolerates overlap.
- **Nil.** Every dereference carries a proof obligation that the pointer is not nil. The verifier generates and discharges it; the user writes `Requires p != nil` for parameters and nothing at the dereference.
- **`append` forks.** Whether an append writes in place or moves the slice is decided by the capacity, which is often unknown, so execution continues once for each outcome. That is why an append has to be a whole right-hand side or a returned value.
- **Loops forget memory by region.** A region the loop writes gets a new unknown value. If every write to it goes through a variable the loop does not assign, or through a slice the loop only appends to, everything else that existed before the loop is known to be unchanged. Otherwise only what existed on entry and is not listed in `Modifies` is known to be unchanged.
- **Where a pointer or slice comes from is stated with `fresh` and `within`.** A function that returns something new says `fresh(result)`; one that appends to a slice it holds says `fresh(s.items) Or within(s.items', s.items)`. Without such a clause the caller knows nothing about what the value may share.

Not built yet:

- **Checking a trusted `modifies` against source.** For a trusted function whose source is available, analyse the body and report a write the entry does not declare. This catches some wrong entries; it cannot certify one, because the analysis stops at assembly, `unsafe`, and calls through interfaces or function values. The trust report should say for each entry whether the check ran to completion.
- **The address of a local variable or of a field** (`&x`, `&p.Field`, `&A[i]`), and pointers to anything but a struct. Methods with a pointer receiver can therefore only be called on a pointer.
- **Linked structures** such as lists and trees. They can be built and read, but a loop that walks one forgets every node the function may modify, and there is no way to state an invariant over all nodes.
- **Interfaces** other than `error`, function values, arrays, `append(s, t...)`, `copy`, and comparing structs.
- **Letting a function accept overlapping slices.**
- **Runs of elements in `Modifies`**, such as all the structs a slice of pointers refers to.

### Struct invariants

Decisions:

- **Declared on the type.** `// @ Invariant 0 <= Count And Count <= |Items|` in the doc comment of a struct type, naming its fields directly.
- **Shorthand for contract clauses at every boundary.** The invariant is assumed on entry for every parameter and receiver of the type, proved on return for those and for every result of the type, and proved at each call for every argument. Between those points it may be broken. It is only ever assumed where a caller has proved it, so it adds no trust.
- **Always enforced, for every function, with no opt-out.** An opt-out would let the invariant be switched off function by function while the type still advertises it. A helper that must run while the invariant is broken takes the fields it needs instead of the struct, or the caller restores the invariant before calling it. Revisit only if real code cannot be restructured that way.
- **Best on a struct's own fields.** An invariant may mention what a pointer field points to, but any call that might modify that target makes the verifier forget the invariant. Ownership between structs is deferred with linked structures.
- **Likely to absorb the boilerplate about slices a struct holds.** With the memory model as built, a method that appends to `s.items` has to promise `fresh(s.items) Or within(s.items', s.items)` so that the next call may write the slice again. An invariant that says a struct owns the array of its slice would state that once.

### Trusted contracts for unproved code

Built: the trust file and its checks, the rule that a call needs a contract, contracts for functions and methods, the shipped contracts with their tests, and the trust report (`laas -vego.trust`). Not built yet: checking a trusted `modifies` against the function's source, contracts for variables such as `io.EOF`, and running the shipped-contract tests on several Go versions.

Contracts of verified functions cross package boundaries as analysis facts, together with the predicates of their package; the predicates of different packages are kept apart by a prefix.

Formulas in the file have to be quoted, because YAML gives its own meaning to `: `, `|`, `!`, `[`, and `#`.

Verified code has to call code that cannot be verified: the standard library, third-party modules, and functions of the project itself that use unsupported Go. A trusted contract states what such a function requires and ensures. Callers must still prove the `Requires`; the `Ensures` is assumed rather than proved.

Decisions:

- **One file, no in-source trust.** Contracts for unproved code live in `vego-trusted.yaml` next to `go.mod`. There is no in-source `Trusted` marker and no `Assume`, so every assumption is a diff in one conspicuous file. A function with both `//@` annotations and an entry is an error.
- **Entry format.** The key is the function's full name as Go prints it (`sort.Ints`, `(*bytes.Buffer).Len`). Fields: `reason` (mandatory free text saying why the contract is believed), `requires`, `ensures`, and `modifies` (what the function may write, in the form of a `Modifies` clause; anything unlisted is assumed untouched). Formulas use the `//@` language. Parameter names come from the real signature; there is no override.
- **Result names.** Named results keep their names. A single unnamed result is `result`; several are `result1`, `result2`, ...
- **No contract, no call.** Verified code that calls a function with neither annotations nor an entry is an error, never silent trust. When in doubt, vego takes the loudest path: agents loop on its output, so anything quiet gets exploited.
- **Checks on the file.** The function exists, every name is a parameter or result of the right type, `modifies` names memory a caller can see, and no contract contradicts itself.
- **What a trusted function is trusted with besides its contract.** It returns without panicking when its `requires` hold, writes nothing a caller can see beyond its `modifies`, keeps no pointer or slice it was given, and returns no pointer into the middle of a struct or array. The last one is what keeps the split of memory by type and field sound.
- **Shipped contracts.** Standard-library contracts are YAML files in this repository, one per package, embedded in the binary. A project entry replaces a shipped one. They state documented behaviour only, written from the documentation of the oldest supported Go version; the Go 1 compatibility promise then keeps them true on every later version, so there are no per-version variants. Each is tested against the real function on random inputs, on every supported toolchain once CI exists.
- **Not shipped.** Contracts for third-party modules, which carry no such promise.
- **Trust report.** `laas -vego.trust ./...` prints the project entries, the shipped entries in use, and unused entries.

### Errors

Built: opaque errors with nil tests, non-nil results for `errors.New`, `fmt.Errorf`, and package-level sentinels, and the always-fails check with its exception. Reading an error variable of another package, such as `io.EOF`, is not supported yet; it needs the trusted file.

Decisions:

- **Opaque errors.** An `error` is a value about which the verifier knows only whether it is `nil`. Contracts write `err = nil` and `err != nil`. Which error it is (sentinels, `errors.Is`) comes after structs and pointers; typed errors and their contents need interfaces and come much later; message text is never modelled.
- **The methods of an error are trusted.** Formatting an error with `fmt.Errorf` runs its `Error` method, which is code the verifier does not see, and an error passed in from outside could be a pointer to memory the function reasons about. The alternatives were to reject formatting errors, which would rule out the `%w` idiom, or to forget all memory at every such call. Instead it is an assumption stated in the README: the methods of an error write nothing a caller can see and do not panic. Verified code cannot create an error that breaks it, since nothing but an error converts to an error.
- **A contract must not allow a function to always fail.** For every verified function that returns an error, vego checks whether an implementation that always returns a non-nil error and zero values would satisfy the postcondition. If it provably would, that is an error, not an opt-in audit finding. The fix is to state when the function succeeds, as in `err = nil <-> 0 <= i < |A|`.
- **Exception: failure that comes from outside.** A function whose failure is not determined by its inputs, such as one that reads a file, cannot promise success. Its contract may allow always failing only if it calls a function whose contract also allows it. Trusted entries are where such failure originates, and the trust report marks them.

- **The outside world is unknown, not modelled.** A call whose outcome depends on something that is not an argument (a file, the network, the clock) returns some value satisfying its contract, fresh on every call. Proofs must hold for every such value. vego does not model the state of the world.

### Integers

Built: every integer type, overflow obligations for arithmetic, negation, division, and conversion, the named limits (`MaxInt` and friends) in annotations, arbitrary-precision arithmetic in the solver, and product reasoning. Not built yet: shifts and bitwise operators, and automatic range facts for slice elements inside quantified annotations.

Decisions:

- **Overflow is an error for every integer type, including `int`.** Go wraps silently; verified code may not. Each arithmetic operation carries a proof obligation that its result fits the type, so program values always equal their mathematical values. The same goes for conversions to a narrower type, negation of the minimum value, and `MinInt / -1`. Code that wraps on purpose (hashes, checksums) cannot be verified and belongs in the trusted file.
- **Annotations keep mathematical integers.** `|A| + 1` in a contract never overflows.
- **Existing examples will need stronger contracts**, for example bounds on the elements a loop sums. That is accepted.

Solver work this requires:

- Arbitrary-precision coefficients. Bounds like 2^63 - 1 overflow the 64-bit arithmetic the solver uses today.
- Reasoning about products, by multiplying known inequalities: if `p >= 0` and `q >= 0` are known then `p*q >= 0` holds, and expanding it gives a linear fact about the products that occur in the goal. This covers bounds from constant ranges and symbolic ones such as `i*w + j < h*w` from `i < h` and `j < w`. Only pairs whose product mentions a term already in the problem are tried. Deeper facts need an `//@ Assert` step.
- Built-in facts that discharge the common cases without annotations, such as `|A| <= MaxInt`.

### Floats

Built as decided.

Decision: floats are opaque. The verifier tracks a `float32` or `float64` through the code but knows nothing about its value: arithmetic yields an unknown float, a comparison an unknown boolean, and a conversion to an integer an unknown integer of that type. Modelling floats as real numbers is ruled out as unsound, and exact IEEE reasoning is out of reach for a native engine.

Consequences, accepted because the first target is services, CLIs, infrastructure, and data structures, where floats are incidental:

- No fact about a float value can be stated or proved.
- An integer computed from a float needs an explicit range check before it is used as an index.
- A loop controlled by a float cannot be proved to terminate, so its function goes in the trusted file.

Possible later: facts that are true of real floats, such as small integers converting exactly, added when a concrete need appears.

### Strings

Built: the basic tier and approximate ranging. A concatenation must be proved not to exceed the largest `int`, for the same reason as an `append`.

Decision: build the basic tier together with sized integers.

- **Basic tier.** A string is an immutable sequence of bytes: length, indexing, equality, literals, concatenation, substrings `s[i:j]`, and the copying conversions `[]byte(s)` and `string(b)`. Substrings are safe here, unlike sub-slices, because strings cannot be written to.
- **Unicode, approximately.** In `for i, r := range s`, `r` is some valid character and the next index is one to four bytes further. Exact UTF-8 decoding is not modelled.
- **Left until real code needs it.** Contracts about content (prefixes, the position `Index` returns) and string ordering.
- **Kept opaque.** Formatting, parsing, and pattern matching. `fmt.Sprintf` returns some string; `strconv.Atoi` returns some number when `err = nil`.

## Later

### Runtime checks for trusted contracts (gradual mode)

A trusted contract may be wrong in practice. The remedy is to check it while the program runs under `go test`: evaluate the `Requires` before the call and the `Ensures` after it, and fail loudly on a violation. The same mechanism covers the other direction, where unproved code calls a verified function and nobody has checked the `Requires`. This is the paper's gradual mode, applied where it pays off most.

Planned mechanism: `go build -toolexec`. The Go toolchain lets a program wrap each compiler invocation and rewrite source files before they are compiled, which is how compile-time OpenTelemetry instrumentation works. vego would use it to inject the checks during test builds only, so:

- the source tree is never modified and no generated files are checked in;
- checks can be added at call sites of external functions, which have no source in the project to edit;
- production builds carry no overhead.

Things to settle when this is built: which formulas are executable (bounded quantifiers are, quantifiers over all integers are not), the cost of checks inside loops, and how a violation is reported so it points at the contract and not at the injected code.

This is deliberately deferred. Nothing else on the roadmap depends on it.

### Effects: marking which functions touch the outside world

Worth investigating; nothing is decided. An effect system records, per function, whether it may interact with the outside world. Functions without the mark are guaranteed to depend only on their arguments.

How it could combine with the current design:

- Trusted entries would declare the effect, for example `effects: [io]` on `os.ReadFile`. The verifier would infer it for verified functions from what they call.
- The always-fails rule already has this shape: a contract may leave failure open only if the function calls something whose contract does. An explicit effect would state that directly instead of deriving it from contract shape, and would catch a trusted entry for a pure function that merely has a weak contract.
- Pure functions could be given stronger reasoning: the same arguments give the same result, and they could be called inside annotations.
- A contract could forbid effects, for example to prove that a function does no I/O.

A further step, deliberately not planned, is modelling the world's state as an invisible input so that contracts can say when I/O succeeds and relate one call to another.

### Other items from the paper

- Multiset reasoning, so a sort can promise that its output is a permutation of its input.
- The `Preserves`, `Immutable`, and `Cost` annotations.
- Mutation-based candidates for the specification audit.
- Counterexamples in diagnostics.
- Maps.
