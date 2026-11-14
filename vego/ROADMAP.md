# vego roadmap

What is planned and not built, and the decisions behind what is built. The README describes what exists today for someone using it; this file is for someone changing it.

## Target

vego is meant for use on real projects, not only textbook algorithms. The first target is the code found in services, command-line tools, infrastructure, parsers, and data structures: logic over integers, strings used as tokens, slices, structs, and errors, calling into the standard library and third-party modules.

Not a target: numerical, scientific, graphics, and machine-learning code, where floating point is the core logic, and code whose point is formatting or parsing text exactly.

Design choices should be judged against the first group. A feature that only helps the second can wait.

## Go that stops a function from being verified

Each of these makes vego report the function that uses it as `cannot verify`. They are listed here in one place, in the order they are meant to be built, which is roughly how often ordinary code runs into them. The sections by area further down say more about some of them.

1. **Which error it is.** `errors.Is`, `errors.As`, comparing with a sentinel, and reading a sentinel of another package such as `io.EOF`. Today an error is only nil or not.
2. **A call that modifies memory inside a condition or a larger expression**: `if !s.Push(x)`, `for it.Next()`, `p.x = f(p)`. Such a call has to be a statement of its own today.
3. **Function values and closures.** This is what `defer cancel()` and `defer func() { ... }()` wait for, the two most common deferred calls that are not supported.
4. **Interfaces other than `error`**, and calls through them: `defer resp.Body.Close()`, `io.Writer`, `sort.Interface`.
5. **Calls to variadic functions**, which `log.Printf` and `fmt.Println` are, and `append(s, t...)`.
6. **Arrays**, and with them every struct that holds one.
7. **Package-level variables** other than error sentinels. Existing code is full of them, and a function that reads one cannot be verified at all today.
8. **`copy`, comparing structs with `==`, labelled `break` and `continue`, `goto`, `fallthrough`, `select`, `defer` inside a loop, a `range` over a map that changes a map of that type.**
9. **Pointers to anything but a struct**, such as `*int`.
10. **Generic functions and types.**
11. **Goroutines and channels.** A proof is about one goroutine; nothing is said about what runs beside it.

Two things do not stop a function from being verified but come up as often:

- **Conversions that drop bits and arithmetic that wraps**, as in `byte(x)` and a hash, are errors by design. `byte(x & 0xFF)` verifies. A way to say "this wraps on purpose" at one operation is not planned yet and would have to be loud.
- **Contracts for the standard library.** Only a handful of functions have shipped contracts, and none of the methods: `sync.Mutex` first.

## Before it is called ready

- **Use it on a real package.** vego has only been run on its own test programs and on programs written to break it. Nobody has annotated existing code with it, so how much friction there is in practice is not known. The first trial should rank everything in this file.
- **Speed.** Generated packages of 40 to 100 short functions with pointer parameters that may be the same have taken around ten minutes. Nothing has been profiled.
- **Newer toolchains.** The pinned `golang.org/x/tools` cannot read packages built by Go 1.27 or newer, so `laas` has to be run with `GOTOOLCHAIN=go1.26.6`, and a module that needs a newer Go cannot be analysed at all. A newer `x/tools` exists; moving to it changes the Go version the whole module needs.
- **What the first readers of the guide could not do.** Two reviewers tried to verify small realistic programs with only `docs/verification.md`. A new module went well; a service with a mutex, a map of structs, wrapped errors, an interface, and a global did not. What stopped them, beyond the list above: formulas have no character literals, no `cap`, and no way to compare a slice with `nil`; `fresh(s.items)` is written without the prime although it speaks of the state on return; a sum or count over a slice that is being written cannot be carried through a loop; an invariant of a struct type is not known of the elements of a slice.
- **Continuous integration.** The tests, including those of the shipped contracts, run by hand and on one toolchain. 32-bit targets have only been tried in a few spots.

## By area: what is built, why, and what is missing

### Structs and pointers

Built: the memory model, structs as values, pointers to structs, methods, `Modifies` clauses checked in both directions, nil checks, slices that share arrays (assignment, slicing, `append` in place or moving), `fresh` and `within`, trusted contracts for methods and for functions returning pointers and slices, and contracts with `Modifies` across packages.

Decisions:

- **Sharing is reasoned about, not forbidden.** The verifier models memory as a whole. Where two pointers may refer to the same struct it considers both cases, so a contract must hold when they are equal or require that they differ.
- **Memory is a set of allocations, and a pointer is an allocation and a position in it.** Everything that Go allocates in one piece (a struct made with `&T{...}`, the array of a slice, a variable whose address is taken) is one allocation. A pointer holds which allocation it points into and where; a slice holds the allocation, the position of its first element, its length, and its capacity. Structs lie at byte offsets, as the compiler places them, so that a struct inside another struct or inside an array has a position of its own and a pointer to it is an ordinary pointer.
- **Memory is split by struct type and field, which is sound because the split follows what Go can express.** There is one region for each field of each struct type, ignoring names and tags since conversion ignores them, and one for each element type of a slice of anything but structs. A region holds, for each allocation and position, the value of that field there. Two regions never hold the same memory: without `unsafe`, the same bytes can only be seen as fields of two struct types when one converts to the other, and those share their regions. Within a region nothing is assumed apart: two pointers, or a pointer and a slice, overlap unless the facts at hand say otherwise. An earlier design gave each pointer a whole object and assumed that objects of different types never met; a converted pointer broke that, and it was replaced rather than patched.
- **A variable whose address is taken lives in memory.** The function is scanned for `&x`, `&x.f`, and calls of pointer-receiver methods on `x`; such a variable gets an allocation where it is declared, a new one each time the declaration runs, and every use of it reads or writes that allocation. The variable of a `for` loop gets a new one for each iteration, holding the value the last one ended with, as Go does from 1.22 on; in a file compiled as older Go the iterations share it, and taking the address of a `range` variable there is not supported. Other variables stay values the verifier holds itself, which is cheaper to reason about.
- **`Modifies` is declared, and checked in both directions.** A function lists what it may write, as paths from its parameters read on entry. A write to anything else that existed on entry is an error, and so is a listed entry that no write needs, so the declaration cannot drift from the body. Callers know that everything unlisted is unchanged. Whether an entry is needed is decided by a quick proof attempt for each write; when that attempt is inconclusive the entry counts as needed.
- **A slice entry covers the capacity.** `Modifies A` allows writing every element up to the capacity of `A`, because an `append` to `A` may write there. Callers lose what they knew about that stretch, and cut the capacity with `A[:n:n]` to keep the rest. A finer entry that stops at the length, for functions that never append, is possible later.
- **Slice parameters of one element type do not overlap**, capacities included: assumed on entry, proved at every call. There is no way yet for a function to say that it tolerates overlap.
- **A field of a type that is not modelled is still part of its struct.** It is a hidden part that is copied, overwritten, and forgotten with the struct, so that assigning the whole struct counts as writing it. A struct that holds an array is the exception and is not modelled at all, since a slice of the array is a second view of the struct's memory.
- **A value without size has no identity.** Two pointers to such values may or may not be equal in Go, so nothing is assumed about where they are, and annotations may compare them only with nil.
- **`defer` is a call at every return.** The function, receiver, and arguments are settled where the statement is written; at each return the results are assigned, the calls that were put off are verified last one first like calls written there, and results that live in memory are read back. Inside a loop the number of calls is not known, so that is not supported.
- **Nil.** Every dereference carries a proof obligation that the pointer is not nil. The verifier generates and discharges it; the user writes `Requires p != nil` for parameters and nothing at the dereference.
- **`append` forks.** Whether an append writes in place or moves the slice is decided by the capacity, which is often unknown, so execution continues once for each outcome. That is why an append has to be a whole right-hand side or a returned value.
- **Loops forget memory by region.** A region the loop writes gets a new unknown value. If every write to it goes through a variable the loop does not assign, or through a slice the loop only appends to, everything else that existed before the loop is known to be unchanged. Otherwise only what existed on entry and is not listed in `Modifies` is known to be unchanged.
- **Where a pointer or slice comes from is stated with `fresh` and `within`.** A function that returns something new says `fresh(result)`; one that appends to a slice it holds says `fresh(s.items) Or within(s.items', s.items)`. Without such a clause the caller knows nothing about what the value may share.

Not built yet:

- **Checking a trusted `modifies` against source.** For a trusted function whose source is available, analyse the body and report a write the entry does not declare. This catches some wrong entries; it cannot certify one, because the analysis stops at assembly, `unsafe`, and calls through interfaces or function values. The trust report should say for each entry whether the check ran to completion.
- **A stronger search for inputs.** A function that returns an error has to have a contract that some input makes succeed, and that input is looked for by enumeration: numbers and strings the contract mentions and a few usual ones, slices up to 4096 long whose elements are all alike, pointers followed two deep, and maps with one key. When the combinations are too many to try, 3000 of them are drawn evenly. An honest contract whose only successes lie outside that (elements that differ from each other, a chain of three pointers, a map with two keys) is reported, in a message that says the search found nothing, and its author has to add a clause that a simple input satisfies. The search should be driven by the solver's own model of the precondition instead of by enumeration.
- **Checking that annotations mean something.** An index out of range or a division by zero inside an annotation is not an error today. The plan is the usual one: each formula gets a condition under which it is defined, read left to right through `And`, `Or`, and `->` and through the bounds of quantifiers, and that condition is proved where the formula is: a `Requires` from the clauses before it, an `Ensures` in the state on return, an invariant at the loop head.
- **Arrays.** Until they are built, a struct that holds an array is not modelled at all, because `s.arr[:]` is a slice into the struct and a hidden field would not show that writing the struct changes the slice. The plan: an array field of `N` elements of a single value occupies `N` positions in the region of its element type, starting at the field's byte offset, which cannot collide with a neighbour since every element takes at least a byte; an array of structs lies at byte offsets like a slice of structs. A cell then covers a run of positions, and an array value is a sequence, as a string is.
- **Pointers to anything but a struct**, such as `*int` or `*string`. A field of type `int` lives in the region of its struct and field, and an element of a `[]int` in the region of `int` elements, so an `*int` could point into either and would have to say which. The way to build it is to key the regions of single values by their type alone, at byte offsets, for all structs and slices; fields of different structs then share a region and are told apart by position, which costs the solver the separation it now gets for free. Worth doing once it is measured.
- **Linked structures** such as lists and trees. They can be built and read, but a loop that walks one forgets every node the function may modify, and there is no way to state an invariant over all nodes.
- **Letting a function accept overlapping slices.**
- **Runs of elements in `Modifies`**, such as all the structs a slice of pointers refers to.

### Maps

Built: maps with integer or string keys and values of any modelled type; reading, the two-result read, writing, `delete`, `len`, `make`, literals, nil, `range`, `Modifies`, and `m[k]`, `has(m, k)`, and `|m|` in annotations.

Decisions:

- **A map is a reference into memory of its own.** For each map type there is a region saying which keys each map has, one for each leaf of the values, and one for the number of keys. Two maps may be the same map, like two pointers.
- **A string key becomes a number.** The logic has a function that gives every sequence a number, the same for two sequences exactly when they have the same length and elements. That is all the solver knows about it.
- **An absent key has the zero value**, so `m[k]` needs no case distinction. This, that the count is not negative, that a present key makes it positive, and that the nil map is empty are stated for each map and key that is read.
- **The count is only tracked through writes.** A write adds one if the key was absent and a delete takes one off if it was present. Nothing ties the count to the set of keys beyond that, so a fact such as "two distinct present keys mean at least two keys" cannot be proved.
- **`delete` on the nil map does nothing**, as in Go. In the model the removal writes that the key is absent and has the zero value, which is already true of every key of the nil map, so no rule about the nil map is ever broken.
- **`range` over a map is a counted loop over unknown keys.** Each iteration gets some key that is present. That the keys of different iterations differ is not modelled, so a loop cannot prove that it saw every key. A loop that writes a map of the ranged type is rejected, since Go's rules for that are involved.
- **Samples of maps have one key.** The search for an input on which a contract forces success tries the nil map and maps with a single key. A value that is a struct is sampled with all its numbers equal and everything else in it zero.

Not built yet: keys of other types (booleans, pointers, structs); a way for an invariant to count the iterations of a `range` over a map, without which a loop cannot add up the values of a map and prove that the sum does not overflow; elements of a map in `Modifies` paths with string keys; and maps of maps beyond what the value model gives for free.

### Struct invariants

Built as decided below, including invariants of types of other packages, which travel as analysis facts with the constants they mention. A declaration is checked once: an invariant that cannot be read, or a set of invariants no value satisfies, is an error even if nothing uses the type.

Decisions:

- **Not assumed after trusted code.** A verified function proves the invariants of what it hands back, so its callers may assume them. A trusted function proves nothing, so after it the invariant of a result, or of a struct it may have modified, has to be proved again before it is relied on.
- **Only at boundaries, only for what is passed directly.** The invariant is applied to parameters, receivers, and results whose type is the struct or a pointer to it. A struct inside another struct, in a slice, or behind a pointer field is not covered.
- **Declared on the type.** `// @ Invariant 0 <= Count And Count <= |Items|` in the doc comment of a struct type, naming its fields directly.
- **Shorthand for contract clauses at every boundary.** The invariant is assumed on entry for every parameter and receiver of the type, proved on return for those and for every result of the type, and proved at each call for every argument. Between those points it may be broken. It is only ever assumed where a verified caller has proved it. Like a `Requires`, it is taken on trust from callers that are not verified.
- **Always enforced, for every function, with no opt-out.** An opt-out would let the invariant be switched off function by function while the type still advertises it. A helper that must run while the invariant is broken takes the fields it needs instead of the struct, or the caller restores the invariant before calling it. Revisit only if real code cannot be restructured that way.
- **Best on a struct's own fields.** An invariant may mention what a pointer field points to, but any call that might modify that target makes the verifier forget the invariant. Ownership between structs is deferred with linked structures.
- **Likely to absorb the boilerplate about slices a struct holds.** With the memory model as built, a method that appends to `s.items` has to promise `fresh(s.items) Or within(s.items', s.items)` so that the next call may write the slice again. An invariant that says a struct owns the array of its slice would state that once.

### Trusted contracts for unproved code

Built: the trust file and its checks, the rule that a call needs a contract, contracts for functions and methods, the shipped contracts with their tests, and the trust report (`laas -vego.trust`). Not built yet: shipped contracts for methods, starting with `sync.Mutex` and `sync.RWMutex`, which every `defer mu.Unlock()` needs (the test of shipped contracts only calls functions so far); checking a trusted `modifies` against the function's source, contracts for variables such as `io.EOF`, and running the shipped-contract tests on several Go versions.

Contracts of verified functions cross package boundaries as analysis facts, together with the predicates of their package; the predicates of different packages are kept apart by a prefix.

Formulas in the file have to be quoted, because YAML gives its own meaning to `: `, `|`, `!`, `[`, and `#`.

Verified code has to call code that cannot be verified: the standard library, third-party modules, and functions of the project itself that use unsupported Go. A trusted contract states what such a function requires and ensures. Callers must still prove the `Requires`; the `Ensures` is assumed rather than proved.

Decisions:

- **One file, no in-source trust.** Contracts for unproved code live in `vego-trusted.yaml` next to `go.mod`. There is no in-source `Trusted` marker and no `Assume`, so every assumption is a diff in one conspicuous file. A function with both `//@` annotations and an entry is an error.
- **Entry format.** The key is the function's full name as Go prints it (`sort.Ints`, `(*bytes.Buffer).Len`). Fields: `reason` (mandatory free text saying why the contract is believed), `requires`, `ensures`, and `modifies` (what the function may write, in the form of a `Modifies` clause; anything unlisted is assumed untouched). Formulas use the `//@` language. Parameter names come from the real signature; there is no override.
- **Result names.** Named results keep their names. A single unnamed result is `result`; several are `result1`, `result2`, ...
- **No contract, no call.** Verified code that calls a function with neither annotations nor an entry is an error, never silent trust. When in doubt, vego takes the loudest path: agents loop on its output, so anything quiet gets exploited.
- **Checks on the file.** The function exists, every name is a parameter or result of the right type, `modifies` is present, even if empty, and names memory a caller can see, a primed path in an `ensures` reads memory of a kind that `modifies` lists, and no contract contradicts itself.
- **Checks at each call.** After the promises of a trusted contract are assumed, a quick attempt is made to prove a contradiction; if it succeeds on a path that was not contradictory before, the call is reported. The attempt is bounded, so a contradiction that is hard to find gets through.
- **Recursion through a trusted function of the same package is found.** Its body is there to read: a function it names, or that a call it cannot resolve may reach because the package names it somewhere other than to call it, counts as called. A call back by way of another package is not seen and is part of what is trusted.
- **What a trusted function is trusted with besides its contract.** It returns without panicking when its `requires` hold, which includes not calling back into its verified caller by way of another package, writes nothing a caller can see beyond its `modifies`, and keeps no pointer or slice it was given. Nothing is assumed about where a pointer it returns points.
- **Shipped contracts.** Standard-library contracts are YAML files in this repository, one per package, embedded in the binary. A project entry replaces a shipped one. They state documented behaviour only, written from the documentation of the oldest supported Go version; the Go 1 compatibility promise then keeps them true on every later version, so there are no per-version variants. Each is tested against the real function on random inputs, on every supported toolchain once CI exists.
- **Not shipped.** Contracts for third-party modules, which carry no such promise.
- **Trust report.** `laas -vego.trust ./...` prints the project entries, the shipped entries in use, and unused entries.

### Errors

Built: opaque errors with nil tests, non-nil results for `errors.New`, `fmt.Errorf`, and package-level sentinels, and the always-fails check with its exception. Reading an error variable of another package, such as `io.EOF`, is not supported yet; it needs the trusted file. An error inside a struct result is not looked at by the always-fails check.

Decisions:

- **Opaque errors.** An `error` is a value about which the verifier knows only whether it is `nil`. Contracts write `err = nil` and `err != nil`. Which error it is (sentinels, `errors.Is`) is the first item of the list above; typed errors and their contents need interfaces and come later; message text is never modelled.
- **Only an error of known origin can be formatted.** `fmt.Errorf` runs the `Error` method of an error it formats and, with verbs such as `%#v`, methods of the values the error contains. An error passed in from outside could use them to write memory the function reasons about. An error may therefore be formatted only if it was made by `errors.New` or `fmt.Errorf`, here or in a verified function that returns nothing else, or is a package-level variable holding such an error. That is decided from the text of each function, without regard to the path taken: a variable qualifies when every assignment to it does. Errors from parameters and from trusted functions can be returned and compared with `nil` but not formatted. Not built: letting a trusted contract vouch for the errors of its function, which wrapping the error of a standard-library call needs.
- **A contract must not allow a function to always fail.** For every verified function that returns an error, vego checks whether an implementation that always returns a non-nil error and zero values would satisfy the postcondition. If it provably would, that is an error, not an opt-in audit finding. The fix is to state when the function succeeds, as in `err = nil <-> 0 <= i < |A|`.
- **Exception: success that hangs on the outside.** A function cannot promise success when a call nothing predicts decides it: a trusted function whose contract leaves open what comes back, or a verified function that is itself excused. The call must decide between failure and success: some return of an error and some return without one must each depend on what the call produced, and each must be reachable by some input. Reaching the call is not enough, and a function that fails whatever the call does is not excused.
- **Depending on a call is decided by proof.** Whether a returned error is nil, or the condition of a branch that was a real choice, depends on a call when it cannot be proved to stay as it is once everything the call produced is replaced by other values the call could have produced. What a call produced spreads to what a later call returns that was handed any of it, and to the unknowns that loops put in place of variables. It is not followed through memory that a later call reads or that a loop writes; a function that depends on the call only in that way is reported and has to be restructured.
- **A sentinel is trusted only when nothing can run before it is set.** `var ErrX = errors.New("x")` is non-nil for a verified function unless code of the package can run during the initialisation of its variables in a way Go's ordering does not see. Code of a package reaches another package only by being handed over, so every hand-over in code that runs during initialisation costs the package its sentinels: an argument, receiver, or type argument of another package's function, an assignment to another package's variable or to anything but a plain variable, a send, a built-in that passes its argument on, and a call or range that cannot be resolved. A value whose type has no room for code is not a hand-over.

- **The outside world is unknown, not modelled.** A call whose outcome depends on something that is not an argument (a file, the network, the clock) returns some value satisfying its contract, fresh on every call. Proofs must hold for every such value. vego does not model the state of the world.

### Integers

Built: every integer type, overflow obligations for arithmetic, negation, division, and conversion, the named limits (`MaxInt` and friends) in annotations, arbitrary-precision arithmetic in the solver, and product reasoning. Shifts and bitwise operators are expressed by arithmetic (`vego/bits.go`): a shift is a multiplication or division by a power of two, `x & y` is an unknown with the facts that hold of any two integers in two's complement plus exact ones for constant masks, and the other operators follow from it by identities such as `x | y = x + y - (x & y)`. This needed no new solver rule. Not built yet: bit operators in annotations, so that a function can say which bit it set; more about `x & y` than its bounds when neither operand is a constant mask (the XOR swap and `x&(x-1) == 0` are not proved); and automatic range facts for slice elements inside quantified annotations.

Decisions:

- **Overflow is an error for every integer type, including `int`.** Go wraps silently; verified code may not. Each arithmetic operation carries a proof obligation that its result fits the type, so program values always equal their mathematical values. The same goes for conversions to a narrower type, negation of the minimum value, and `MinInt / -1`. Code that wraps on purpose (hashes, checksums) cannot be verified and belongs in the trusted file.
- **Annotations keep mathematical integers.** `|A| + 1` in a contract never overflows.
- **A shift to the left must not lose bits**, for the same reason, and a shift count that may be negative is an error since Go panics on one.
- **No new solver rule for bits.** Everything about `&`, `|`, `^` and shifts is told to the solver as facts about unknown numbers, each of which is true of all integers in two's complement and tested against Go's operators in `bits_test.go`.

How the solver supports this: coefficients of arbitrary precision, since bounds like 2^63 - 1 do not fit 64 bits; products bounded by multiplying known inequalities, which covers `i*w + j < h*w` from `i < h` and `j < w` and leaves deeper facts to an `//@ Assert`; and built-in facts such as `|A| <= MaxInt`.

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

Decisions:

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
