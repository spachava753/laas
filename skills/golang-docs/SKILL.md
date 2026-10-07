---
name: golang-docs
description: Write, review, or improve idiomatic Go doc comments for functions, methods, types, interfaces, and struct fields. Use for Go API documentation, not general prose or implementation-only changes.
---

# Go doc comments

Write the smallest complete caller-facing contract, not a tour of the code.
Keep edits within the requested scope.

## Find the facts before drafting

Read the declaration, relevant implementation, helpers, callers, tests, and nearby
documentation. Identify the essential purpose and result, then collect the
conditions a caller must know. Distinguish established guarantees from incidental
implementation behavior. A name, a branch, or a single example is not a contract.

Make a short working checklist of applicable facts and their evidence:

- What the operation does, what inputs mean, and what success and failure return.
- Preconditions and supported input representations.
- Defaults and the meaning of zero or omitted values.
- Whether inputs are copied, retained, mutated, or required to remain unchanged.
- How long results and resources remain valid, and who performs cleanup.
- Interactions and precedence between related options or operations.
- Established concurrency, cancellation, and repeat-call guarantees.

Trace beyond the immediate declaration when a fact depends on another operation.
Do not write speculative promises. If evidence conflicts, resolve it before
presenting an unconditional rule.

## Turn facts into comments

Start with a complete sentence naming the declaration and stating its essential
job. For methods, use the method name. A natural article before a type name is
fine. Attach the comment directly to the declaration, with no blank line between.

Follow with only the qualifications needed to use it correctly. Prefer a few
precise sentences to an exhaustive list of implementation cases. Do not let an
interesting detail crowd out a precondition, ownership rule, or default.

For a type, explain what its instances represent. For a function type or interface,
state the work implementations must perform and the meaning of inputs and outputs;
do not merely describe the behavior of one consumer. For requested struct fields,
explain each field's meaning, defaults, constraints, and interactions beside that
field. Keep the type's overview separate from those details.

Use the package's terminology and valid Go doc links. Cite an external contract
only when the available evidence establishes it. Preserve relevant qualifications
rather than inventing a stronger guarantee. Add examples only when they clarify a
material distinction.

## Check completeness and scope

Compare each draft with the working checklist. Every material fact needs a clear
statement, and every assertion needs evidence. Remove incidental explanations
that do not help a caller; check for missing restrictions as carefully as false
claims. Confirm comment attachment, format as appropriate, and review the diff
for unrelated code or comment changes.
