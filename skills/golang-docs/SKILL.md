---
name: golang-docs
description: Write, review, or improve idiomatic Go doc comments for functions, methods, types, interfaces, and struct fields. Use for Go API documentation, not general prose or implementation-only changes.
---

# Go doc comments

Document the contract a caller needs to use the API correctly. Explain purpose and
observable behavior, not just the signature or a narration of implementation steps.
Stay within the requested editing scope.

## Establish the contract

Read the declaration and implementation before drafting. Follow relevant helpers
and types when their behavior affects callers. Trace how inputs are checked,
transformed, retained, copied, or ignored, and how returned values remain related
to their inputs. Use callers, tests, nearby comments, and existing package
conventions to resolve uncertainty. Do not infer a promise from a name or from
one successful example.

For each requested declaration, identify the applicable facts:

- Purpose, result meaning, and how inputs affect the operation.
- Preconditions, supported input shapes, and restrictions callers must respect.
- Defaults, zero values, and distinctions between absent and explicitly supplied values.
- Failure conditions, returned errors, and documented panic conditions.
- Mutations, side effects, ownership, resource lifetime, and cleanup responsibilities.
- Concurrency guarantees and cancellation behavior, if the API establishes them.
- Relationships to other operations, precedence rules, and compatibility constraints.

These are questions to investigate, not headings to fill mechanically. Omit
inapplicable items. If evidence is incomplete, investigate further or leave out an
unsupported claim; do not manufacture guarantees to make the comment look complete.

## Write for the reader

- Begin a declaration comment with the declared name, or a natural article followed
  by that name. Use the method name for a method. Attach the comment directly to
  its declaration without an intervening blank line.
- Lead with one clear sentence stating the operation's own purpose, effects, and
  result meaning. Follow with the conditions needed to use it correctly. First
  write a minimal complete contract; add detail only if it helps a caller make
  a decision. Avoid enumerating implementation branches or supported kinds when
  that obscures the essential contract.
- Prefer precise behavior over adjectives such as safe, efficient, or flexible.
  State what happens and under which conditions. Avoid promises broader than the
  implementation and its established contract support.
- For a type, explain what it represents and how it is used. For a function type
  or callback, document the work an implementation must perform, its inputs, its
  results, and failure expectations; describing how one consumer invokes it is
  not a substitute. For an interface, describe shared obligations without assuming
  the behavior of one concrete implementation.
- For each requested field, explain its meaning and relevant units, defaults,
  omission behavior, interactions, and constraints. A field description should be
  useful where that field is declared; do not hide its contract only in the type's
  comment. Explain the type's overall purpose separately.
- Use Go documentation links for relevant identifiers. Add a reference to an
  external contract only when the code or existing documentation establishes it;
  do not invent specification citations or look up an answer outside the task's
  permitted sources.
- Match the package's terminology and tone. Keep examples only when they clarify
  a meaningful distinction. Prefer a concise complete comment to a long list of
  implementation details.

## Review the change

Compare the draft against the evidence, fact by fact. Check for omitted conditions
as well as contradictions. Pay particular attention to zero-value behavior,
restrictions, errors, and interactions that are easy to miss in a summary.

Check the opening sentence alone: does it state the essential job rather than
merely naming a consumer or restating the signature? Check qualifications against
the relevant evidence, including ownership and validity after the call. Then
remove details that are redundant, unsupported, or distract from these facts.
Check that each requested declaration and field has an attached comment and that
unrelated code and comments stayed intact.
Use the relevant Go formatting and checks available in the project, then review
the diff for accidental changes.
