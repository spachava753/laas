# Writing documentation

These rules apply to every file in `docs/` and to the user-facing sections of the README. They cover two things: how the text reads, and whether it is true.

## Who reads it

Write for a reader who knows Go well and knows nothing about this project. That reader is often an agent using the tool for the first time. They read the guide once from the top and then come back to look things up.

Before you write a section, decide what the reader is trying to do when they reach it. Tell them what to type, what they will see, and what to do next. Leave out how the tool works inside unless the reader needs it to use the tool.

## Sentences

Keep the text direct, neutral, and easy to read.

- Put one idea in a sentence. If a sentence needs a second read, split it.
- Use ordinary word order: subject, verb, object. Write "`vego` knows one thing about an error", not "About an error, `vego` knows one thing".
- Vary the length. A run of sentences with the same length and shape is tiring to read. Follow a long sentence with a short one where it fits.
- State the fact. Do not comment on it, sell it, or sum it up with a slogan.
- Use the plain word. Write "the function must list the slice", not "the function has to say whether it writes it".
- Define a term the first time you use it, and then keep using that term. Do not switch between "precondition", "the `Requires`", and "what the function asks for".
- Address the reader as "you". Use the present tense.

## Patterns to avoid

These patterns make text sound machine-written and harder to follow. Each line shows a sentence that was removed from this repository and its replacement.

A definition hung on a colon:

> ✗ `Requires` is the other half of a contract: what must hold when the function is called.
>
> ✓ A `Requires` clause states what must be true when the function is called.

A trailing "which" clause that carries a second idea:

> ✗ The smallest annotation is `//@ Ensures True`, which promises nothing and turns on the checks every verified function gets.
>
> ✓ To turn on the built-in checks without writing a contract, add `// @Ensures True`.

A list of items packed into one sentence:

> ✗ For that code `vego` proves that nothing panics, that no integer overflows, that loops and recursion end, that the function meets its contract, and that it changes nothing it did not say it would.
>
> ✓ A sentence that introduces the list, followed by a bulleted list with one item per line.

A figure of speech or a personified tool:

> ✗ `vego` found it without being asked, because it checks every arithmetic operation of a verified function.
>
> ✓ `vego` reports this because it checks every arithmetic operation in a verified function for overflow. Nothing in the contract asked for that check.

A sentence that announces structure or adds emphasis without content:

> ✗ Three things are worth knowing before you start.
>
> ✗ That is the whole method.
>
> ✗ This is not busywork.
>
> ✓ Delete the sentence. If it carried a fact, state the fact.

Also avoid:

- phrasing a point as "not X, but Y" when "Y" alone would do;
- groups of three used for rhythm;
- idioms and literary turns of phrase, such as "part ways", "get round to", "and rightly", "hold up", "take on faith";
- hedges and intensifiers, such as "simply", "just", "very", "a great deal of", "quite";
- em dashes and semicolons used to join two sentences. Write two sentences.

## Layout

- Use headings for structure. A reader who comes back to look something up scans the headings, so name each one after what the section answers.
- Use bold only for a rule the reader must not miss. One or two uses in a long document is normal. Do not start paragraphs with a bold run-in phrase. Use a subheading or a plain sentence.
- Use a bulleted list for items that are parallel, a numbered list for steps in order, and a table when each item has the same two or three attributes.
- Do not put reasoning in a list or a table. Reasoning goes in paragraphs.
- Put commands, code, file names, flags, and messages in code formatting. Quote a message exactly as the tool prints it.
- Show an example before the explanation of it, and keep it short. Show the failing version and the message it produces when the point is a check.

## Accuracy

Documentation in this repository is reviewed like code. A wrong sentence in the guide costs a reader more than a missing one.

- Run the tool before you describe what it does. Do not write what the tool should do or what you remember it doing.
- Every program in `docs/verification.md` must also be in `vego/testdata/src/guide`, with the messages it produces as `// want` expectations. When you change an example in the guide, change the corpus in the same commit, and the other way round.
- Do not recommend something you have not tried. This applies most of all to entries in the trust file. A recipe for a trusted contract is a claim about someone else's code, and two such recipes were removed from the guide because the contracts were false.
- Say "not proved" when the tool could not prove something. Do not say "false" or "wrong" unless it is.
- State limits plainly and in the place the reader will hit them. If something is unsupported, say so, show the message, and say what to do instead.
- If the tool's behaviour is the problem, fix the tool. Do not document around a fault.
- When a change to the tool changes a message, a flag, or a supported form, search the documentation for it and update every place.

## Before you finish

1. Read the changed text from the top as someone who has never seen the project. Mark every sentence you had to read twice, and rewrite it.
2. Check each changed statement against the tool.
3. Run `go test ./...`, which runs the guide corpus.
4. Check that every internal link still points at a heading that exists.
